#!/usr/bin/env python3
"""Cross-check the Lean side's index semantics against the source's own verifier.

Standard library only.  This script exists to answer one narrow question that
neither the exporter's SHA-256 pins nor Lean's kernel checks answer: does the
Lean encoding read the pinned record literals with the *source repository's*
index convention, or merely with some convention under which the hypotheses
happen to hold?  The kernel checks establish the mathematical properties of the
functions Lean receives; the exporter pins establish which bytes were consumed.
Neither pins the reading.  Composing the order-52 enumeration with
`(a,b,c) -> (a,b,-c)`, or swapping the two coordinates at order 20, leaves the
profile check green while naming a different matrix.

The check here is independent of `scripts/export_data.py`: the index maps,
the Goethals--Seidel block table and the `fromBlocks` layout below are
transcribed from `Challenge.lean` -- the compared statement surface -- not from
the exporter.  It proceeds in three steps.

1. Authenticate the two Hadamard-B records byte-for-byte against the same
   SHA-256 pins the exporter uses, and decode their sign tables.
2. Require the literal tables inlined in `Challenge.lean` and emitted into
   `HadamardBFormal/Data/Generated.lean` to equal those record tables entry for
   entry, so that the compared surface holds the record's bytes.
3. Assemble each bordered array under the Lean semantics, hand it to the source
   repository's `verify/verify.py` -- the lab's sole trust chain -- and require
   the canonical digest it reports to equal the record's own `pinned_sha256`.

A wrong index order fails step 3: the assembled matrix is a different matrix
and its canonical digest is a different digest.

Usage:

    python -B scripts/crosscheck_assembly.py --source-root <Hadamard-B checkout>

Exit code 0 iff every step passes; 1 on any mismatch.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]

# The same pins the exporter enforces.  Repeated here rather than imported so
# that this script is a second reading of the sources, not a second call into
# the first reading.
SOURCE_PINS = {
    "data/h52-gate.json":
        "ef60c4ff9f245eec5ba7f035e5968152836207fcd9235a0b1851150d2fb1d170",
    "data/h20-boundary.json":
        "716610543b79ab9e1c9f1adb142c114544e70e58d370500130b83c17a18cf254",
}

BOUNDARY_LABEL = "T1-diagK-w2s"


class CrosscheckError(ValueError):
    """A source is missing or changed, or a reading does not agree."""


# --------------------------------------------------------------- source data


def load_pinned_json(source_root: Path, relative_path: str) -> object:
    path = source_root / Path(relative_path)
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise CrosscheckError(f"cannot read {path}: {error}") from error
    digest = hashlib.sha256(raw).hexdigest()
    expected = SOURCE_PINS[relative_path]
    if digest != expected:
        raise CrosscheckError(
            f"SHA-256 mismatch for {path}: expected {expected}, got {digest}"
        )
    return json.loads(raw.decode("ascii"))


def signs(text: object, label: str, width: int) -> list[int]:
    if not isinstance(text, str) or len(text) != width:
        raise CrosscheckError(f"{label} must be a {width}-character sign string")
    if set(text) - {"+", "-"}:
        raise CrosscheckError(f"{label} contains characters other than + and -")
    return [1 if character == "+" else -1 for character in text]


def sign_rows(value: object, label: str, rows: int, width: int) -> list[list[int]]:
    if not isinstance(value, list) or len(value) != rows:
        raise CrosscheckError(f"{label} must have {rows} rows")
    return [signs(row, f"{label}[{i}]", width) for i, row in enumerate(value)]


# ------------------------------------------------- literals as Lean holds them

# The outer literal closes on a line indented by exactly two spaces; the inner
# ones are indented further, whether or not the emitter wrapped their values.
_DEF = re.compile(
    r"def\s+(?P<name>\w+)\s*:\s*Vector \(Vector Int \d+\) \d+\s*:=\s*"
    r"(?P<body>#v\[.*?\n  \])",
    re.DOTALL,
)
_INNER = re.compile(r"#v\[([^\[\]]*)\]", re.DOTALL)


def lean_tables(path: Path) -> dict[str, list[list[int]]]:
    """Every `Vector (Vector Int w) r` literal in a Lean file, by name."""
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        raise CrosscheckError(f"cannot read {path}: {error}") from error
    tables: dict[str, list[list[int]]] = {}
    for match in _DEF.finditer(text):
        rows = []
        for inner in _INNER.finditer(match.group("body")):
            rows.append([int(token) for token in inner.group(1).split(",")])
        tables[match.group("name")] = rows
    return tables


# ------------------------------------------------------- the Lean semantics
#
# Transcribed from `Challenge.lean`.  Group elements are tuples of residues;
# `Fin 4 x G` enumerates the `Fin 4` component outermost and `G` in its own
# product order, which is the row-major mixed-radix order `gidx` computes.


class Group:
    """A finite abelian group `Z_{n_0} x ... x Z_{n_k}` in Lean's order."""

    def __init__(self, factors: list[int]) -> None:
        self.factors = list(factors)
        self.order = 1
        for factor in self.factors:
            self.order *= factor
        self.elements = [self.of_index(k) for k in range(self.order)]

    def of_index(self, k: int) -> tuple[int, ...]:
        """Invert the mixed-radix flat index; the last coordinate runs fastest."""
        coordinates = []
        for factor in reversed(self.factors):
            coordinates.append(k % factor)
            k //= factor
        return tuple(reversed(coordinates))

    def index(self, g: tuple[int, ...]) -> int:
        """`gidx`: `(a,b,c) -> 6a + 3b + c` at `(2,2,3)`, `(a,b) -> 2a + b` at `(2,2)`."""
        k = 0
        for coordinate, factor in zip(g, self.factors):
            k = k * factor + coordinate % factor
        return k

    def sub(self, g: tuple[int, ...], h: tuple[int, ...]) -> tuple[int, ...]:
        return tuple((a - b) % n for a, b, n in zip(g, h, self.factors))

    def add(self, g: tuple[int, ...], h: tuple[int, ...]) -> tuple[int, ...]:
        return tuple((a + b) % n for a, b, n in zip(g, h, self.factors))


def pair_index(J: int, b: int) -> int:
    """`pairIdx (J, b) = 2J + b`: the class index runs fastest."""
    return 2 * J + b


def assemble(
    group: Group,
    kappa,
    rho: tuple[int, ...],
    corner: list[list[int]],
    row_table: list[list[int]],
    col_of,
    seeds: list[list[int]],
) -> list[list[int]]:
    """`border kappa E P Q x rho` at `s = 1`, as an explicit sign matrix.

    `Matrix.fromBlocks E (rowStrip kappa P) (colStrip kappa Q) (core x rho)`
    over `Fin 4 (+) (Fin 4 x G)`: the four border rows first, then the four
    superblocks, each enumerating `G` in `gidx` order.
    """
    elements = group.elements
    n = group.order

    def x(q: int, g: tuple[int, ...]) -> int:
        return seeds[q][group.index(g)]

    # `dev (x q) [g][h] = x q (h - g)`; `revCols r A [g][h] = A [g][rho - h]`;
    # `(dev (x q)).transpose [g][h] = x q (g - h)`.
    def dev(q: int, g: tuple[int, ...], h: tuple[int, ...]) -> int:
        return x(q, group.sub(h, g))

    def rev(q: int, g: tuple[int, ...], h: tuple[int, ...]) -> int:
        return dev(q, g, group.sub(rho, h))

    def rev_t(q: int, g: tuple[int, ...], h: tuple[int, ...]) -> int:
        # `dev(x q)ᵀ [g][rho - h] = x q (g - (rho - h))`.
        return x(q, group.sub(g, group.sub(rho, h)))

    def block(i: int, j: int, g: tuple[int, ...], h: tuple[int, ...]) -> int:
        """`gsBlock (reflect rho) (fun q => dev (x q)) i j g h`, standard orientation."""
        if i == 0:
            return [dev(0, g, h), rev(1, g, h), rev(2, g, h), rev(3, g, h)][j]
        if i == 1:
            return [-rev(1, g, h), dev(0, g, h), rev_t(3, g, h), -rev_t(2, g, h)][j]
        if i == 2:
            return [-rev(2, g, h), -rev_t(3, g, h), dev(0, g, h), rev_t(1, g, h)][j]
        return [-rev(3, g, h), rev_t(2, g, h), -rev_t(1, g, h), dev(0, g, h)][j]

    rows: list[list[int]] = []
    for r in range(4):
        row = list(corner[r])
        for J in range(4):
            for h in elements:
                row.append(row_table[r][pair_index(J, kappa(h))])
        rows.append(row)
    for I in range(4):
        for g in elements:
            row = [col_of(I, kappa(g), c) for c in range(4)]
            for j in range(4):
                for h in elements:
                    row.append(block(I, j, g, h))
            rows.append(row)

    size = 4 * (n + 1)
    if len(rows) != size or any(len(row) != size for row in rows):
        raise CrosscheckError(f"assembled a non-square {len(rows)}-row array")
    return rows


# ------------------------------------------------------------ the trust chain


def canonical_digest(verify_script: Path, rows: list[list[int]], tag: str) -> str:
    """Run the source repository's verifier and return its canonical digest."""
    text = "\n".join(
        "".join("+" if value == 1 else "-" for value in row) for row in rows
    ) + "\n"
    with tempfile.TemporaryDirectory(prefix="crosscheck-") as scratch:
        path = Path(scratch) / f"{tag}.txt"
        path.write_text(text, encoding="ascii", newline="\n")
        completed = subprocess.run(
            [sys.executable, "-B", str(verify_script), str(path)],
            capture_output=True,
            text=True,
        )
    line = ((completed.stdout or completed.stderr).strip().splitlines()
            or ["(no output)"])[-1]
    if completed.returncode != 0 or "canonical_sha256=" not in line:
        raise CrosscheckError(f"{tag}: verify.py rc={completed.returncode}: {line}")
    print(f"  {tag}: {line}")
    return line.rsplit("canonical_sha256=", 1)[1].strip()


# ------------------------------------------------------------------ the check


def require(condition: bool, message: str, failures: list[str]) -> None:
    if not condition:
        failures.append(message)


def run(source_root: Path, verify_script: Path) -> int:
    failures: list[str] = []

    gate = json.loads(json.dumps(
        load_pinned_json(source_root, "data/h52-gate.json")))["record"]
    boundary_document = load_pinned_json(source_root, "data/h20-boundary.json")
    matches = [entry for entry in boundary_document["instances"]
               if entry.get("label") == BOUNDARY_LABEL]
    if len(matches) != 1:
        raise CrosscheckError(
            f"expected exactly one instance labelled {BOUNDARY_LABEL!r}")
    boundary = matches[0]

    record_tables = {
        "seed52Data": sign_rows(gate["seeds"], "gate.seeds", 4, 12),
        "corner52Data": sign_rows(gate["corner"], "gate.corner", 4, 4),
        "rowTable52Data": sign_rows(gate["row_table"], "gate.row_table", 4, 8),
        "colTable52Data": sign_rows(gate["col_table"], "gate.col_table", 4, 8),
        "seed20Data": sign_rows(boundary["seeds"], "boundary.seeds", 4, 4),
        "corner20Data": sign_rows(boundary["corner"], "boundary.corner", 4, 4),
        "rowTable20Data": sign_rows(boundary["row_table"], "boundary.row_table", 4, 8),
        "colRows20Data": sign_rows(boundary["col_rows"], "boundary.col_rows", 8, 4),
    }

    print("literal agreement, records against the Lean sources:")
    for lean_file in (REPOSITORY_ROOT / "Challenge.lean",
                      REPOSITORY_ROOT / "HadamardBFormal" / "Data" / "Generated.lean"):
        found = lean_tables(lean_file)
        for name, table in record_tables.items():
            require(name in found, f"{lean_file.name}: {name} not found", failures)
            if name in found:
                require(found[name] == table,
                        f"{lean_file.name}: {name} differs from the pinned record",
                        failures)
        print(f"  {lean_file.name}: {len(record_tables)} tables checked")

    print("assembly, under the index semantics of Challenge.lean:")
    G52 = Group([2, 2, 3])
    gate_rows = assemble(
        G52,
        kappa=lambda g: g[0] % 2,                       # kappa52: first coordinate
        rho=(0, 0, 0),                                  # rho52
        corner=record_tables["corner52Data"],
        row_table=record_tables["rowTable52Data"],
        # Q52 [(I,b)][c] = colTable52Data[c][2I + b]: the record stores it transposed.
        col_of=lambda I, b, c: record_tables["colTable52Data"][c][pair_index(I, b)],
        seeds=record_tables["seed52Data"],
    )
    G20 = Group([2, 2])
    boundary_rows = assemble(
        G20,
        kappa=lambda g: (g[0] + g[1]) % 2,              # kappa20: the diagonal subgroup
        rho=(1, 1),                                     # rho20
        corner=record_tables["corner20Data"],
        row_table=record_tables["rowTable20Data"],
        # Q20 [(I,b)][c] = colRows20Data[2I + b][c]: this record stores Q row by row.
        col_of=lambda I, b, c: record_tables["colRows20Data"][pair_index(I, b)][c],
        seeds=record_tables["seed20Data"],
    )

    for tag, rows, record in (("H52-gate", gate_rows, gate),
                              ("H20-boundary", boundary_rows, boundary)):
        digest = canonical_digest(verify_script, rows, tag)
        pinned = record.get("pinned_sha256")
        require(digest == pinned,
                f"{tag}: canonical digest {digest} does not match the record's "
                f"pinned_sha256 {pinned}", failures)

    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        print(f"CROSSCHECK: FAIL ({len(failures)} problems)")
        return 1
    print("CROSSCHECK: PASS -- both instances assemble, under the Lean index "
          "semantics, to the matrices the source records pin.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--source-root",
        type=Path,
        required=True,
        help="path to the Hadamard-B repository root (the directory containing data/)",
    )
    parser.add_argument(
        "--verify",
        type=Path,
        default=None,
        help="the source repository's verify/verify.py (default: <source-root>/verify/verify.py)",
    )
    args = parser.parse_args()
    verify_script = args.verify or (args.source_root / "verify" / "verify.py")
    if not verify_script.is_file():
        print(f"crosscheck_assembly.py: error: no verifier at {verify_script}")
        return 1
    try:
        return run(args.source_root, verify_script)
    except CrosscheckError as error:
        print(f"crosscheck_assembly.py: error: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
