#!/usr/bin/env python3
"""Export the pinned bordered Goethals--Seidel witness as Lean definitions.

The exporter intentionally uses only the Python standard library.  It verifies
the source file byte-for-byte against the SHA-256 pin below before parsing it,
so a changed or substituted source cannot silently alter the Lean data.

Index conventions, matched to `Hadamard-B/tools/bordered_gs.py`:

* `AbelianGroup.idx` is row-major mixed radix, so for `G = Z2 x Z2 x Z3` the flat
  seed index of `(a, b, c)` is `6a + 3b + c`.  The Lean side computes the same
  index in `HadamardBFormalCore.Data.gidx52`.
* `coset_divisors = [2, 1, 1]` makes `kappa` the first coordinate, i.e. the
  index-two character of `G`.
* the border tables are `4s x 4i` with the class index running fastest, so the
  flat column index of the pair `(J, b)` is `2J + b`
  (`HadamardBFormalCore.Data.pairIdx`), and `col_table` is stored transposed:
  `Q[(I,b)][r] = col_table[r][2I + b]`.

The index convention is not proved correct inside Lean, and a wrong one would
not necessarily turn the build red: `(a, b, c) -> (a, b, -c)` at order 52 and
the coordinate swap at order 20 both preserve `kappa` and leave the two-tier
PAF profile check in `HadamardBFormal/Data.lean` green while naming a different
matrix.  This exporter establishes which bytes were consumed and that they were
decoded deterministically; literal source-index fidelity is the business of
`scripts/crosscheck_assembly.py`, which re-implements the reading from
`Challenge.lean` -- independently of this file -- and matches the assembled
matrices against the source repository's own canonical digests.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import NoReturn


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = REPOSITORY_ROOT / "HadamardBFormal" / "Data" / "Generated.lean"

SOURCE_PINS = {
    "data/h52-gate.json":
        "ef60c4ff9f245eec5ba7f035e5968152836207fcd9235a0b1851150d2fb1d170",
    "data/h20-boundary.json":
        "716610543b79ab9e1c9f1adb142c114544e70e58d370500130b83c17a18cf254",
}

# The gate record's own fields, as they must appear for the Lean encoding below
# to be the record.  Anything else is a different instance and must be refused.
GATE_GROUP = [2, 2, 3]
GATE_ORDER = 52
GATE_S = 1
GATE_COSET_DIVISORS = [2, 1, 1]
GATE_R_SHIFT = [0, 0, 0]
GATE_VARIANT = "standard"

# The order-20 boundary record.  Only the `standard`-orientation instance T1 is
# exported: T2 declares `orientation: "transpose-negated"`, which the standard
# orientation of this library does not cover, so it is out of scope by
# construction and must never be emitted.
BOUNDARY_LABEL = "T1-diagK-w2s"
BOUNDARY_GROUP = [2, 2]
BOUNDARY_ORDER = 20
BOUNDARY_S = 1
BOUNDARY_I = 2
BOUNDARY_W = 2
BOUNDARY_K_GENERATORS = [[1, 1]]
BOUNDARY_R_SHIFT = [1, 1]
BOUNDARY_ORIENTATION = "standard"


class ExportError(ValueError):
    """A pinned source is missing, changed, or has an unexpected schema."""


def fail(message: str) -> NoReturn:
    raise ExportError(message)


def load_pinned_json(source_root: Path, relative_path: str) -> object:
    path = source_root / Path(relative_path)
    try:
        raw = path.read_bytes()
    except OSError as error:
        fail(f"cannot read {path}: {error}")

    actual_hash = hashlib.sha256(raw).hexdigest()
    expected_hash = SOURCE_PINS[relative_path]
    if actual_hash != expected_hash:
        fail(
            f"SHA-256 mismatch for {path}: expected {expected_hash}, "
            f"got {actual_hash}"
        )

    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as error:
        fail(f"{path} is not ASCII JSON: {error}")
    try:
        return json.loads(text)
    except json.JSONDecodeError as error:
        fail(f"invalid JSON in {path}: {error}")


def expect_mapping(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        fail(f"{label} must be a JSON object with string keys")
    return value


def expect_int(value: object, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{label} must be an integer")
    return value


def expect_list(value: object, label: str) -> list[object]:
    if not isinstance(value, list):
        fail(f"{label} must be a JSON array")
    return value


def expect_int_list(value: object, label: str) -> list[int]:
    return [
        expect_int(item, f"{label}[{index}]")
        for index, item in enumerate(expect_list(value, label))
    ]


def signs(text: object, label: str, width: int) -> list[int]:
    if not isinstance(text, str):
        fail(f"{label} must be a string")
    if len(text) != width:
        fail(f"{label} must have length {width}, got {len(text)}")
    unexpected = sorted(set(text) - {"+", "-"})
    if unexpected:
        fail(f"{label} contains unexpected characters {unexpected}")
    return [1 if character == "+" else -1 for character in text]


def sign_rows(value: object, label: str, rows: int, width: int) -> list[list[int]]:
    raw = expect_list(value, label)
    if len(raw) != rows:
        fail(f"{label} must have {rows} rows, got {len(raw)}")
    return [signs(row, f"{label}[{index}]", width) for index, row in enumerate(raw)]


def decode_gate(document: object, label: str) -> dict[str, object]:
    outer = expect_mapping(document, label)
    record = expect_mapping(outer.get("record"), f"{label}.record")

    order = expect_int(record.get("order"), f"{label}.record.order")
    if order != GATE_ORDER:
        fail(f"{label}.record.order must be {GATE_ORDER}, got {order}")

    variant = record.get("gs_variant", GATE_VARIANT)
    if variant != GATE_VARIANT:
        fail(
            f"{label}.record.gs_variant must be {GATE_VARIANT!r} "
            f"(this library formalizes the standard orientation only), got {variant!r}"
        )

    group = expect_int_list(record.get("group"), f"{label}.record.group")
    if group != GATE_GROUP:
        fail(f"{label}.record.group must be {GATE_GROUP}, got {group}")

    s = expect_int(record.get("s"), f"{label}.record.s")
    if s != GATE_S:
        fail(f"{label}.record.s must be {GATE_S}, got {s}")

    divisors = expect_int_list(
        record.get("coset_divisors"), f"{label}.record.coset_divisors"
    )
    if divisors != GATE_COSET_DIVISORS:
        fail(
            f"{label}.record.coset_divisors must be {GATE_COSET_DIVISORS} "
            f"(the index-two character is the first coordinate), got {divisors}"
        )

    shift = expect_int_list(record.get("r_shift"), f"{label}.record.r_shift")
    if shift != GATE_R_SHIFT:
        fail(f"{label}.record.r_shift must be {GATE_R_SHIFT}, got {shift}")

    n = group[0] * group[1] * group[2]
    if order != 4 * (n + s):
        fail(f"{label}.record: order {order} is not 4(|G| + s) = {4 * (n + s)}")

    seeds = sign_rows(record.get("seeds"), f"{label}.record.seeds", 4, n)
    corner = sign_rows(record.get("corner"), f"{label}.record.corner", 4 * s, 4 * s)
    row_table = sign_rows(
        record.get("row_table"), f"{label}.record.row_table", 4 * s, 8 * s
    )
    col_table = sign_rows(
        record.get("col_table"), f"{label}.record.col_table", 4 * s, 8 * s
    )

    inner_pin = record.get("pinned_sha256")
    if not isinstance(inner_pin, str) or len(inner_pin) != 64:
        fail(f"{label}.record.pinned_sha256 must be a 64-character digest")

    return {
        "n": n,
        "seeds": seeds,
        "corner": corner,
        "row_table": row_table,
        "col_table": col_table,
        "record_pin": inner_pin,
    }


def decode_boundary(document: object, label: str) -> dict[str, object]:
    outer = expect_mapping(document, label)
    instances = expect_list(outer.get("instances"), f"{label}.instances")

    matches = [
        expect_mapping(entry, f"{label}.instances[{index}]")
        for index, entry in enumerate(instances)
        if isinstance(entry, dict) and entry.get("label") == BOUNDARY_LABEL
    ]
    if len(matches) != 1:
        fail(
            f"{label}.instances must contain exactly one entry labelled "
            f"{BOUNDARY_LABEL!r}, found {len(matches)}"
        )
    record = matches[0]
    tag = f"{label}.instances[{BOUNDARY_LABEL!r}]"

    orientation = record.get("orientation")
    if orientation != BOUNDARY_ORIENTATION:
        fail(
            f"{tag}.orientation must be {BOUNDARY_ORIENTATION!r} "
            f"(the transpose-negated instance T2 is out of scope by construction), "
            f"got {orientation!r}"
        )

    for key, want in (
        ("order", BOUNDARY_ORDER),
        ("s", BOUNDARY_S),
        ("i", BOUNDARY_I),
        ("w", BOUNDARY_W),
    ):
        got = expect_int(record.get(key), f"{tag}.{key}")
        if got != want:
            fail(f"{tag}.{key} must be {want}, got {got}")

    group = expect_int_list(record.get("group"), f"{tag}.group")
    if group != BOUNDARY_GROUP:
        fail(f"{tag}.group must be {BOUNDARY_GROUP}, got {group}")

    generators = expect_list(record.get("K_generators"), f"{tag}.K_generators")
    decoded_generators = [
        expect_int_list(row, f"{tag}.K_generators[{index}]")
        for index, row in enumerate(generators)
    ]
    if decoded_generators != BOUNDARY_K_GENERATORS:
        fail(
            f"{tag}.K_generators must be {BOUNDARY_K_GENERATORS} "
            f"(the Lean encoding hard-codes κ(a,b) = a + b, the diagonal subgroup), "
            f"got {decoded_generators}"
        )

    shift = expect_int_list(record.get("r_shift"), f"{tag}.r_shift")
    if shift != BOUNDARY_R_SHIFT:
        fail(f"{tag}.r_shift must be {BOUNDARY_R_SHIFT}, got {shift}")

    n = group[0] * group[1]
    if BOUNDARY_ORDER != 4 * (n + BOUNDARY_S):
        fail(f"{tag}: order {BOUNDARY_ORDER} is not 4(|G| + s)")

    seeds = sign_rows(record.get("seeds"), f"{tag}.seeds", 4, n)
    corner = sign_rows(record.get("corner"), f"{tag}.corner", 4, 4)
    row_table = sign_rows(record.get("row_table"), f"{tag}.row_table", 4, 8)
    # `col_rows` is `Q` written out row by row: `Q[2I + c][r]`, NOT the
    # transposed `col_table` of the coordinate-kernel record format.
    col_rows = sign_rows(record.get("col_rows"), f"{tag}.col_rows", 8, 4)

    inner_pin = record.get("pinned_sha256")
    if not isinstance(inner_pin, str) or len(inner_pin) != 64:
        fail(f"{tag}.pinned_sha256 must be a 64-character digest")

    return {
        "n": n,
        "seeds": seeds,
        "corner": corner,
        "row_table": row_table,
        "col_rows": col_rows,
        "record_pin": inner_pin,
    }


def format_vector(values: list[int], indent: str, values_per_line: int = 16) -> list[str]:
    chunks = [
        values[index : index + values_per_line]
        for index in range(0, len(values), values_per_line)
    ]
    lines = [f"{indent}#v["]
    for index, chunk in enumerate(chunks):
        suffix = "," if index + 1 < len(chunks) else ""
        lines.append(f"{indent}  {', '.join(str(value) for value in chunk)}{suffix}")
    lines.append(f"{indent}]")
    return lines


def format_table(name: str, rows: list[list[int]], width: int) -> list[str]:
    if any(len(row) != width for row in rows):
        fail(f"internal shape error while formatting {name}")
    lines = [
        f"private def {name} : Vector (Vector Int {width}) {len(rows)} :=",
        "  #v[",
    ]
    for row_index, row in enumerate(rows):
        vector_lines = format_vector(row, "    ")
        if row_index + 1 < len(rows):
            vector_lines[-1] += ","
        lines.extend(vector_lines)
    lines.extend(["  ]", ""])
    return lines


def render(source_root: Path) -> str:
    gate = decode_gate(
        load_pinned_json(source_root, "data/h52-gate.json"), "data/h52-gate.json"
    )
    boundary = decode_boundary(
        load_pinned_json(source_root, "data/h20-boundary.json"), "data/h20-boundary.json"
    )
    n = gate["n"]

    lines = [
        "/-",
        "This file is generated by scripts/export_data.py. Do not edit it by hand.",
        "The absolute --source-root is intentionally omitted so identical pinned inputs",
        "produce identical output on every machine.",
        "",
        "Pinned sources:",
    ]
    for relative_path, digest in SOURCE_PINS.items():
        lines.extend([f"* Hadamard-B/{relative_path}", f"  SHA-256: {digest}"])
    lines.extend(
        [
            "",
            "The records additionally carry their own provenance digests, which are the",
            "lab's pins on the parameter blocks rather than on this file:",
            "* h52-gate.json, record.pinned_sha256",
            f"  {gate['record_pin']}",
            "* h20-boundary.json, instance T1, pinned_sha256",
            f"  {boundary['record_pin']}",
            "-/",
            "",
            "import Mathlib.Data.ZMod.Basic",
            "import HadamardBFormal.Defs",
            "",
            "/-!",
            "# Two bordered Goethals--Seidel instances, as Lean data",
            "",
            "* the Theorem-D gate of `NOTE-B` §2.2 (cert 03): a from-scratch",
            "  `s = 1, i = 2` instance on the non-cyclic group",
            "  `G = ZMod 2 x ZMod 2 x ZMod 3`, in the `ε = +1` branch (`κ ρ = 0`);",
            "* the `w = 2s` hypothesis-boundary instance T1 of `NOTE-B` §2.2 (cert 05),",
            "  on `G = ZMod 2 x ZMod 2` with `K` the **diagonal** subgroup — an",
            "  arbitrary index-two subgroup rather than a coordinate kernel, which the",
            "  surjective-hom model handles as `κ(a,b) = a + b`.",
            "",
            "The companion instance T2 of the order-20 record is **out of scope by",
            "construction**: it declares the transpose-negated orientation, and this",
            "library formalizes the standard orientation only.  The exporter refuses to",
            "emit it.",
            "",
            "Only the literals and the index maps live here.  Every mathematical",
            "property of this data is checked by kernel reduction in",
            "`HadamardBFormal/Data.lean`, and the Hadamard conclusions are derived from",
            "Theorem A in `HadamardBFormal/Results.lean`.",
            "-/",
            "",
            "namespace HadamardBFormalCore.Data",
            "",
            "open HadamardBFormalCore",
            "",
            "/-- The gate group `G = ZMod 2 x ZMod 2 x ZMod 3`, of order 12. -/",
            "abbrev G52 : Type := ZMod 2 × ZMod 2 × ZMod 3",
            "",
            "/-- The flat index of a group element, in the row-major mixed-radix order of",
            "`Hadamard-B/tools/bordered_gs.py` (`AbelianGroup.idx`): `(a,b,c) ↦ 6a + 3b + c`. -/",
            "def gidx52 (z : G52) : Fin 12 :=",
            "  ⟨6 * z.1.val + 3 * z.2.1.val + z.2.2.val, by",
            "    have h0 : z.1.val < 2 := ZMod.val_lt z.1",
            "    have h1 : z.2.1.val < 2 := ZMod.val_lt z.2.1",
            "    have h2 : z.2.2.val < 3 := ZMod.val_lt z.2.2",
            "    omega⟩",
            "",
            "/-- The flat index of a border-table column `(J, b)`, class index fastest:",
            "`(J, b) ↦ 2J + b`. -/",
            "def pairIdx (z : Fin 4 × ZMod 2) : Fin 8 :=",
            "  ⟨2 * z.1.val + z.2.val, by",
            "    have h0 : z.1.val < 4 := z.1.isLt",
            "    have h1 : z.2.val < 2 := ZMod.val_lt z.2",
            "    omega⟩",
            "",
            "/-- The index-two character of `G`, `coset_divisors = [2,1,1]`: the first",
            "coordinate. -/",
            "def kappa52 : G52 →+ ZMod 2 where",
            "  toFun z := z.1",
            "  map_zero' := rfl",
            "  map_add' _ _ := rfl",
            "",
            "@[simp]",
            "theorem kappa52_apply (z : G52) : kappa52 z = z.1 := rfl",
            "",
            "/-- The reflection shift `ρ`, the record's `r_shift = (0,0,0)`.  Since `κ ρ = 0`",
            "this instance is the `ε = +1` branch. -/",
            "def rho52 : G52 := 0",
            "",
        ]
    )

    lines.extend(format_table("seed52Data", gate["seeds"], n))
    lines.extend(
        [
            "/-- The four seed sequences of the gate record, as functions on `G`. -/",
            "def seed52 : Fin 4 → G52 → ℤ := fun q g => (seed52Data.get q).get (gidx52 g)",
            "",
        ]
    )

    lines.extend(format_table("corner52Data", gate["corner"], 4))
    lines.extend(
        [
            "/-- The corner `E` of the gate record. -/",
            "def E52 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ :=",
            "  fun r c => (corner52Data.get r).get c",
            "",
        ]
    )

    lines.extend(format_table("rowTable52Data", gate["row_table"], 8))
    lines.extend(
        [
            "/-- The row table `P` of the gate record, indexed by `Fin 4 × ZMod 2`. -/",
            "def P52 : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=",
            "  fun r z => (rowTable52Data.get r).get (pairIdx z)",
            "",
        ]
    )

    lines.extend(format_table("colTable52Data", gate["col_table"], 8))
    lines.extend(
        [
            "/-- The column table `Q` of the gate record.  The record stores it transposed:",
            "`Q[(I,b)][r] = col_table[r][2I + b]`. -/",
            "def Q52 : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=",
            "  fun z c => (colTable52Data.get c).get (pairIdx z)",
            "",
        ]
    )

    lines.extend(
        [
            "/-! ### The order-20 boundary instance T1 -/",
            "",
            "/-- The boundary group `G = ZMod 2 x ZMod 2`, of order 4. -/",
            "abbrev G20 : Type := ZMod 2 × ZMod 2",
            "",
            "/-- The flat index of a group element, row-major mixed radix: `(a,b) ↦ 2a + b`. -/",
            "def gidx20 (z : G20) : Fin 4 :=",
            "  ⟨2 * z.1.val + z.2.val, by",
            "    have h0 : z.1.val < 2 := ZMod.val_lt z.1",
            "    have h1 : z.2.val < 2 := ZMod.val_lt z.2",
            "    omega⟩",
            "",
            "/-- The **diagonal** index-two subgroup `K = ⟨(1,1)⟩`, presented as the",
            "surjective hom `κ(a,b) = a + b`.  This is not a coordinate kernel, which is",
            "exactly the point of the boundary record. -/",
            "def kappa20 : G20 →+ ZMod 2 where",
            "  toFun z := z.1 + z.2",
            "  map_zero' := rfl",
            "  map_add' a b := add_add_add_comm a.1 b.1 a.2 b.2",
            "",
            "@[simp]",
            "theorem kappa20_apply (z : G20) : kappa20 z = z.1 + z.2 := rfl",
            "",
            "/-- The reflection shift `ρ = (1,1)` of the boundary record.  Note `κ ρ = 0`. -/",
            "def rho20 : G20 := (1, 1)",
            "",
        ]
    )

    lines.extend(format_table("seed20Data", boundary["seeds"], boundary["n"]))
    lines.extend(
        [
            "/-- The four seed sequences of the boundary record. -/",
            "def seed20 : Fin 4 → G20 → ℤ := fun q g => (seed20Data.get q).get (gidx20 g)",
            "",
        ]
    )

    lines.extend(format_table("corner20Data", boundary["corner"], 4))
    lines.extend(
        [
            "/-- The corner `E` of the boundary record. -/",
            "def E20 : Matrix (Fin (4 * 1)) (Fin (4 * 1)) ℤ :=",
            "  fun r c => (corner20Data.get r).get c",
            "",
        ]
    )

    lines.extend(format_table("rowTable20Data", boundary["row_table"], 8))
    lines.extend(
        [
            "/-- The row table `P` of the boundary record. -/",
            "def P20 : Matrix (Fin (4 * 1)) (Fin 4 × ZMod 2) ℤ :=",
            "  fun r z => (rowTable20Data.get r).get (pairIdx z)",
            "",
        ]
    )

    lines.extend(format_table("colRows20Data", boundary["col_rows"], 4))
    lines.extend(
        [
            "/-- The column table `Q` of the boundary record.  This record stores `Q` row by",
            "row — `Q[(I,b)][r] = col_rows[2I + b][r]` — not transposed. -/",
            "def Q20 : Matrix (Fin 4 × ZMod 2) (Fin (4 * 1)) ℤ :=",
            "  fun z c => (colRows20Data.get (pairIdx z)).get c",
            "",
            "end HadamardBFormalCore.Data",
            "",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-root",
        type=Path,
        required=True,
        help="path to the Hadamard-B repository root (the directory containing data/)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"generated Lean file (default: {DEFAULT_OUTPUT})",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that --output already equals the deterministic generated content",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        content = render(args.source_root)
    except ExportError as error:
        raise SystemExit(f"export_data.py: error: {error}") from error

    encoded = content.encode("utf-8")
    output = args.output
    if args.check:
        try:
            existing = output.read_bytes()
        except OSError as error:
            raise SystemExit(f"export_data.py: error: cannot read {output}: {error}") from error
        if existing != encoded:
            raise SystemExit(f"export_data.py: error: generated output differs from {output}")
        print(f"up to date: {output} ({hashlib.sha256(encoded).hexdigest()})")
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.tmp-{os.getpid()}")
    try:
        temporary.write_bytes(encoded)
        os.replace(temporary, output)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
    print(
        f"wrote {output} ({len(encoded)} bytes, "
        f"SHA-256 {hashlib.sha256(encoded).hexdigest()})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
