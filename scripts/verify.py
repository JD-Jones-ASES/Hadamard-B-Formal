#!/usr/bin/env python3
"""The single local verification entrypoint for this package.

Standard library only.  Runs, in order:

1. `lake build` in a sanitised environment -- the library, `Challenge`,
   `Solution`, and `Test.AxiomAudit`, whose `#eval` performs the transitive
   axiom audit over every compared declaration at build time;
2. `scripts/export_data.py --check` -- the committed generated data is the
   deterministic render of the pinned source bytes;
3. `scripts/crosscheck_assembly.py` -- both instances, reassembled from
   `Challenge.lean`'s index semantics, carry the digests the source records pin;
4. a forbidden-token scan -- no `sorry`, `admit`, `native_decide`, or custom
   `axiom` anywhere outside `Challenge.lean`, and exactly as many deliberate
   holes in `Challenge.lean` as there are compared theorems;
5. a set-equality check over the six hand-maintained lists that must agree:
   `comparator.json`, `Test/AxiomAudit.lean`, `Challenge.lean`, `Solution.lean`,
   and `formalization.yaml`'s `main_results` and `alignment.statements`.

NOTE: Palomar Comparator, `lean4export`, and NanoDa are NOT run here and are not
installed on this machine.  They run only in Palomar's protected environment,
where a successful run additionally establishes that the recorded Solution
satisfies the recorded Challenge and that the exported proof replays through
Lean's kernel and the pinned NanoDa kernel.  Nothing in either set establishes
fidelity to the informal source, novelty, interest, or peer review.

Usage:

    python -B scripts/verify.py --source-root <Hadamard-B checkout>

Exit code 0 iff every step passes.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NAMESPACE = "HadamardBFormal"

# Environment variables a build is allowed to inherit.  Anything Lean- or
# Lake-specific is dropped, so a leaked LEAN_PATH cannot shadow the pinned tree.
ENV_KEEP = (
    "PATH", "PATHEXT", "SYSTEMROOT", "WINDIR", "COMSPEC", "HOME", "USERPROFILE",
    "TEMP", "TMP", "TMPDIR", "APPDATA", "LOCALAPPDATA", "ELAN_HOME",
    "SYSTEMDRIVE", "PROGRAMFILES", "PROGRAMDATA", "LANG", "LC_ALL",
)

TOKENS = re.compile(r"(?<![\w'])(sorry|admit|native_decide)(?![\w'])")
AXIOM_DECL = re.compile(r"^\s*axiom\s", re.M)
CHALLENGE_THEOREM = re.compile(r"^theorem\s+([A-Za-z_][\w']*)", re.M)
CHALLENGE_DEF = re.compile(r"^(?:def|abbrev)\s+([A-Za-z_][\w']*)", re.M)
AUDIT_DECL = re.compile(r"``(" + NAMESPACE + r"\.[\w'.]+)")
YAML_DECLARATION = re.compile(r'^\s*-\s*declaration:\s*"([^"]+)"', re.M)
YAML_LEAN = re.compile(r'^\s*lean:\s*"([^"]+)"', re.M)


class Report:
    def __init__(self) -> None:
        self.failures: list[str] = []

    def check(self, ok: bool, label: str, detail: str = "") -> bool:
        if ok:
            print(f"  PASS  {label}")
        else:
            print(f"  FAIL  {label}" + (f"\n        {detail}" if detail else ""))
            self.failures.append(label)
        return ok


def sanitised_env() -> dict[str, str]:
    env = {key: os.environ[key] for key in ENV_KEEP if key in os.environ}
    env.setdefault("PATH", os.defpath)
    return env


def run(command: list[str], label: str, report: Report, tail: int = 12) -> bool:
    print(f"\n{label}")
    print(f"  $ {' '.join(command)}")
    completed = subprocess.run(
        command,
        cwd=str(ROOT),
        env=sanitised_env(),
        capture_output=True,
        text=True,
        errors="replace",
    )
    output = ((completed.stdout or "") + (completed.stderr or "")).strip()
    lines = output.splitlines()
    for line in lines[-tail:]:
        print(f"  | {line}")
    if len(lines) > tail:
        print(f"  | ... ({len(lines) - tail} earlier lines suppressed)")
    return report.check(completed.returncode == 0, label,
                        f"exit status {completed.returncode}")


def strip_comments(text: str) -> str:
    """Blank out Lean comments and string literals, preserving offsets.

    The token scan is about code, not prose: `Data.lean` says "`decide`, never
    `native_decide`" in a docstring and must not trip it.  Block comments nest,
    so the depth is tracked rather than regex-matched.
    """
    out = list(text)
    index, length, depth = 0, len(text), 0
    while index < length:
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                out[index] = out[index + 1] = " "
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                out[index] = out[index + 1] = " "
                index += 2
                continue
            if text[index] != "\n":
                out[index] = " "
            index += 1
            continue
        if pair == "/-":
            depth = 1
            out[index] = out[index + 1] = " "
            index += 2
            continue
        if pair == "--":
            while index < length and text[index] != "\n":
                out[index] = " "
                index += 1
            continue
        if text[index] == '"':
            out[index] = " "
            index += 1
            while index < length and text[index] != '"':
                if text[index] == "\\" and index + 1 < length:
                    if text[index + 1] != "\n":
                        out[index + 1] = " "
                    out[index] = " "
                    index += 2
                    continue
                if text[index] != "\n":
                    out[index] = " "
                index += 1
            if index < length:
                out[index] = " "
                index += 1
            continue
        index += 1
    return "".join(out)


def lean_sources() -> list[Path]:
    paths = [ROOT / "Solution.lean", ROOT / "HadamardBFormal.lean"]
    for directory in ("HadamardBFormal", "Test"):
        paths.extend(sorted((ROOT / directory).rglob("*.lean")))
    return [path for path in paths if path.is_file()]


def forbidden_tokens(report: Report, challenge_theorems: int) -> None:
    print("\nStep 4: forbidden-token scan")
    offenders: list[str] = []
    for path in lean_sources():
        text = strip_comments(path.read_text(encoding="utf-8"))
        relative = path.relative_to(ROOT).as_posix()
        for match in TOKENS.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            offenders.append(f"{relative}:{line}: {match.group(1)}")
        for match in AXIOM_DECL.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            offenders.append(f"{relative}:{line}: axiom declaration")
    report.check(not offenders,
                 "no sorry/admit/native_decide/axiom outside Challenge.lean",
                 "; ".join(offenders[:8]))

    challenge = strip_comments((ROOT / "Challenge.lean").read_text(encoding="utf-8"))
    holes = len(TOKENS.findall(challenge))
    report.check(holes == challenge_theorems,
                 f"Challenge.lean holds exactly one deliberate hole per compared "
                 f"theorem ({challenge_theorems})",
                 f"found {holes} holes")
    report.check(not AXIOM_DECL.search(challenge),
                 "Challenge.lean declares no axiom")


def read_lists() -> dict[str, list[str]]:
    comparator = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    challenge = strip_comments((ROOT / "Challenge.lean").read_text(encoding="utf-8"))
    solution = strip_comments((ROOT / "Solution.lean").read_text(encoding="utf-8"))
    audit = strip_comments(
        (ROOT / "Test" / "AxiomAudit.lean").read_text(encoding="utf-8"))
    metadata = (ROOT / "formalization.yaml").read_text(encoding="utf-8")

    def qualify(names) -> list[str]:
        return [f"{NAMESPACE}.{name}" for name in names]

    return {
        "comparator.json theorem_names": comparator["theorem_names"],
        "comparator.json definition_names": comparator["definition_names"],
        "Challenge.lean theorems": qualify(CHALLENGE_THEOREM.findall(challenge)),
        "Challenge.lean definitions": qualify(CHALLENGE_DEF.findall(challenge)),
        "Solution.lean theorems": qualify(CHALLENGE_THEOREM.findall(solution)),
        "Solution.lean definitions": qualify(CHALLENGE_DEF.findall(solution)),
        "Test/AxiomAudit.lean auditedDeclarations": AUDIT_DECL.findall(audit),
        "formalization.yaml main_results": YAML_DECLARATION.findall(metadata),
        "formalization.yaml alignment": YAML_LEAN.findall(metadata),
    }


def set_equality(report: Report) -> int:
    print("\nStep 5: list set-equality")
    lists = read_lists()
    for label, names in lists.items():
        duplicates = sorted({n for n in names if names.count(n) > 1})
        report.check(not duplicates, f"{label} has no duplicate", ", ".join(duplicates))

    theorem_lists = [
        "comparator.json theorem_names",
        "Test/AxiomAudit.lean auditedDeclarations",
        "Challenge.lean theorems",
        "Solution.lean theorems",
        "formalization.yaml main_results",
        "formalization.yaml alignment",
    ]
    definition_lists = [
        "comparator.json definition_names",
        "Challenge.lean definitions",
        "Solution.lean definitions",
    ]
    for group, members in (("theorem", theorem_lists),
                           ("definition", definition_lists)):
        reference = set(lists[members[0]])
        for label in members[1:]:
            other = set(lists[label])
            missing = sorted(reference - other)
            extra = sorted(other - reference)
            detail = ""
            if missing:
                detail += f"missing from {label}: {', '.join(missing)}. "
            if extra:
                detail += f"not in {members[0]}: {', '.join(extra)}."
            report.check(reference == other,
                         f"{label} is set-equal to {members[0]}", detail.strip())
        print(f"  ----  {group} surface: {len(reference)} names")
    return len(set(lists["comparator.json theorem_names"]))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--source-root",
        type=Path,
        required=True,
        help="path to the Hadamard-B repository root (the directory containing data/)",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="skip step 1 (for iterating on the static checks; not a valid preflight)",
    )
    args = parser.parse_args()
    report = Report()

    print(f"hadamard-b-formal local verification\n  repository: {ROOT}\n"
          f"  source:     {args.source_root}")

    if args.no_build:
        print("\nStep 1: lake build -- SKIPPED (--no-build); this is not a preflight run")
    else:
        run(["lake", "--rehash", "build", "--no-ansi"], "Step 1: lake build", report,
            tail=16)

    run([sys.executable, "-B", str(ROOT / "scripts" / "export_data.py"),
         "--source-root", str(args.source_root), "--check"],
        "Step 2: exporter determinism", report)

    run([sys.executable, "-B", str(ROOT / "scripts" / "crosscheck_assembly.py"),
         "--source-root", str(args.source_root)],
        "Step 3: assembly cross-check", report, tail=10)

    compared = set_equality(report)
    forbidden_tokens(report, compared)

    print("\nNOTE: Palomar Comparator, lean4export, and NanoDa were NOT run here.")
    print("      They run only in Palomar's protected environment.  A successful")
    print("      protected run would additionally establish that the recorded")
    print("      Solution satisfies the recorded Challenge and that the exported")
    print("      proof replays through Lean's kernel and the pinned NanoDa kernel.")
    print("      No check, local or protected, establishes fidelity to the")
    print("      informal source, novelty, interest, or peer review.")

    if report.failures:
        print(f"\nVERIFY: FAIL ({len(report.failures)}): "
              + "; ".join(report.failures))
        return 1
    print("\nVERIFY: PASS -- build, axiom audit, exporter, cross-check, "
          "token scan, and list set-equality all green.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
