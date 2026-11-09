#!/usr/bin/env python3
"""G7R-3b Axiom precision gate — kernel-level axiom surface of the 11 bridge theorems.

Generates a temporary Lean file with `#print axioms` for each bridge theorem,
runs it via `lake env lean` (after `lake build`), and asserts the axiom policy:

* NEW bridge theorems (GATE 7R additions): axiom deps ⊆ {propext}
  — the COUNTEREXAMPLE-FIRST contract, machine-checked on every push;
* legacy bridge theorems: axiom deps ⊆ {propext, Classical.choice, Quot.sound}
  — the standard Mathlib axiom surface, no more.

This catches what grep cannot: `sorryAx` from sorry/admit and `Lean.ofReduceBool`
from native_decide both appear as *axiom dependencies* and fail the allowlist.

Exit 0 = PASS, 1 = FAIL.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GATE_DIR = ROOT / ".gate"

# theorem full name -> policy
NEW = ["avatar_split_image_characterization", "toStep_not_injective", "toBelief'_not_injective"]
LEGACY = [
    "avatar_to_core_injective",
    "unsplit_split",
    "split_unsplit_of_default",
    "derivable_does_not_imply_established",
    "toBelief_not_injective",
    "toBelief_not_surjective",
    "toBelief'_surjective",
    "verified_and_refuted_distinguished",
]
NS = "Polymath.STCKG"
ALLOWED_NEW = {"propext"}
ALLOWED_LEGACY = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    GATE_DIR.mkdir(exist_ok=True)
    check_file = GATE_DIR / "AxiomGate.lean"
    names = [f"{NS}.{n}" for n in NEW + LEGACY]
    check_file.write_text(
        "import RequestProject.STCKG.Core\n"
        "import RequestProject.STCKG.Claim\n"
        "import RequestProject.STCKG.Evidence\n\n"
        + "\n".join(f"#print axioms {n}" for n in names)
        + "\n",
        encoding="utf-8",
    )

    proc = subprocess.run(
        ["lake", "env", "lean", str(check_file.relative_to(ROOT))],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=600,
    )
    output = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print("FAIL: lake env lean returned non-zero exit")
        print(output[-4000:])
        return 1

    pattern = re.compile(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
    deps: dict[str, set[str]] = {}
    for m in pattern.finditer(output):
        if m.group(2) is None:
            # "'name' does not depend on any axioms"
            deps[m.group(1)] = set()
        else:
            deps[m.group(1)] = set(s.strip() for s in m.group(2).split(",") if s.strip())

    failed = False
    print(f"{'THEOREM':60s} {'AXIOM DEPS':45s} POLICY  RESULT")
    print("-" * 130)
    for full in names:
        short = full.rsplit(".", 1)[-1]
        actual = deps.get(full)
        if actual is None:
            print(f"{short:60s} {'<MISSING FROM OUTPUT>':45s} -       FAIL")
            failed = True
            continue
        allowed = ALLOWED_NEW if short in NEW else ALLOWED_LEGACY
        ok = actual <= allowed
        policy = "⊆ {propext}" if short in NEW else "⊆ Mathlib defaults"
        print(f"{short:60s} {('[{' + ', '.join(sorted(actual)) + '}]') if actual else '{} (none)':45s} {policy:8s} {'PASS' if ok else 'FAIL'}")
        if not ok:
            failed = True

    if failed:
        print("\nG7R-3b Axiom precision: FAIL — axiom surface exceeds policy")
        return 1
    print("\nG7R-3b Axiom precision: PASS — 11/11 theorems within policy (3 new: propext-only)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
