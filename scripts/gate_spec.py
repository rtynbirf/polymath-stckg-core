#!/usr/bin/env python3
"""G7R-0 Specification gate — static, kernel-independent integrity checks.

Runs in under a second, needs no Lean toolchain. Fails the pipeline BEFORE
an expensive `lake build` if any structural contract is violated.

Checks
------
1. STCKG strict scan   : no sorry / admit / sorryAx / axiom / unsafe /
                          @[implemented_by] / native_decide inside
                          RequestProject/STCKG/
2. Project axiom scan  : no `axiom` declarations anywhere in RequestProject/
3. Theorem manifest    : each of the 11 bridge theorems appears EXACTLY ONCE
4. File inventory      : the 9-file STCKG layer is present and unchanged
5. Toolchain pinning   : lean-toolchain == lakefile mathlib rev ==
                          lake-manifest mathlib inputRev
6. Secret scan         : no credential patterns in tracked files

Exit code 0 = PASS, 1 = FAIL. JSON report via --json PATH.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT / "RequestProject"
STCKG = PROJECT / "STCKG"

STCKG_FILES = {
    "CategoryGate.lean", "Claim.lean", "Composition.lean", "Core.lean",
    "Correspondence.lean", "Evidence.lean", "EvolutionAudit.lean",
    "Index.lean", "IndexedFamily.lean",
}

BRIDGE_THEOREMS = [
    "avatar_to_core_injective",
    "unsplit_split",
    "split_unsplit_of_default",
    "avatar_split_image_characterization",
    "derivable_does_not_imply_established",
    "toStep_not_injective",
    "toBelief_not_injective",
    "toBelief_not_surjective",
    "toBelief'_surjective",
    "toBelief'_not_injective",
    "verified_and_refuted_distinguished",
]

NEW_BRIDGE_THEOREMS = {
    "avatar_split_image_characterization",   # A4, [propext]
    "toStep_not_injective",                  # B2, [propext]
    "toBelief'_not_injective",               # E4, [propext]
}

FORBIDDEN_STCKG = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"sorryAx", "sorryAx"),
    (r"^\s*axiom\s", "axiom declaration"),
    (r"\bunsafe\b", "unsafe"),
    (r"@\[implemented_by\]", "@[implemented_by]"),
    (r"native_decide", "native_decide"),
]

SECRET_PATTERNS = [
    (r"ghp_[A-Za-z0-9]{30,}", "GitHub PAT (classic)"),
    (r"github_pat_[A-Za-z0-9_]{40,}", "GitHub PAT (fine-grained)"),
    (r"gh[pousr]_[A-Za-z0-9]{20,}", "GitHub token (app/refresh/server/user)"),
    (r"AKIA[0-9A-Z]{16}", "AWS access key"),
    (r"xox[baprs]-[A-Za-z0-9-]{10,}", "Slack token"),
    (r"BEGIN (RSA |EC )?PRIVATE KEY", "private key block"),
]

results: list[dict] = []
failed = False


def record(name: str, ok: bool, detail: str) -> None:
    global failed
    results.append({"check": name, "result": "PASS" if ok else "FAIL", "detail": detail})
    print(f"[{'PASS' if ok else 'FAIL'}] {name}: {detail}")
    if not ok:
        failed = True


def scan_text_files(directory: Path):
    for p in sorted(directory.rglob("*.lean")):
        yield p


def main() -> int:
    # ---- 1. STCKG strict scan -------------------------------------------
    stckg_hits: list[str] = []
    for p in scan_text_files(STCKG):
        text = p.read_text(encoding="utf-8", errors="replace")
        for i, line in enumerate(text.splitlines(), 1):
            for pattern, label in FORBIDDEN_STCKG:
                if re.search(pattern, line):
                    stckg_hits.append(f"{p.relative_to(ROOT)}:{i} [{label}] {line.strip()[:100]}")
    record(
        "STCKG strict scan (0 forbidden constructs)",
        not stckg_hits,
        f"0 matches in RequestProject/STCKG/" if not stckg_hits else f"{len(stckg_hits)} matches",
    )
    for h in stckg_hits[:20]:
        print(f"       {h}")

    # ---- 2. project-wide axiom declarations ------------------------------
    axiom_hits: list[str] = []
    for p in scan_text_files(PROJECT):
        text = p.read_text(encoding="utf-8", errors="replace")
        for i, line in enumerate(text.splitlines(), 1):
            if re.search(r"^\s*axiom\s", line):
                axiom_hits.append(f"{p.relative_to(ROOT)}:{i} {line.strip()[:100]}")
    record(
        "Project axiom scan (0 custom axioms)",
        not axiom_hits,
        "axiom surface = Mathlib defaults only" if not axiom_hits else f"{len(axiom_hits)} axiom declarations",
    )
    for h in axiom_hits[:20]:
        print(f"       {h}")

    # ---- 3. theorem manifest (exactly once each) -------------------------
    theorem_counts: dict[str, int] = {}
    sources: dict[str, str] = {}
    for p in scan_text_files(PROJECT):
        sources[str(p)] = p.read_text(encoding="utf-8", errors="replace")
    manifest_ok = True
    for t in BRIDGE_THEOREMS:
        pattern = re.compile(rf"theorem\s+{re.escape(t)}\b")
        n = sum(len(pattern.findall(src)) for src in sources.values())
        theorem_counts[t] = n
        if n != 1:
            manifest_ok = False
    new_ok = all(theorem_counts[t] == 1 for t in NEW_BRIDGE_THEOREMS)
    record(
        "Bridge theorem manifest (11 theorems, exactly once each)",
        manifest_ok,
        f"{sum(1 for c in theorem_counts.values() if c == 1)}/11 unique"
        + ("; all 3 new theorems present" if new_ok else "; NEW-THEOREM MANIFEST BROKEN"),
    )
    for t, n in theorem_counts.items():
        mark = "*" if t in NEW_BRIDGE_THEOREMS else " "
        print(f"       {mark} {t:45s} x{n}")

    # ---- 4. file inventory ------------------------------------------------
    present = {p.name for p in STCKG.glob("*.lean")}
    record(
        "STCKG file inventory (9 files)",
        present == STCKG_FILES,
        f"{len(present)}/9 files" + ("" if present == STCKG_FILES else f"; diff: {present ^ STCKG_FILES}"),
    )

    # ---- 5. toolchain pinning consistency ---------------------------------
    tc = (ROOT / "lean-toolchain").read_text().strip()
    tc_version = tc.rsplit(":", 1)[-1]
    lakefile = (ROOT / "lakefile.toml").read_text()
    m = re.search(r'name\s*=\s*"mathlib".*?rev\s*=\s*"([^"]+)"', lakefile, re.S)
    lakefile_rev = m.group(1) if m else None
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next((pkg for pkg in manifest["packages"] if pkg["name"] == "mathlib"), None)
    manifest_rev = mathlib["inputRev"] if mathlib else None
    pinned_ok = tc_version == lakefile_rev == manifest_rev
    record(
        "Toolchain pinning (toolchain == lakefile == manifest)",
        pinned_ok,
        f"lean-toolchain={tc_version}, lakefile mathlib rev={lakefile_rev}, manifest inputRev={manifest_rev}",
    )

    # ---- 6. secret scan -----------------------------------------------------
    secret_hits: list[str] = []
    skip_dirs = {".git", ".lake", "node_modules"}
    for p in ROOT.rglob("*"):
        if not p.is_file() or any(part in skip_dirs for part in p.parts):
            continue
        try:
            text = p.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        for i, line in enumerate(text.splitlines(), 1):
            for pattern, label in SECRET_PATTERNS:
                if re.search(pattern, line):
                    secret_hits.append(f"{p.relative_to(ROOT)}:{i} [{label}]")
    record(
        "Secret scan (0 credentials in tracked files)",
        not secret_hits,
        "clean" if not secret_hits else f"{len(secret_hits)} hits: {secret_hits[:10]}",
    )

    # ---- JSON report ---------------------------------------------------------
    report = {
        "gate": "G7R-0 Specification",
        "project": "polymath-stckg-core",
        "checks": results,
        "pass": not failed,
        "theorem_counts": theorem_counts,
        "new_theorems_propext_only_contract": sorted(NEW_BRIDGE_THEOREMS),
    }
    json_path = None
    if "--json" in sys.argv:
        json_path = sys.argv[sys.argv.index("--json") + 1]
        Path(json_path).write_text(json.dumps(report, indent=2, ensure_ascii=False))
        print(f"JSON report -> {json_path}")

    print(f"\nG7R-0 Specification: {'PASS' if not failed else 'FAIL'}")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
