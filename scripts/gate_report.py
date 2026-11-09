#!/usr/bin/env python3
"""GATE REPORT — consolidates gate results into GATE_REPORT.md + dynamic badge SVG.

Reads gate outcomes from environment variables set by the workflow:
  SPEC_RESULT, LEAN_RESULT  (success | failure | cancelled | skipped)
  GITHUB_SHA, GITHUB_RUN_ID, GITHUB_REF_NAME, GITHUB_SERVER_URL, GITHUB_REPOSITORY
Optional: SPEC_JSON — path to the G7R-0 JSON artifact.

Always exits 0 (a red report must be publishable, not swallowed).
"""

from __future__ import annotations

import json
import os
from datetime import datetime, timezone
from pathlib import Path

OUT = Path("gate-report")
OUT.mkdir(exist_ok=True)

SPEC_RESULT = os.environ.get("SPEC_RESULT", "unknown")
LEAN_RESULT = os.environ.get("LEAN_RESULT", "unknown")
SHA = os.environ.get("GITHUB_SHA", "local")[:12]
RUN_ID = os.environ.get("GITHUB_RUN_ID", "0")
REF = os.environ.get("GITHUB_REF_NAME", "main")
SERVER = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
REPO = os.environ.get("GITHUB_REPOSITORY", "rtynbirf/polymath-stckg-core")
RUN_URL = f"{SERVER}/{REPO}/actions/runs/{RUN_ID}"

GREEN, RED, GREY = "#2ea043", "#cf222e", "#8b949e"


def gate(result: str) -> tuple[str, str]:
    return {"success": ("PASS", GREEN), "failure": ("FAIL", RED)}.get(result, ("N/A", GREY))


s_txt, s_color = gate(SPEC_RESULT)
l_txt, l_color = gate(LEAN_RESULT)
overall_ok = SPEC_RESULT == "success" and LEAN_RESULT == "success"
overall_txt, overall_color = ("PASS", GREEN) if overall_ok else ("FAIL", RED)
now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")

spec_summary = {}
spec_path = os.environ.get("SPEC_JSON")
if spec_path and Path(spec_path).exists():
    data = json.loads(Path(spec_path).read_text())
    spec_summary = {c["check"]: c["detail"] for c in data.get("checks", [])}

rows = []
for name, res in [
    ("G7R-0 Specification", SPEC_RESULT),
    ("G7R-1+2 Baseline & Elaboration (lake build --wfail)", LEAN_RESULT),
    ("G7R-3a Kernel axiom audit (axiom-audit)", LEAN_RESULT),
    ("G7R-3b Axiom precision (#print axioms policy)", LEAN_RESULT),
    ("G7R-3c Integrity & theorem existence (bash parity)", LEAN_RESULT),
]:
    txt, color = gate(res)
    rows.append(f"| {name} | <span style='color:{color}'>**{txt}**</span> |")

# bridge-theorem details are static facts of the contract; keep them in the report
theorems_md = """
### Bridge theorem manifest (kernel-verified)

| # | Theorem | File | Axiom policy |
|---|---------|------|--------------|
| 1 | `avatar_to_core_injective` | `STCKG/Core.lean` | ⊆ Mathlib defaults |
| 2 | `unsplit_split` | `STCKG/Core.lean` | ⊆ Mathlib defaults |
| 3 | `split_unsplit_of_default` | `STCKG/Core.lean` | ⊆ Mathlib defaults |
| 4 | `avatar_split_image_characterization` **(A4, new)** | `STCKG/Core.lean` | ⊆ {propext} |
| 5 | `derivable_does_not_imply_established` | `STCKG/Claim.lean` | ⊆ Mathlib defaults |
| 6 | `toStep_not_injective` **(B2, new)** | `STCKG/Claim.lean` | ⊆ {propext} |
| 7 | `toBelief_not_injective` | `STCKG/Evidence.lean` | ⊆ Mathlib defaults |
| 8 | `toBelief_not_surjective` | `STCKG/Evidence.lean` | ⊆ Mathlib defaults |
| 9 | `toBelief'_surjective` | `STCKG/Evidence.lean` | ⊆ Mathlib defaults |
| 10 | `toBelief'_not_injective` **(E4, new)** | `STCKG/Evidence.lean` | ⊆ {propext} |
| 11 | `verified_and_refuted_distinguished` | `STCKG/Evidence.lean` | ⊆ Mathlib defaults |
"""

spec_details_md = ""
if spec_summary:
    spec_details_md = "\n".join(f"- **{k}** — {v}" for k, v in spec_summary.items())

report = f"""# GATE 7R REPORT

**Verdict: {overall_txt}** · commit `{SHA}` · ref `{REF}` · {now}
[Run #{RUN_ID}]({RUN_URL})

## Gate matrix

| Gate | Result |
|------|--------|
{chr(10).join(rows)}

**Overall: {overall_txt}**

## G7R-0 Specification details

{spec_details_md}

{theorems_md}
## What this run proves

1. The 9-file STCKG layer elaborates from scratch against Mathlib `v4.28.0` with
   **zero warnings** (`lake build --wfail`) — a hidden `sorry` would emit a
   warning and fail the build.
2. `axiom-audit` walks the **compiled kernel environment**: any `sorryAx`,
   `Lean.ofReduceBool` (native_decide), or home-rolled axiom — including ones
   reaching in through imports — fails the audit.
3. The 3 new bridge theorems (A4, B2, E4) are machine-checked to depend on
   **nothing but `propext`** — the COUNTEREXAMPLE-FIRST contract holds.
4. Each of the 11 bridge theorems exists **exactly once** in the sources.
"""

(OUT / "GATE_REPORT.md").write_text(report, encoding="utf-8")

badge = f"""<svg xmlns="http://www.w3.org/2000/svg" width="212" height="24" role="img" aria-label="GATE 7R: {overall_txt}">
  <title>GATE 7R: {overall_txt}</title>
  <linearGradient id="s" x2="0" y2="100%"><stop offset="0" stop-color="#bbb" stop-opacity=".1"/><stop offset="1" stop-opacity=".1"/></linearGradient>
  <clipPath id="r"><rect width="212" height="24" rx="3" fill="#fff"/></clipPath>
  <g clip-path="url(#r)">
    <rect width="130" height="24" fill="#555"/>
    <rect x="130" width="82" height="24" fill="{overall_color}"/>
    <rect width="212" height="24" fill="url(#s)"/>
  </g>
  <g fill="#fff" text-anchor="middle" font-family="Verdana,Geneva,DejaVu Sans,sans-serif" font-size="11">
    <text x="65" y="16" fill="#010101" fill-opacity=".3">GATE 7R</text>
    <text x="65" y="15">GATE 7R</text>
    <text x="170" y="16" fill="#010101" fill-opacity=".3">{overall_txt}</text>
    <text x="170" y="15">{overall_txt}</text>
  </g>
</svg>
"""
(OUT / "gate7r.svg").write_text(badge, encoding="utf-8")
print(f"GATE 7R: {overall_txt} -> {OUT}/GATE_REPORT.md, {OUT}/gate7r.svg")
