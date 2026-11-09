#!/usr/bin/env bash
# GATE 7R STEP 6 — integrity scan (local, STCKG scoped).
set -euo pipefail

echo "== forbidden constructs in RequestProject/STCKG/ =="
if rg -n '\bsorry\b|\badmit\b|sorryAx|^\s*axiom\s|\bunsafe\b|@\[implemented_by\]' RequestProject/STCKG/; then
  echo "FAIL: forbidden constructs found" >&2
  exit 1
fi
echo "PASS: 0 sorry / 0 admit / 0 sorryAx / 0 axiom / 0 unsafe / 0 @[implemented_by]"

echo
echo "== axiom transparency (whole project, declarations only) =="
if rg -n '^\s*axiom\s' RequestProject/; then
  echo "FAIL: custom axioms declared" >&2
  exit 1
fi
echo "PASS: axiom surface = Mathlib defaults only"
