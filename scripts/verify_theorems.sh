#!/usr/bin/env bash
# GATE 7R STEP 7 — theorem existence check.
# Each of the 11 bridge theorems must appear EXACTLY ONCE in a .lean file.
# Uses plain grep (not rg): no external dependency, same behavior locally and in CI.
set -euo pipefail

THEOREMS=(
  "avatar_to_core_injective"
  "unsplit_split"
  "split_unsplit_of_default"
  "avatar_split_image_characterization"
  "derivable_does_not_imply_established"
  "toStep_not_injective"
  "toBelief_not_injective"
  "toBelief_not_surjective"
  "toBelief'_surjective"
  "toBelief'_not_injective"
  "verified_and_refuted_distinguished"
)

fail=0
printf "%-42s %s\n" "THEOREM" "MATCHES"
printf -- "---------------------------------------------------------\n"
for t in "${THEOREMS[@]}"; do
  n=$(grep -rE "theorem ${t}\b" RequestProject --include='*.lean' | wc -l)
  status="PASS"
  if [ "$n" -ne 1 ]; then status="FAIL"; fail=1; fi
  printf "%-42s %-3s %s\n" "$t" "$n" "$status"
done

if [ "$fail" -ne 0 ]; then
  echo "FAIL: theorem count mismatch (existence is not uniqueness)" >&2
  exit 1
fi
echo "PASS: 11/11 theorems found exactly once"
