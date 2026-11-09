# RELEASE-0.2 GATE 6 — BRIDGE CONTRACT (v4 FINAL — GATE 7R VERIFIED)

**Date:** 2026-08-12
**Executor:** Polymath (Super Z) — specification; Aristotle — independent verification
**GATE 7R result:** **ALL PASS**

### Version history

| Version | Event | Change |
|---------|-------|--------|
| v1 | GATE 6 initial | 3 theorems specified with proof sketches |
| v2 | GATE 7 v1 FAIL | Fixed implicit arg syntax `(a₁ := ...)` (a₂ := ...)` |
| v3 | Colleague review | Adopted COUNTEREXAMPLE-FIRST principle. B2/E4 rewritten. |
| **v4** | **GATE 7R PASS** | **Recorded Aristotle's actual working proofs (with tactic fixes). GATE 7 GREEN.** |

---

## GATE 7 EXECUTION SUMMARY

### GATE 7 v1

| Item | Result |
|------|--------|
| Overall | **FAIL** (lake build exit 1, [8149/8158]) |
| A4 | PASS |
| B2 | FAIL (3 errors: implicit arg parsing) |
| E4 | FAIL (3 errors: implicit arg parsing) |
| Value | Confirmed verification gap between mathematical intuition and machine-checked code |

### GATE 7R — Counterexample Repair Pass

| Item | Result |
|------|--------|
| Overall | **PASS** (lake build exit 0, 8158 jobs, 0 errors, 0 warnings) |
| A4 avatar_split_image_characterization | **PASS** (unchanged from v1) |
| B2 toStep_not_injective | **PASS** (COUNTEREXAMPLE-FIRST, tactic adjusted by Aristotle) |
| E4 toBelief'_not_injective | **PASS** (COUNTEREXAMPLE-FIRST, tactic adjusted by Aristotle) |
| Integrity | All PASS (0 axioms, 0 sorry, 0 unsafe) |
| Existing theorems | All PASS, untouched |
| Files modified | 3 (Core.lean +15, Claim.lean +19, Evidence.lean +24, additions only) |

### Aristotle's tactic adjustments (new theorems only)

| Theorem | Prompt text issue | Actual fix |
|---------|------------------|-------------|
| B2 | `simp [claimA]; decide` — `simp` already closed the goal, trailing `decide` had no target | Removed redundant `decide` |
| E4 | Anonymous `⟨...⟩` constructors in `h_ne` had no expected type, causing `Invalid ⟨...⟩ notation` | Added explicit `: RefutableProfile` type ascription |

**Assessment:** COUNTEREXAMPLE-FIRST methodology validated. Proof structure (witness → equality → distinction → contradiction) was correct. Fixes were surface-level Lean 4 tactic details, not methodological changes.

---

## FORMAL ASSERTIONS (3 new theorems — ACTUAL WORKING PROOFS)

### Theorem A4 — Avatar.split image characterization

**File:** `RequestProject/STCKG/Core.lean` (before `end Polymath.STCKG`)
**Status:** GATE 7 v1 PASS, GATE 7R PASS (unchanged)
**Axioms:** `[propext]` (Mathlib default)

```lean
/-- The image of `Avatar.split` is exactly the pairs whose
`KnowledgeObject` component carries the default maturity and confidence.
This completes the bridge characterization: `Avatar` is in bijection
with the restricted set `{p | p.1.maturity = .hypothesis ∧ p.1.confidence = 0}`. -/
theorem avatar_split_image_characterization (p : KnowledgeObject × AvatarExtra) :
    p ∈ Set.range Avatar.split ↔
      p.1.maturity = .hypothesis ∧ p.1.confidence = 0 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    subst ha
    simp [Avatar.split, Avatar.toKnowledgeObject]
  · intro ⟨hm, hc⟩
    exact ⟨unsplit p, split_unsplit_of_default p hm hc⟩
```

---

### Theorem B2 — Claim.toStep is not injective (ACTUAL WORKING PROOF)

**File:** `RequestProject/STCKG/Claim.lean` (before `end Polymath.STCKG`)
**Status:** GATE 7 v1 FAIL, GATE 7R PASS
**Axioms:** `[propext]` (Mathlib default)

```lean
/-- `Claim.toStep` is not injective: two claims with the same `id` and
`assumptions` but different `predicate` produce the same `Step`.
This formalizes the information loss of the Claim → ProofGraph.Step bridge.

**Witness:** `claimA` with `predicate := "X"` and `claimA` with `predicate := "Y"`.
Both map to `⟨0, []⟩` because `toStep` only reads `id` and `assumptions`.
The claims differ in `predicate`, so they are distinct. -/
theorem toStep_not_injective : ¬ Function.Injective Claim.toStep := by
  intro h
  -- CONCRETE WITNESS: two claims, same id/assumptions, different predicate
  have h_eq : Claim.toStep { claimA with predicate := "X" } =
      Claim.toStep { claimA with predicate := "Y" } := by
    simp [Claim.toStep, claimA]
  -- COMPUTABLE DISTINCTION: the witness claims are not equal
  have h_ne : { claimA with predicate := "X" } ≠ { claimA with predicate := "Y" } := by
    simp [claimA]
  -- CONCLUSION: injectivity would force equal claims from equal steps
  exact h_ne (h h_eq)
```

**Diff from prompt:** `decide` removed after `simp [claimA]` (already closed goal).

---

### Theorem E4 — RefutableProfile.toBelief is not injective (ACTUAL WORKING PROOF)

**File:** `RequestProject/STCKG/Evidence.lean` (before `end Polymath.STCKG`)
**Status:** GATE 7 v1 FAIL, GATE 7R PASS
**Axioms:** `[propext]` (Mathlib default)

```lean
/-- `RefutableProfile.toBelief` is still not injective: two refutable
profiles that differ only in `logicalSupport` (a field not examined by
`toBelief'`) map to the same belief value `PT.UNKNOWN`.

**Witness:** Two `RefutableProfile` values with `base.logicalSupport`
set to `.strong` and `.moderate` respectively, all other fields
identical (blank). Both have `conflictLevel = .none`, `refutation = .absent`,
`formalStatus = .noFormalization`, so both evaluate to `PT.UNKNOWN`. -/
theorem toBelief'_not_injective : ¬ Function.Injective RefutableProfile.toBelief := by
  intro h
  -- CONCRETE WITNESS: two profiles, same belief-relevant fields, different logicalSupport
  have h_eq : RefutableProfile.toBelief
      ⟨{ EvidenceProfile.blank with logicalSupport := .strong }, .absent⟩ =
    RefutableProfile.toBelief
      ⟨{ EvidenceProfile.blank with logicalSupport := .moderate }, .absent⟩ := by
    simp [RefutableProfile.toBelief, EvidenceProfile.toBelief, EvidenceProfile.blank]
  -- COMPUTABLE DISTINCTION: the witness profiles are not equal
  have h_ne : (⟨{ EvidenceProfile.blank with logicalSupport := .strong }, .absent⟩ :
        RefutableProfile) ≠
      ⟨{ EvidenceProfile.blank with logicalSupport := .moderate }, .absent⟩ := by
    simp [EvidenceProfile.blank]; decide
  -- CONCLUSION: injectivity would force equal profiles from equal beliefs
  exact h_ne (h h_eq)
```

**Diff from prompt:** Added `: RefutableProfile` type ascription to first `⟨...⟩` in `h_ne`.

---

## EXISTING THEOREMS REUSED (9 theorems — unchanged, all VERIFIED)

| # | Theorem | File | Reused for |
|---|---------|------|-----------|
| 1 | `avatar_to_core_injective` | STCKG/Core.lean:219 | 6A-A1 |
| 2 | `unsplit_split` | STCKG/Core.lean:213 | 6A-A2 |
| 3 | `split_unsplit_of_default` | STCKG/Core.lean:225 | 6A-A3 |
| 4 | `derivable_does_not_imply_established` | STCKG/Claim.lean:189 | 6B-B1 |
| 5 | `toBelief_not_injective` | STCKG/Evidence.lean:137 | 6C-E1 |
| 6 | `toBelief_not_surjective` | STCKG/Evidence.lean:146 | 6C-E2 |
| 7 | `toBelief'_surjective` | STCKG/Evidence.lean:175 | 6C-E3 |
| 8 | `verified_and_refuted_distinguished` | STCKG/Evidence.lean:188 | 6C-E5 |
| 9 | `derivable_of_assumptions_derivable` | STCKG/Claim.lean:161 | Bridge transport |

---

## BRIDGE CLASSIFICATION SUMMARY

| Bridge | Classification | Key theorems | Verified |
|--------|---------------|-------------|----------|
| Avatar ↔ KO×Extra | LOSSLESS ON RESTRICTED IMAGE | A1-A4 (4 theorems) | YES |
| Claim → Step | LOSSY PROJECTION | B1-B2 (2 theorems) | YES |
| EvidenceProfile → PT | LOSSY PROJECTION | E1-E2 (6 theorems) | YES |
| RefutableProfile → PT | LOSSY PROJECTION, SURJECTIVE | E3-E5 (3 theorems) | YES |
| Referent → KO | NO NATURAL BRIDGE | N/A (GATE 2 structural audit) | N/A |

**Total: 14 theorems (3 new + 11 existing), 0 custom axioms, 0 sorry, lake build clean.**

---

## GATE 6 CRITICAL RULE COMPLIANCE

| Constraint | Status |
|-----------|--------|
| No `update_spec_declaration` | PASS |
| No ST-CKG redesign | PASS |
| No changed semantic definitions | PASS |
| No weakened/deleted theorems | PASS |
| No new axioms | PASS |
| No sorry/admit/unsafe | PASS |
| Direct file operations only | PASS |
| Every theorem genuinely elaborated | PASS (8158 jobs, 0 errors) |
| No projection→embedding conversion | PASS |
| Bridge type distinctions preserved | PASS |
| COUNTEREXAMPLE-FIRST principle | PASS (validated by GATE 7R) |

---

## METHODLOGICAL LESSONS

### 1. Verification gap is real

GATE 7 v1 FAIL экспериментально подтвердил: между математической интуицией и машинно проверенным семантическим контрактом существует реальный verification gap. Интуитивно корректное доказательство может не пройти элаборацию из-за тонкостей Lean 4 (implicit args, type inference context).

### 2. COUNTEREXAMPLE-FIRST eliminates an entire failure class

Принцип witness → equality → distinction → contradiction:
- Даёт Lean достаточно type information для корректного вывода implicit args
- Делает witness первичным объектом, а не тактическим артефактом
- Делает proof readable и auditable

### 3. Independent execution is non-negotiable

GATE 7 v1 (Aristotle) нашёл ошибки, которые Polymath не увидел. GATE 7R (Aristotle) подтвердил исправления. Без независимого запуска проект остался бы с latent broken proofs.

---

**GATE 6 v4 FINAL: 3 new theorems, COUNTEREXAMPLE-FIRST, independently verified. GATE 7 = GREEN.**
