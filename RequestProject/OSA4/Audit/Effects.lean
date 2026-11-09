import RequestProject.OSA4.Effects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Audit: the effect algebra

The five effect levels form a linear order, and aggregation computes the least
upper bound of a list of effects.  This module verifies that reading:

* `aggregate_le_iff` and `le_aggregate_of_mem` — aggregation is the supremum;
* `aggregate_eq_of_perm` — the aggregate does not depend on the order of the
  list, nor on repetitions (`aggregate_cons_self`);
* `effectLevel_card` and `effectLevel_chain` — the level scale is a five-element
  chain.
-/

namespace Polymath.OSA4.Audit

open Polymath.OSA4

theorem aggregate_le_iff (l : List EffectLevel) (b : EffectLevel) :
    aggregate l ≤ b ↔ ∀ e ∈ l, e ≤ b := by
  induction l with
  | nil => simp [aggregate, EffectLevel.E0_le b]
  | cons e t ih =>
      simp only [aggregate, EffectLevel.join, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

theorem le_aggregate_of_mem {l : List EffectLevel} {e : EffectLevel} (he : e ∈ l) :
    e ≤ aggregate l := aggregate_le_of_mem he

/-- Aggregation only depends on the set of effects that occur. -/
theorem aggregate_eq_of_mem_iff {l l' : List EffectLevel} (h : ∀ e, e ∈ l ↔ e ∈ l') :
    aggregate l = aggregate l' := by
  refine le_antisymm ?_ ?_
  · exact (aggregate_le_iff l _).2 fun e he => le_aggregate_of_mem ((h e).1 he)
  · exact (aggregate_le_iff l' _).2 fun e he => le_aggregate_of_mem ((h e).2 he)

theorem aggregate_eq_of_perm {l l' : List EffectLevel} (h : l.Perm l') :
    aggregate l = aggregate l' := aggregate_eq_of_mem_iff fun _ => h.mem_iff

theorem aggregate_cons_self (e : EffectLevel) (l : List EffectLevel) :
    aggregate (e :: e :: l) = aggregate (e :: l) :=
  aggregate_eq_of_mem_iff (by intro x; simp)

theorem effectLevel_card : Fintype.card EffectLevel = 5 := by decide

/-- The five levels form a strictly increasing chain. -/
theorem effectLevel_chain :
    EffectLevel.E0 < EffectLevel.E1 ∧ EffectLevel.E1 < EffectLevel.E2 ∧
    EffectLevel.E2 < EffectLevel.E3 ∧ EffectLevel.E3 < EffectLevel.E4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `E4` is the top of the scale. -/
theorem le_E4 (a : EffectLevel) : a ≤ EffectLevel.E4 := by
  cases a <;> decide

/-- The audit of the effect algebra. -/
theorem effects_audit :
    (∀ l₁ l₂ : List EffectLevel,
        aggregate (l₁ ++ l₂) = EffectLevel.join (aggregate l₁) (aggregate l₂)) ∧
    (∀ (l : List EffectLevel) (b : EffectLevel), aggregate l ≤ b ↔ ∀ e ∈ l, e ≤ b) ∧
    (∀ ops : List Op, WithinBudget EffectLevel.E4 ops) :=
  ⟨law008_aggregate_append, aggregate_le_iff, withinBudget_E4⟩

end Polymath.OSA4.Audit
