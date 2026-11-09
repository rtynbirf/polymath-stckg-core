import RequestProject.STCKG.Claim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Composition: lazy closure and the confidence heuristic

This file settles §26 of the directive.

* **Lazy composition is enough.**  The derived relation is the transitive
  closure of the stored one; materialising composites and closing again produces
  nothing new (`transGen_idempotent`, `materialize_sound`,
  `materialize_complete`).  Materialisation is therefore an engineering
  optimisation, never a semantic act.
* **`confidence (g ∘ f) = min (conf f) (conf g)` is a heuristic, not a law.**
  `composeConfidence` is commutative, associative and idempotent
  (so it is a well-behaved aggregation), and it agrees with the existing
  `Polymath.chainConfidence` on non-empty chains (`chainConfidence_cons_eq`).
  But `confidence_does_not_determine_derivability` shows that two claims with
  *identical* evidence can differ in derivability, so the number carries no
  epistemic force: `STATUS = HEURISTIC`, engineering layer.
-/

namespace Polymath.STCKG

open Polymath Polymath.ProofGraph

/-! ## Lazy composition -/

/-- The derived (composed) relation: the transitive closure of the stored one. -/
def derived {α : Type _} (R : α → α → Prop) : α → α → Prop := Relation.TransGen R

/-- Materialising a composite edge and then closing again changes nothing. -/
theorem transGen_idempotent {α : Type _} (R : α → α → Prop) :
    derived (derived R) = derived R :=
  Relation.transGen_idem

/-- Every materialised composite was already derivable. -/
theorem materialize_sound {α : Type _} {R : α → α → Prop} {a b c : α}
    (hab : derived R a b) (hbc : derived R b c) : derived R a c := hab.trans hbc

/-- Conversely, every derived edge is a finite composition of stored ones, so
lazy evaluation loses nothing. -/
theorem materialize_complete {α : Type _} {R : α → α → Prop} {a c : α}
    (h : derived R a c) : R a c ∨ ∃ b, derived R a b ∧ R b c := by
  cases h with
  | single hac => exact Or.inl hac
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-! ## The confidence heuristic -/

/-- Composition of confidences: the weakest link.  Engineering heuristic. -/
def composeConfidence (a b : ℤ) : ℤ := min a b

theorem composeConfidence_comm (a b : ℤ) : composeConfidence a b = composeConfidence b a :=
  min_comm a b

theorem composeConfidence_assoc (a b c : ℤ) :
    composeConfidence (composeConfidence a b) c = composeConfidence a (composeConfidence b c) :=
  min_assoc a b c

theorem composeConfidence_idem (a : ℤ) : composeConfidence a a = a := min_self a

theorem composeConfidence_le_left (a b : ℤ) : composeConfidence a b ≤ a := min_le_left a b

/-- The heuristic agrees with the existing `chainConfidence` of `Core.lean`. -/
theorem chainConfidence_cons_eq (c : ℤ) (t : List ℤ) :
    chainConfidence (c :: t) = composeConfidence c (chainConfidence t) := rfl

/-- Everything derivable is either assumed or is the conclusion of a step. -/
theorem derivable_assumed_or_concluded {P : Proofs} {x : ℕ} (h : Derivable P x) :
    x ∈ P.assumptions ∨ ∃ s ∈ P.steps, s.conclusion = x := by
  cases h with
  | assumption hn => exact Or.inl hn
  | infer hs _ => exact Or.inr ⟨_, hs, rfl⟩

/-- **The heuristic is not epistemic.**  Two claims with exactly the same
evidence profile — hence the same confidence, however it is computed from the
profile — can differ in whether they are derivable in the claim graph. -/
theorem confidence_does_not_determine_derivability :
    ∃ (base : Finset ℕ) (cs : List Claim) (c d : Claim),
      c.evidence = d.evidence ∧
      Derivable (toProofs base cs) c.id ∧ ¬ Derivable (toProofs base cs) d.id := by
  refine ⟨∅, [claimA], claimA, claimB, rfl, derivable_of_no_assumptions (by simp) rfl, ?_⟩
  intro h
  rcases derivable_assumed_or_concluded h with hn | ⟨s, hs, hconc⟩
  · simp [toProofs] at hn
  · have hs' : s = claimA.toStep := by simpa [toProofs] using hs
    rw [hs'] at hconc
    exact absurd hconc (by decide)

/-- Any scalar summary of evidence is therefore confined to the engineering
layer: it can order claims, but an ordering never justifies a derivation. -/
theorem confidence_order_is_not_justification (f : EvidenceProfile → ℤ) :
    ∃ (base : Finset ℕ) (cs : List Claim) (c d : Claim),
      f c.evidence = f d.evidence ∧
      Derivable (toProofs base cs) c.id ∧ ¬ Derivable (toProofs base cs) d.id := by
  obtain ⟨base, cs, c, d, hev, h₁, h₂⟩ := confidence_does_not_determine_derivability
  exact ⟨base, cs, c, d, by rw [hev], h₁, h₂⟩

end Polymath.STCKG
