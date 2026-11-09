import RequestProject.UAM_MyhillNerode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# State complexity of the boolean operations

`UAM.StateComplexity.AcceptedBy L n` says that some deterministic automaton with
at most `n` states accepts `L`.  The boolean operations are then bounded by the
usual product constructions:

* `AcceptedBy.compl` — complement costs nothing;
* `AcceptedBy.inf`, `AcceptedBy.sup` — intersection and union cost at most `m*n`;
* `nerode_le_of_acceptedBy` — the matching lower bound: the number of Nerode
  classes of `L` never exceeds the number of states of any automaton for `L`, so
  a language with more than `n` Nerode classes is not accepted by any `n`-state
  automaton (`not_acceptedBy_of_lt_nerode`).
-/

namespace UAM.StateComplexity

open UAM.MyhillNerode

universe u

variable {α : Type u}

/-- `L` is accepted by a deterministic automaton with at most `n` states. -/
def AcceptedBy (L : Language α) (n : ℕ) : Prop :=
  ∃ (σ : Type u) (_ : Fintype σ) (M : DFA α σ), M.accepts = L ∧ Nat.card σ ≤ n

theorem AcceptedBy.isRegular {L : Language α} {n : ℕ} (h : AcceptedBy L n) : L.IsRegular := by
  obtain ⟨σ, hσ, M, hM, -⟩ := h
  exact Language.isRegular_iff.2 ⟨σ, hσ, M, hM⟩

/-- Complementation does not change the number of states. -/
theorem AcceptedBy.compl {L : Language α} {n : ℕ} (h : AcceptedBy L n) :
    AcceptedBy Lᶜ n := by
  obtain ⟨σ, hσ, M, hM, hcard⟩ := h
  exact ⟨σ, hσ, Mᶜ, by simp [hM], hcard⟩

/-- The product automaton accepts the intersection with at most `m * n` states. -/
theorem AcceptedBy.inf {L M : Language α} {m n : ℕ}
    (hL : AcceptedBy L m) (hM : AcceptedBy M n) : AcceptedBy (L ⊓ M) (m * n) := by
  obtain ⟨σ, hσ, A, hA, hcA⟩ := hL
  obtain ⟨τ, hτ, B, hB, hcB⟩ := hM
  refine ⟨σ × τ, inferInstance, A.inter B, by simp [hA, hB], ?_⟩
  have : Nat.card (σ × τ) = Nat.card σ * Nat.card τ := Nat.card_prod σ τ
  rw [this]
  exact Nat.mul_le_mul hcA hcB

/-- The product automaton accepts the union with at most `m * n` states. -/
theorem AcceptedBy.sup {L M : Language α} {m n : ℕ}
    (hL : AcceptedBy L m) (hM : AcceptedBy M n) : AcceptedBy (L ⊔ M) (m * n) := by
  obtain ⟨σ, hσ, A, hA, hcA⟩ := hL
  obtain ⟨τ, hτ, B, hB, hcB⟩ := hM
  refine ⟨σ × τ, inferInstance, A.union B, ?_, ?_⟩
  · rw [DFA.accepts_union, hA, hB]
    rfl
  · rw [Nat.card_prod]
    exact Nat.mul_le_mul hcA hcB

/-- **Lower bound.**  Any automaton for `L` has at least as many states as `L`
has Nerode classes. -/
theorem nerode_le_of_acceptedBy {L : Language α} {n : ℕ} (h : AcceptedBy L n) :
    Nat.card (NerodeClasses L) ≤ n := by
  obtain ⟨σ, hσ, M, hM, hcard⟩ := h
  subst hM
  have := card_nerodeClasses_le_card_states M
  rw [Nat.card_eq_fintype_card (α := σ)] at hcard
  exact le_trans this hcard

/-- A language with more Nerode classes than `n` is not accepted by any
automaton with `n` states. -/
theorem not_acceptedBy_of_lt_nerode {L : Language α} {n : ℕ}
    (h : n < Nat.card (NerodeClasses L)) : ¬ AcceptedBy L n :=
  fun hacc => absurd (nerode_le_of_acceptedBy hacc) (not_le.2 h)

/-- The Nerode quotient itself realises the optimum: a regular language is
accepted by an automaton with exactly its number of Nerode classes. -/
theorem acceptedBy_nerode {L : Language α} (h : L.IsRegular) :
    AcceptedBy L (Nat.card (NerodeClasses L)) := by
  classical
  have hfin : Finite (Set.range L.leftQuotient) :=
    Set.Finite.to_subtype (Language.IsRegular.finite_range_leftQuotient h)
  have hcard : Nat.card (Set.range L.leftQuotient) = Nat.card (NerodeClasses L) :=
    Nat.card_congr (nerodeClassesEquivLeftQuotients L).symm
  exact ⟨Set.range L.leftQuotient, Fintype.ofFinite _, nerodeDFA L, nerodeDFA_accepts L,
    le_of_eq hcard⟩

end UAM.StateComplexity
