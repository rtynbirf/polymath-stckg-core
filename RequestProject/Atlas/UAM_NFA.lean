import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Nondeterministic automata and the subset construction

Regularity was defined by deterministic automata.  This module records that
nondeterminism — with or without ε-moves — does not change the class of
languages accepted:

* `UAM.NFA.isRegular_iff_isNFARegular` — a language is regular iff some finite
  nondeterministic automaton accepts it;
* `UAM.NFA.isRegular_iff_isEpsilonRegular` — the same for automata with ε-moves;
* `UAM.NFA.exists_dfa_card_le_two_pow` — the subset construction is quantitative:
  an `n`-state nondeterministic automaton is determinized into an automaton with
  at most `2 ^ n` states.
-/

namespace UAM.NFA

universe u

variable {α : Type u}

/-! ## Nondeterministic acceptance -/

/-- `L` is accepted by some finite nondeterministic automaton. -/
def IsNFARegular (L : Language α) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : NFA α σ), M.accepts = L

/-- `L` is accepted by some finite nondeterministic automaton with ε-moves. -/
def IsEpsilonRegular (L : Language α) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (M : εNFA α σ), M.accepts = L

/-- A deterministic automaton is a special nondeterministic one. -/
theorem isNFARegular_of_isRegular {L : Language α} (h : L.IsRegular) : IsNFARegular L := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  exact ⟨σ, hσ, M.toNFA, DFA.toNFA_correct M⟩

/-- The subset construction turns a nondeterministic automaton into a
deterministic one. -/
theorem isRegular_of_isNFARegular {L : Language α} (h : IsNFARegular L) : L.IsRegular := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  classical
  exact ⟨Set σ, inferInstance, M.toDFA, M.toDFA_correct⟩

/-- **Nondeterminism does not add power.** -/
theorem isRegular_iff_isNFARegular (L : Language α) : L.IsRegular ↔ IsNFARegular L :=
  ⟨isNFARegular_of_isRegular, isRegular_of_isNFARegular⟩

/-- An ε-free nondeterministic automaton is a special automaton with ε-moves. -/
theorem isEpsilonRegular_of_isNFARegular {L : Language α} (h : IsNFARegular L) :
    IsEpsilonRegular L := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  exact ⟨σ, hσ, M.toεNFA, NFA.toεNFA_correct M⟩

/-- ε-moves can be eliminated. -/
theorem isNFARegular_of_isEpsilonRegular {L : Language α} (h : IsEpsilonRegular L) :
    IsNFARegular L := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  exact ⟨σ, hσ, M.toNFA, M.toNFA_correct⟩

/-- **ε-moves do not add power.** -/
theorem isRegular_iff_isEpsilonRegular (L : Language α) : L.IsRegular ↔ IsEpsilonRegular L :=
  ⟨fun h => isEpsilonRegular_of_isNFARegular (isNFARegular_of_isRegular h),
    fun h => isRegular_of_isNFARegular (isNFARegular_of_isEpsilonRegular h)⟩

/-- All three notions of acceptance coincide. -/
theorem regular_nfa_epsilon_equiv (L : Language α) :
    (L.IsRegular ↔ IsNFARegular L) ∧ (IsNFARegular L ↔ IsEpsilonRegular L) :=
  ⟨isRegular_iff_isNFARegular L,
    ⟨isEpsilonRegular_of_isNFARegular, isNFARegular_of_isEpsilonRegular⟩⟩

/-! ## State complexity of determinization -/

/-- **The subset construction costs at most an exponential.**  A language
accepted by an `n`-state nondeterministic automaton is accepted by a
deterministic automaton with at most `2 ^ n` states. -/
theorem exists_dfa_card_le_two_pow {σ : Type} [Fintype σ] (M : NFA α σ) :
    ∃ (τ : Type) (hτ : Fintype τ) (D : DFA α τ),
      D.accepts = M.accepts ∧ @Fintype.card τ hτ ≤ 2 ^ Fintype.card σ := by
  classical
  refine ⟨Set σ, inferInstance, M.toDFA, M.toDFA_correct, ?_⟩
  simp [Fintype.card_set (α := σ)]

end UAM.NFA
