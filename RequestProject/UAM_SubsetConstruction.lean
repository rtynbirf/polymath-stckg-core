import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The subset construction: nondeterminism does not add power

This module records the determinization layer of the automata tower.  We define
what it means for a language to be recognized by a finite nondeterministic
automaton (`IsNFARecognizable`) or by one with silent transitions
(`IsEpsNFARecognizable`), and prove that both notions coincide with regularity:

* `isRegular_iff_isNFARecognizable`;
* `isRegular_iff_isEpsNFARecognizable`.

The quantitative content of the subset construction is isolated in
`exists_dfa_card_le_two_pow`: an `n`-state nondeterministic automaton can be
replaced by a deterministic one with at most `2 ^ n` states.
-/

namespace UAM.SubsetConstruction

universe u

variable {α : Type u}

/-- A language is *NFA-recognizable* when some nondeterministic automaton with a
finite state space accepts exactly it. -/
def IsNFARecognizable (L : Language α) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : NFA α σ, M.accepts = L

/-- A language is *ε-NFA-recognizable* when some nondeterministic automaton with
silent transitions and a finite state space accepts exactly it. -/
def IsEpsNFARecognizable (L : Language α) : Prop :=
  ∃ σ : Type, ∃ _ : Fintype σ, ∃ M : εNFA α σ, M.accepts = L

/-! ## Determinization -/

/-- The subset construction turns an NFA into a DFA accepting the same language. -/
theorem toDFA_accepts {σ : Type} (M : NFA α σ) : M.toDFA.accepts = M.accepts :=
  M.toDFA_correct

/-- The state space of the subset construction has exactly `2 ^ n` elements. -/
theorem card_powerset_states (σ : Type) [Fintype σ] :
    Fintype.card (Set σ) = 2 ^ Fintype.card σ := by
  classical
  exact Fintype.card_set

/-- Quantitative subset construction: an `n`-state NFA is equivalent to a DFA
with at most `2 ^ n` states. -/
theorem exists_dfa_card_le_two_pow {σ : Type} [Fintype σ] (M : NFA α σ) :
    ∃ (τ : Type) (_ : Fintype τ) (D : DFA α τ),
      D.accepts = M.accepts ∧ Fintype.card τ ≤ 2 ^ Fintype.card σ := by
  classical
  exact ⟨Set σ, inferInstance, M.toDFA, M.toDFA_correct,
    le_of_eq (card_powerset_states σ)⟩

/-! ## Recognizability coincides with regularity -/

theorem isRegular_of_isNFARecognizable {L : Language α} (h : IsNFARecognizable L) :
    L.IsRegular := by
  classical
  obtain ⟨σ, _, M, hM⟩ := h
  exact ⟨Set σ, inferInstance, M.toDFA, by rw [M.toDFA_correct, hM]⟩

theorem isNFARecognizable_of_isRegular {L : Language α} (h : L.IsRegular) :
    IsNFARecognizable L := by
  obtain ⟨σ, _, M, hM⟩ := h
  exact ⟨σ, inferInstance, M.toNFA, by rw [DFA.toNFA_correct, hM]⟩

/-- Nondeterminism does not extend the class of languages recognized by finite
automata. -/
theorem isRegular_iff_isNFARecognizable {L : Language α} :
    L.IsRegular ↔ IsNFARecognizable L :=
  ⟨isNFARecognizable_of_isRegular, isRegular_of_isNFARecognizable⟩

theorem isEpsNFARecognizable_of_isNFARecognizable {L : Language α}
    (h : IsNFARecognizable L) : IsEpsNFARecognizable L := by
  obtain ⟨σ, _, M, hM⟩ := h
  exact ⟨σ, inferInstance, M.toεNFA, by rw [NFA.toεNFA_correct, hM]⟩

theorem isNFARecognizable_of_isEpsNFARecognizable {L : Language α}
    (h : IsEpsNFARecognizable L) : IsNFARecognizable L := by
  obtain ⟨σ, _, M, hM⟩ := h
  exact ⟨σ, inferInstance, M.toNFA, by rw [εNFA.toNFA_correct, hM]⟩

/-- Silent transitions do not extend the class of languages recognized by finite
automata either. -/
theorem isRegular_iff_isEpsNFARecognizable {L : Language α} :
    L.IsRegular ↔ IsEpsNFARecognizable L :=
  ⟨fun h => isEpsNFARecognizable_of_isNFARecognizable
      (isNFARecognizable_of_isRegular h),
   fun h => isRegular_of_isNFARecognizable (isNFARecognizable_of_isEpsNFARecognizable h)⟩

/-- The three recognizability notions agree. -/
theorem regular_nfa_epsNFA_equiv {L : Language α} :
    (L.IsRegular ↔ IsNFARecognizable L) ∧ (IsNFARecognizable L ↔ IsEpsNFARecognizable L) :=
  ⟨isRegular_iff_isNFARecognizable,
   ⟨isEpsNFARecognizable_of_isNFARecognizable, isNFARecognizable_of_isEpsNFARecognizable⟩⟩

end UAM.SubsetConstruction
