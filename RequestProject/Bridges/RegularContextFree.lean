import RequestProject.UAM_ContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: regular languages are context-free

A deterministic finite automaton is turned into a right-linear grammar whose
nonterminals are the states.  `yields_ofDFA_iff` shows the grammar derives
exactly the words the automaton accepts from a given state, so every regular
language is context-free and, via `contextFree_iff_pda`, is accepted by a
pushdown automaton.
-/

namespace UAM.ContextFree

universe u

variable {α σ : Type u}

/-- The right-linear grammar of a DFA: a state either accepts and halts, or
reads a letter and moves on. -/
def ofDFA (M : DFA α σ) : Grammar σ α where
  rule q β := (β = [] ∧ q ∈ M.accept) ∨ (∃ a : α, β = [Sum.inr a, Sum.inl (M.step q a)])
  start := M.start

/-- The grammar of a DFA derives exactly the words accepted from a state. -/
theorem yields_ofDFA_iff (M : DFA α σ) (q : σ) (w : List α) :
    Yields (ofDFA M) [Sum.inl q] w ↔ M.evalFrom q w ∈ M.accept := by
  induction w generalizing q with
  | nil =>
    constructor
    · intro h
      obtain ⟨β, hr, hβ⟩ := yields_singleton_inv h
      rcases hr with ⟨-, hacc⟩ | ⟨a, rfl⟩
      · simpa using hacc
      · cases hβ
    · intro h
      have hrule : (ofDFA M).rule q [] := Or.inl ⟨rfl, by simpa using h⟩
      have := Yields.nonterm hrule (Yields.nil (g := ofDFA M)) (Yields.nil (g := ofDFA M))
      simpa using this
  | cons a w ih =>
    rw [DFA.evalFrom_cons, ← ih (M.step q a)]
    constructor
    · intro h
      obtain ⟨β, hr, hβ⟩ := yields_singleton_inv h
      rcases hr with ⟨rfl, -⟩ | ⟨b, rfl⟩
      · cases hβ
      · cases hβ with
        | term hrest => exact hrest
    · intro h
      have hrule : (ofDFA M).rule q [Sum.inr a, Sum.inl (M.step q a)] := Or.inr ⟨a, rfl⟩
      have hβ : Yields (ofDFA M) [Sum.inr a, Sum.inl (M.step q a)] (a :: w) :=
        Yields.term h
      have := Yields.nonterm hrule hβ (Yields.nil (g := ofDFA M))
      simpa using this

/-- The grammar of a DFA generates exactly the language of the DFA. -/
theorem dfa_language_eq_grammar_language (M : DFA α σ) :
    (ofDFA M).language = M.accepts := by
  ext w
  rw [DFA.mem_accepts]
  exact yields_ofDFA_iff M M.start w

/-- Every regular language is context-free. -/
theorem regular_subset_contextFree (M : DFA α σ) :
    ∃ (N : Type u) (g : Grammar N α), g.language = M.accepts :=
  ⟨σ, ofDFA M, dfa_language_eq_grammar_language M⟩

/-- Every regular language is accepted by a pushdown automaton. -/
theorem regular_subset_pda (M : DFA α σ) :
    ∃ (Γ : Type u) (P : PDA Γ α), P.language = M.accepts :=
  (contextFree_iff_pda (M.accepts : Set (List α))).1 (regular_subset_contextFree M)

end UAM.ContextFree
