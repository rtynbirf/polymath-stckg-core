import RequestProject.Bridges.RegularContextFree
import RequestProject.Atlas.UAM_NFA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: right-linear grammars generate exactly the regular languages

`Bridges.RegularContextFree` turns a deterministic automaton into a right-linear
grammar.  This module proves the converse: a grammar all of whose rules are
right-linear (`A → ε` or `A → a B`) and which has finitely many nonterminals
generates a regular language.

The construction is the obvious one: the nonterminals become the states of a
nondeterministic automaton, a rule `A → a B` becomes a transition and a rule
`A → ε` marks `A` accepting.  `yields_iff_acceptsFrom` is the key
correspondence, proved by induction on the word.

Combining the two directions gives `isRegular_iff_exists_rightLinear`: a
language is regular exactly when some finite right-linear grammar generates it.
-/

namespace UAM.ContextFree

variable {N T : Type}

/-! ## Right-linear grammars -/

/-- A grammar is *right-linear* when every rule is of the form `A → ε` or
`A → a B`. -/
def RightLinear (g : Grammar N T) : Prop :=
  ∀ A β, g.rule A β → β = [] ∨ ∃ (a : T) (B : N), β = [Sum.inr a, Sum.inl B]

/-- The grammar built from a deterministic automaton is right-linear. -/
theorem rightLinear_ofDFA {σ α : Type} (M : DFA α σ) : RightLinear (ofDFA M) := by
  rintro q β (⟨rfl, -⟩ | ⟨a, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨a, M.step q a, rfl⟩

/-! ## The automaton of a right-linear grammar -/

/-- The nondeterministic automaton of a right-linear grammar: states are
nonterminals, `A → a B` is a transition and `A → ε` makes `A` accepting. -/
def nfaOf (g : Grammar N T) : NFA T N where
  step A a := {B | g.rule A [Sum.inr a, Sum.inl B]}
  start := {g.start}
  accept := {A | g.rule A []}

@[simp] theorem mem_nfaOf_step {g : Grammar N T} {A B : N} {a : T} :
    B ∈ (nfaOf g).step A a ↔ g.rule A [Sum.inr a, Sum.inl B] := Iff.rfl

@[simp] theorem mem_nfaOf_accept {g : Grammar N T} {A : N} :
    A ∈ (nfaOf g).accept ↔ g.rule A [] := Iff.rfl

/-- A right-linear derivation from `A` cannot produce a word from the empty
right-hand side unless the word is empty. -/
theorem yields_nil_iff_rule_nil {g : Grammar N T} (hg : RightLinear g) (A : N) :
    Yields g [Sum.inl A] [] ↔ g.rule A [] := by
  constructor
  · intro h
    obtain ⟨β, hr, hβ⟩ := yields_singleton_inv h
    rcases hg A β hr with rfl | ⟨a, B, rfl⟩
    · exact hr
    · cases hβ
  · intro hr
    have := Yields.nonterm hr (Yields.nil (g := g)) (Yields.nil (g := g))
    simpa using this

/-- One step of a right-linear derivation. -/
theorem yields_cons_iff {g : Grammar N T} (hg : RightLinear g) (A : N) (a : T) (w : List T) :
    Yields g [Sum.inl A] (a :: w) ↔
      ∃ B, g.rule A [Sum.inr a, Sum.inl B] ∧ Yields g [Sum.inl B] w := by
  constructor
  · intro h
    obtain ⟨β, hr, hβ⟩ := yields_singleton_inv h
    rcases hg A β hr with rfl | ⟨b, B, rfl⟩
    · cases hβ
    · cases hβ with
      | term hrest =>
        refine ⟨B, hr, ?_⟩
        simpa using hrest
  · rintro ⟨B, hr, hB⟩
    have hβ : Yields g [Sum.inr a, Sum.inl B] (a :: w) := Yields.term (by simpa using hB)
    have := Yields.nonterm hr hβ (Yields.nil (g := g))
    simpa using this

/-- **The key correspondence.**  A right-linear grammar derives `w` from `A`
exactly when its automaton accepts `w` starting at `A`. -/
theorem yields_iff_acceptsFrom {g : Grammar N T} (hg : RightLinear g) (A : N) (w : List T) :
    Yields g [Sum.inl A] w ↔ w ∈ (nfaOf g).acceptsFrom {A} := by
  induction w generalizing A with
  | nil =>
    rw [yields_nil_iff_rule_nil hg, NFA.mem_acceptsFrom, NFA.evalFrom_nil]
    constructor
    · intro h; exact ⟨A, h, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact hs
  | cons a w ih =>
    rw [yields_cons_iff hg, NFA.mem_acceptsFrom, NFA.evalFrom_cons]
    constructor
    · rintro ⟨B, hr, hB⟩
      obtain ⟨s, hs, hsB⟩ := (NFA.mem_acceptsFrom).1 ((ih B).1 hB)
      refine ⟨s, hs, ?_⟩
      rw [NFA.mem_evalFrom_iff_exists]
      exact ⟨B, NFA.mem_stepSet.2 ⟨A, rfl, hr⟩, hsB⟩
    · rintro ⟨s, hs, hsw⟩
      rw [NFA.mem_evalFrom_iff_exists] at hsw
      obtain ⟨B, hB, hsB⟩ := hsw
      obtain ⟨A', hA', hr⟩ := NFA.mem_stepSet.1 hB
      cases hA'
      exact ⟨B, hr, (ih B).2 ((NFA.mem_acceptsFrom).2 ⟨s, hs, hsB⟩)⟩

/-- The automaton of a right-linear grammar accepts exactly its language. -/
theorem nfaOf_accepts {g : Grammar N T} (hg : RightLinear g) :
    (nfaOf g).accepts = g.language := by
  ext w
  rw [NFA.mem_accepts]
  refine Iff.trans ?_ (yields_iff_acceptsFrom hg g.start w).symm
  rw [NFA.mem_acceptsFrom]
  rfl

/-- **A finite right-linear grammar generates a regular language.** -/
theorem isRegular_of_rightLinear [Fintype N] {g : Grammar N T} (hg : RightLinear g) :
    Language.IsRegular (T := T) g.language :=
  UAM.NFA.isRegular_of_isNFARegular ⟨N, inferInstance, nfaOf g, nfaOf_accepts hg⟩

/-- **Right-linear grammars characterise the regular languages.** -/
theorem isRegular_iff_exists_rightLinear (L : Language T) :
    L.IsRegular ↔
      ∃ (N : Type) (_ : Fintype N) (g : Grammar N T), RightLinear g ∧ g.language = L := by
  constructor
  · rintro ⟨σ, hσ, M, rfl⟩
    exact ⟨σ, hσ, ofDFA M, rightLinear_ofDFA M, dfa_language_eq_grammar_language M⟩
  · rintro ⟨N, hN, g, hg, rfl⟩
    exact isRegular_of_rightLinear hg

end UAM.ContextFree
