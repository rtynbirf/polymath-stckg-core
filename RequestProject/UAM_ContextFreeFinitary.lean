import RequestProject.UAM_ContextFreeClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Finitary grammars and the honest class of context-free languages

A `Grammar N T` carries an arbitrary *relation* `rule : N → List (N ⊕ T) → Prop`,
so it may have infinitely many productions.  This makes the naive predicate
`IsContextFree L := ∃ N g, g.language = L` degenerate: `isContextFree_trivial`
below shows that **every** language over `T` satisfies it — one nonterminal with
one production `S → w` for each word `w ∈ L` already generates `L`.  The closure
theorems stated for that predicate are therefore true but empty.

This module repairs the definition.  A grammar is *finitary* when its set of
productions is finite, and

  `IsCFL L := ∃ N (g : Grammar N T), g.Finitary ∧ g.language = L`

is the honest notion.  We reprove the closure properties for it — union,
concatenation, Kleene star, reversal — by checking that the grammar
constructions of `UAM_ContextFreeClosure` preserve finiteness, and we show that
every regular language over a finite alphabet is context-free in this sense.
-/

namespace UAM.ContextFree

universe u

variable {N T : Type u}

/-! ## Finitary grammars -/

/-- The set of productions of a grammar. -/
def Grammar.rules (g : Grammar N T) : Set (N × List (N ⊕ T)) := {p | g.rule p.1 p.2}

@[simp] theorem Grammar.mem_rules {g : Grammar N T} {A : N} {β : List (N ⊕ T)} :
    (A, β) ∈ g.rules ↔ g.rule A β := Iff.rfl

/-- A grammar is *finitary* when it has only finitely many productions. -/
def Grammar.Finitary (g : Grammar N T) : Prop := g.rules.Finite

/-- A language is context-free when some finitary grammar generates it. -/
def IsCFL (L : Language T) : Prop :=
  ∃ (N : Type u) (g : Grammar N T), g.Finitary ∧ g.language = L

theorem IsCFL.isContextFree {L : Language T} (h : IsCFL L) : IsContextFree L := by
  obtain ⟨N, g, -, hL⟩ := h
  exact ⟨N, g, hL⟩

/-! ## The naive predicate is vacuous -/

/-- A sentential form containing only terminals derives exactly itself. -/
theorem yields_map_inr_iff (g : Grammar N T) (v w : List T) :
    Yields g (v.map Sum.inr) w ↔ w = v := by
  induction v generalizing w with
  | nil =>
    simp only [List.map_nil]
    exact ⟨fun h => h.eq_nil_of_nil, fun h => by subst h; exact Yields.nil⟩
  | cons a v ih =>
    simp only [List.map_cons]
    constructor
    · intro h
      cases h with
      | term hrest => rw [(ih _).1 hrest]
    · rintro rfl
      exact Yields.term ((ih v).2 rfl)

/-- The one-nonterminal grammar with a production `S → w` for each word of `L`.
It has infinitely many productions as soon as `L` is infinite. -/
def wordGrammar (L : Language T) : Grammar PUnit.{u + 1} T where
  rule _ β := ∃ w ∈ L, β = w.map Sum.inr
  start := PUnit.unit

@[simp] theorem wordGrammar_language (L : Language T) : (wordGrammar L).language = L := by
  ext w
  constructor
  · intro hw
    obtain ⟨β, ⟨v, hv, rfl⟩, hβ⟩ := yields_singleton_inv hw
    rw [(yields_map_inr_iff _ v w).1 hβ]
    exact hv
  · intro hw
    have hr : (wordGrammar L).rule PUnit.unit (w.map Sum.inr) := ⟨w, hw, rfl⟩
    have hβ : Yields (wordGrammar L) (w.map Sum.inr) w := (yields_map_inr_iff _ w w).2 rfl
    have := Yields.nonterm (α := []) hr hβ Yields.nil
    simpa using this

/-- **The naive predicate `IsContextFree` is vacuous**: every language is
"context-free" once grammars may have infinitely many productions. -/
theorem isContextFree_trivial (L : Language T) : IsContextFree L :=
  ⟨PUnit.{u + 1}, wordGrammar L, wordGrammar_language L⟩

/-! ## Finiteness of the closure constructions -/

section Binary

variable {N₁ N₂ : Type u}

theorem finitary_unionGrammar {g₁ : Grammar N₁ T} {g₂ : Grammar N₂ T}
    (h₁ : g₁.Finitary) (h₂ : g₂.Finitary) : (unionGrammar g₁ g₂).Finitary := by
  refine Set.Finite.subset
    (((h₁.image (fun p => (inl₂ (N₂ := N₂) p.1, relabel (inl₂ (N₂ := N₂)) p.2))).union
        (h₂.image (fun p => (inr₂ (N₁ := N₁) p.1, relabel (inr₂ (N₁ := N₁)) p.2)))).union
      ((Set.finite_singleton ((none : Option (N₁ ⊕ N₂)),
          [Sum.inl (inl₂ (N₂ := N₂) g₁.start)])).union
        (Set.finite_singleton ((none : Option (N₁ ⊕ N₂)),
          [Sum.inl (inr₂ (N₁ := N₁) g₂.start)])))) ?_
  rintro ⟨C, γ⟩ hr
  match C with
  | none =>
    rcases hr with h | h
    · have h' : γ = [Sum.inl (inl₂ (N₂ := N₂) g₁.start)] := h
      exact Or.inr (Or.inl (by simp [h']))
    · have h' : γ = [Sum.inl (inr₂ (N₁ := N₁) g₂.start)] := h
      exact Or.inr (Or.inr (by simp [h']))
  | some (Sum.inl A) =>
    obtain ⟨β, hβ, rfl⟩ := hr
    exact Or.inl (Or.inl ⟨(A, β), hβ, rfl⟩)
  | some (Sum.inr B) =>
    obtain ⟨β, hβ, rfl⟩ := hr
    exact Or.inl (Or.inr ⟨(B, β), hβ, rfl⟩)

theorem finitary_concatGrammar {g₁ : Grammar N₁ T} {g₂ : Grammar N₂ T}
    (h₁ : g₁.Finitary) (h₂ : g₂.Finitary) : (concatGrammar g₁ g₂).Finitary := by
  refine Set.Finite.subset
    (((h₁.image (fun p => (inl₂ (N₂ := N₂) p.1, relabel (inl₂ (N₂ := N₂)) p.2))).union
        (h₂.image (fun p => (inr₂ (N₁ := N₁) p.1, relabel (inr₂ (N₁ := N₁)) p.2)))).union
      (Set.finite_singleton ((none : Option (N₁ ⊕ N₂)),
        [Sum.inl (inl₂ (N₂ := N₂) g₁.start), Sum.inl (inr₂ (N₁ := N₁) g₂.start)]))) ?_
  rintro ⟨C, γ⟩ hr
  match C with
  | none =>
    have h' : γ = [Sum.inl (inl₂ (N₂ := N₂) g₁.start), Sum.inl (inr₂ (N₁ := N₁) g₂.start)] := hr
    exact Or.inr (by simp [h'])
  | some (Sum.inl A) =>
    obtain ⟨β, hβ, rfl⟩ := hr
    exact Or.inl (Or.inl ⟨(A, β), hβ, rfl⟩)
  | some (Sum.inr B) =>
    obtain ⟨β, hβ, rfl⟩ := hr
    exact Or.inl (Or.inr ⟨(B, β), hβ, rfl⟩)

end Binary

theorem finitary_starGrammar {g : Grammar N T} (h : g.Finitary) : (starGrammar g).Finitary := by
  refine Set.Finite.subset
    ((h.image (fun p => ((some p.1 : Option N), relabel (some : N → Option N) p.2))).union
      ((Set.finite_singleton ((none : Option N), ([] : List (Option N ⊕ T)))).union
        (Set.finite_singleton ((none : Option N),
          [Sum.inl (some g.start), Sum.inl (none : Option N)])))) ?_
  rintro ⟨C, γ⟩ hr
  match C with
  | none =>
    rcases hr with h' | h'
    · have h'' : γ = ([] : List (Option N ⊕ T)) := h'
      exact Or.inr (Or.inl (by simp [h'']))
    · have h'' : γ = [Sum.inl (some g.start), Sum.inl (none : Option N)] := h'
      exact Or.inr (Or.inr (by simp [h'']))
  | some A =>
    obtain ⟨β, hβ, rfl⟩ := hr
    exact Or.inl ⟨(A, β), hβ, rfl⟩

theorem finitary_revGrammar {g : Grammar N T} (h : g.Finitary) : (revGrammar g).Finitary := by
  refine Set.Finite.subset (h.image (fun p => (p.1, p.2.reverse))) ?_
  rintro ⟨A, γ⟩ ⟨β, hβ, rfl⟩
  exact ⟨(A, β), hβ, rfl⟩

/-! ## Closure properties of the honest class -/

section Closure

open scoped Computability

/-- **Context-free languages are closed under union.** -/
theorem IsCFL.union {L₁ L₂ : Language T} (h₁ : IsCFL L₁) (h₂ : IsCFL L₂) : IsCFL (L₁ + L₂) := by
  obtain ⟨N₁, g₁, hf₁, rfl⟩ := h₁
  obtain ⟨N₂, g₂, hf₂, rfl⟩ := h₂
  exact ⟨Option (N₁ ⊕ N₂), unionGrammar g₁ g₂, finitary_unionGrammar hf₁ hf₂,
    unionGrammar_language g₁ g₂⟩

/-- **Context-free languages are closed under concatenation.** -/
theorem IsCFL.mul {L₁ L₂ : Language T} (h₁ : IsCFL L₁) (h₂ : IsCFL L₂) : IsCFL (L₁ * L₂) := by
  obtain ⟨N₁, g₁, hf₁, rfl⟩ := h₁
  obtain ⟨N₂, g₂, hf₂, rfl⟩ := h₂
  exact ⟨Option (N₁ ⊕ N₂), concatGrammar g₁ g₂, finitary_concatGrammar hf₁ hf₂,
    concatGrammar_lang g₁ g₂⟩

/-- **Context-free languages are closed under Kleene star.** -/
theorem IsCFL.kstar {L : Language T} (h : IsCFL L) : IsCFL (L∗) := by
  obtain ⟨N, g, hf, rfl⟩ := h
  exact ⟨Option N, starGrammar g, finitary_starGrammar hf, starGrammar_language g⟩

/-- **Context-free languages are closed under reversal.** -/
theorem IsCFL.reverse {L : Language T} (h : IsCFL L) : IsCFL L.reverse := by
  obtain ⟨N, g, hf, rfl⟩ := h
  exact ⟨N, revGrammar g, finitary_revGrammar hf, revGrammar_language g⟩

end Closure

/-! ## Regular languages over a finite alphabet -/

theorem finitary_ofDFA {σ : Type u} [Finite σ] [Finite T] (M : DFA T σ) :
    (ofDFA M).Finitary := by
  classical
  have hfin : (Set.univ : Set (σ × Option T)).Finite := Set.finite_univ
  refine Set.Finite.subset
    (hfin.image (fun p : σ × Option T =>
      match p.2 with
      | none => (p.1, ([] : List (σ ⊕ T)))
      | some a => (p.1, [Sum.inr a, Sum.inl (M.step p.1 a)]))) ?_
  rintro ⟨q, γ⟩ hr
  rcases hr with ⟨hγ, -⟩ | ⟨a, hγ⟩
  · have hγ' : γ = ([] : List (σ ⊕ T)) := hγ
    exact ⟨(q, none), Set.mem_univ _, by simp [hγ']⟩
  · have hγ' : γ = [Sum.inr a, Sum.inl (M.step q a)] := hγ
    exact ⟨(q, some a), Set.mem_univ _, by simp [hγ']⟩

/-- **Every regular language over a finite alphabet is context-free.** -/
theorem isCFL_of_isRegular [Finite T] {L : Language T} (h : L.IsRegular) : IsCFL L := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  have : Finite σ := hσ.finite
  have : Finite (ULift.{u} σ) := Finite.of_equiv _ Equiv.ulift.symm
  refine ⟨ULift.{u} σ, ofDFA (DFA.reindex Equiv.ulift.symm M), finitary_ofDFA _, ?_⟩
  rw [dfa_language_eq_grammar_language, DFA.accepts_reindex]

open scoped Computability in
/-- The honest class of context-free languages contains the regular languages
over a finite alphabet and is closed under the three Kleene operations. -/
theorem isCFL_kleene_closed [Finite T] :
    (∀ L : Language T, L.IsRegular → IsCFL L) ∧
      (∀ L₁ L₂ : Language T, IsCFL L₁ → IsCFL L₂ → IsCFL (L₁ + L₂)) ∧
      (∀ L₁ L₂ : Language T, IsCFL L₁ → IsCFL L₂ → IsCFL (L₁ * L₂)) ∧
      (∀ L : Language T, IsCFL L → IsCFL (L∗)) :=
  ⟨fun _ h => isCFL_of_isRegular h,
    fun _ _ h₁ h₂ => h₁.union h₂,
    fun _ _ h₁ h₂ => h₁.mul h₂,
    fun _ h => h.kstar⟩

end UAM.ContextFree
