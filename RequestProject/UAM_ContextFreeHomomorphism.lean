import RequestProject.UAM_ContextFreeClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Context-free languages are closed under homomorphic images

A *homomorphism* of words is determined by a map `f : T → List T'` sending each
letter to a word; it acts on words by `hom f w = w.flatMap f`.  Substituting
`f a` for every terminal `a` in the rules of a grammar produces a grammar for
the image language:

* `UAM.ContextFree.subst` — substitution on sentential forms;
* `UAM.ContextFree.homGrammar` — the substituted grammar;
* `UAM.ContextFree.homGrammar_language` — it generates exactly the image;
* `UAM.ContextFree.IsContextFree.hom` — the closure statement.

The technical lemma making the converse direction work is
`yields_terminals_append`: a derivation whose sentential form begins with a
block of terminals produces exactly that block first.
-/

namespace UAM.ContextFree

universe u

variable {N T T' : Type u}

/-! ## Substitution -/

/-- A letter-to-word map acting on words. -/
def hom (f : T → List T') (w : List T) : List T' := w.flatMap f

@[simp] theorem hom_nil (f : T → List T') : hom f [] = [] := rfl

@[simp] theorem hom_cons (f : T → List T') (a : T) (w : List T) :
    hom f (a :: w) = f a ++ hom f w := by simp [hom]

@[simp] theorem hom_append (f : T → List T') (u v : List T) :
    hom f (u ++ v) = hom f u ++ hom f v := by simp [hom]

/-- Substitution on a single symbol: nonterminals are kept, terminals are
replaced by their image word. -/
def substSym (f : T → List T') : N ⊕ T → List (N ⊕ T')
  | Sum.inl A => [Sum.inl A]
  | Sum.inr a => (f a).map Sum.inr

/-- Substitution on a sentential form. -/
def subst (f : T → List T') (α : List (N ⊕ T)) : List (N ⊕ T') := α.flatMap (substSym f)

@[simp] theorem subst_nil (f : T → List T') : subst (N := N) f [] = [] := rfl

@[simp] theorem subst_cons_inl (f : T → List T') (A : N) (α : List (N ⊕ T)) :
    subst f (Sum.inl A :: α) = Sum.inl A :: subst f α := by
  simp [subst, substSym]

@[simp] theorem subst_cons_inr (f : T → List T') (a : T) (α : List (N ⊕ T)) :
    subst f (Sum.inr a :: α) = (f a).map Sum.inr ++ subst f α := by
  simp [subst, substSym]

/-- The grammar obtained by substituting for every terminal. -/
def homGrammar (g : Grammar N T) (f : T → List T') : Grammar N T' where
  rule A γ := ∃ β, g.rule A β ∧ γ = subst f β
  start := g.start

/-! ## Derivations starting with a block of terminals -/

/-- A sentential form beginning with a block of terminals derives exactly that
block followed by a derivation of the rest. -/
theorem yields_terminals_append {g : Grammar N T'} (u : List T') (γ : List (N ⊕ T'))
    (w : List T') :
    Yields g (u.map Sum.inr ++ γ) w ↔ ∃ v, w = u ++ v ∧ Yields g γ v := by
  induction u generalizing w with
  | nil => exact ⟨fun h => ⟨w, rfl, by simpa using h⟩, by rintro ⟨v, rfl, hv⟩; simpa using hv⟩
  | cons a t ih =>
    constructor
    · intro h
      rw [List.map_cons, List.cons_append] at h
      cases h with
      | term hrest =>
        obtain ⟨v, rfl, hv⟩ := (ih _).1 hrest
        exact ⟨v, rfl, hv⟩
    · rintro ⟨v, rfl, hv⟩
      have := Yields.term (g := g) (a := a) ((ih (t ++ v)).2 ⟨v, rfl, hv⟩)
      simpa using this

/-! ## The two directions -/

theorem yields_homGrammar {g : Grammar N T} {f : T → List T'} {α : List (N ⊕ T)} {w : List T}
    (hy : Yields g α w) : Yields (homGrammar g f) (subst f α) (hom f w) := by
  induction hy with
  | nil => exact Yields.nil
  | @term a α₀ w₀ _ ih =>
    rw [subst_cons_inr, hom_cons]
    exact (yields_terminals_append (f a) (subst f α₀) (f a ++ hom f w₀)).2 ⟨_, rfl, ih⟩
  | @nonterm A β α₀ u w₀ hr _ _ ihβ ihtail =>
    rw [subst_cons_inl, hom_append]
    exact Yields.nonterm ⟨β, hr, rfl⟩ ihβ ihtail

/-- A word of terminals derives itself. -/
theorem yields_terminal_word (g : Grammar N T) (u : List T) :
    Yields g (u.map Sum.inr) u := by
  induction u with
  | nil => exact Yields.nil
  | cons a t ih => exact Yields.term ih

/-! ### Inverting substitution -/

theorem subst_eq_nil_inv {f : T → List T'} (α : List (N ⊕ T)) (h : subst f α = []) :
    ∃ u : List T, α = u.map Sum.inr ∧ hom f u = [] := by
  induction α with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x α₀ ih =>
    cases x with
    | inl A => simp at h
    | inr a =>
      rw [subst_cons_inr, List.append_eq_nil_iff] at h
      obtain ⟨h1, h2⟩ := h
      have hfa : f a = [] := by simpa using h1
      obtain ⟨u, rfl, hu⟩ := ih h2
      exact ⟨a :: u, by simp, by simp [hfa, hu]⟩

theorem subst_eq_cons_inl_inv {f : T → List T'} (α : List (N ⊕ T)) (A : N) :
    ∀ γ₀ : List (N ⊕ T'), subst f α = Sum.inl A :: γ₀ →
      ∃ (u : List T) (α₀ : List (N ⊕ T)), α = u.map Sum.inr ++ Sum.inl A :: α₀ ∧
        hom f u = [] ∧ γ₀ = subst f α₀ := by
  induction α with
  | nil => intro γ₀ h; simp at h
  | cons x α₀ ih =>
    intro γ₀ h
    cases x with
    | inl B =>
      rw [subst_cons_inl] at h
      simp only [List.cons.injEq] at h
      obtain ⟨hB, hrest⟩ := h
      cases (Sum.inl_injective hB : B = A)
      exact ⟨[], α₀, by simp, rfl, hrest.symm⟩
    | inr a =>
      rw [subst_cons_inr] at h
      cases hfa : f a with
      | nil =>
        rw [hfa] at h
        simp only [List.map_nil, List.nil_append] at h
        obtain ⟨u, α₁, rfl, hu, hγ⟩ := ih γ₀ h
        exact ⟨a :: u, α₁, by simp, by simp [hfa, hu], hγ⟩
      | cons d l => rw [hfa] at h; simp at h

theorem subst_eq_cons_inr_inv {f : T → List T'} (α : List (N ⊕ T)) (b : T') :
    ∀ γ₀ : List (N ⊕ T'), subst f α = Sum.inr b :: γ₀ →
      ∃ (u : List T) (a : T) (l : List T') (α₀ : List (N ⊕ T)),
        α = u.map Sum.inr ++ Sum.inr a :: α₀ ∧ hom f u = [] ∧ f a = b :: l ∧
          γ₀ = l.map Sum.inr ++ subst f α₀ := by
  induction α with
  | nil => intro γ₀ h; simp at h
  | cons x α₀ ih =>
    intro γ₀ h
    cases x with
    | inl B => rw [subst_cons_inl] at h; simp at h
    | inr a =>
      rw [subst_cons_inr] at h
      cases hfa : f a with
      | nil =>
        rw [hfa] at h
        simp only [List.map_nil, List.nil_append] at h
        obtain ⟨u, c, l, α₁, rfl, hu, hfc, hγ⟩ := ih γ₀ h
        exact ⟨a :: u, c, l, α₁, by simp, by simp [hfa, hu], hfc, hγ⟩
      | cons d l =>
        rw [hfa] at h
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
        obtain ⟨hd, hrest⟩ := h
        cases (Sum.inr_injective hd : d = b)
        exact ⟨[], a, l, α₀, by simp, rfl, hfa, hrest.symm⟩

/-! ### The converse direction -/

theorem yields_of_yields_homGrammar {g : Grammar N T} {f : T → List T'}
    {γ : List (N ⊕ T')} {w' : List T'} (hy : Yields (homGrammar g f) γ w') :
    ∀ (t : List T') (α : List (N ⊕ T)), γ = t.map Sum.inr ++ subst f α →
      ∃ w, Yields g α w ∧ w' = t ++ hom f w := by
  induction hy with
  | nil =>
    intro t α hγ
    cases t with
    | cons c s => simp at hγ
    | nil =>
      simp only [List.map_nil, List.nil_append] at hγ
      obtain ⟨u, rfl, hu⟩ := subst_eq_nil_inv α hγ.symm
      exact ⟨u, yields_terminal_word g u, by simp [hu]⟩
  | @term b γ₀ w₀ _ ih =>
    intro t α hγ
    cases t with
    | cons c s =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hγ
      obtain ⟨hc, hrest⟩ := hγ
      cases (Sum.inr_injective hc.symm : c = b)
      obtain ⟨w, hw, rfl⟩ := ih s α hrest
      exact ⟨w, hw, by simp⟩
    | nil =>
      simp only [List.map_nil, List.nil_append] at hγ
      obtain ⟨u, a, l, α₀, rfl, hu, hfa, hγ₀⟩ := subst_eq_cons_inr_inv α b γ₀ hγ.symm
      obtain ⟨w, hw, hw'⟩ := ih l α₀ hγ₀
      refine ⟨u ++ a :: w, Yields.append (yields_terminal_word g u) (Yields.term hw), ?_⟩
      simp [hw', hu, hfa]
  | @nonterm B γβ γ₀ uu w₀ hr _ _ ihβ ihtail =>
    intro t α hγ
    cases t with
    | cons c s =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hγ
      exact absurd hγ.1 (by simp)
    | nil =>
      simp only [List.map_nil, List.nil_append] at hγ
      obtain ⟨u, α₀, rfl, hu, hγ₀⟩ := subst_eq_cons_inl_inv α B γ₀ hγ.symm
      obtain ⟨β, hβ, hγβ⟩ := hr
      obtain ⟨wβ, hwβ, hw1⟩ := ihβ [] β (by simpa using hγβ)
      obtain ⟨wt, hwt, hw2⟩ := ihtail [] α₀ (by simpa using hγ₀)
      refine ⟨u ++ (wβ ++ wt),
        Yields.append (yields_terminal_word g u) (Yields.nonterm hβ hwβ hwt), ?_⟩
      simp [hw1, hw2, hu]

/-! ## The image language -/

theorem homGrammar_language (g : Grammar N T) (f : T → List T') :
    (homGrammar g f).language = {w' | ∃ w ∈ g.language, w' = hom f w} := by
  ext w'
  constructor
  · intro hw
    obtain ⟨w, hw', rfl⟩ :=
      yields_of_yields_homGrammar (f := f) hw [] [Sum.inl g.start] (by simp [homGrammar])
    exact ⟨w, hw', by simp⟩
  · rintro ⟨w, hw, rfl⟩
    have := yields_homGrammar (f := f) (α := [Sum.inl g.start]) hw
    simpa [Grammar.language, homGrammar, hom] using this

/-- **Context-free languages are closed under homomorphic images.** -/
theorem IsContextFree.hom {L : Language T} (h : IsContextFree L) (f : T → List T') :
    IsContextFree {w' : List T' | ∃ w ∈ L, w' = hom f w} := by
  obtain ⟨N, g, rfl⟩ := h
  exact ⟨N, homGrammar g f, homGrammar_language g f⟩

/-- Letterwise renaming is the special case of a homomorphism sending each
letter to a one-letter word. -/
theorem hom_singleton (f : T → T') (w : List T) :
    hom (fun a => [f a]) w = w.map f := by
  induction w with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **Context-free languages are closed under renaming of the alphabet.** -/
theorem IsContextFree.map {L : Language T} (h : IsContextFree L) (f : T → T') :
    IsContextFree (Language.map f L) := by
  have h' := h.hom (fun a => [f a])
  refine Eq.mp (congrArg IsContextFree ?_) h'
  ext w'
  simp only [Language.map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, hom_singleton]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

end UAM.ContextFree
