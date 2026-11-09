import RequestProject.UAM_ContextFreeFinitary
import RequestProject.UAM_ContextFreeIntersection
import RequestProject.UAM_ContextFreeHomomorphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Intersection with a regular language, and homomorphic images, for finitary
grammars

`UAM_ContextFreeFinitary` replaced the vacuous predicate `IsContextFree` by
`IsCFL`, which insists that the generating grammar have finitely many
productions, and reproved the Kleene closure properties for it.  This module
does the same for the two remaining classical closure theorems:

* `UAM.ContextFree.IsCFL.inter_regular` — the intersection of a context-free
  language with a regular one is context-free;
* `UAM.ContextFree.IsCFL.hom` — context-free languages are closed under
  homomorphic images.

The work is to check that the two grammar constructions stay finitary.  For the
homomorphism grammar this is immediate.  For the triple grammar it rests on
`UAM.ContextFree.finite_threaded`: for fixed endpoints there are only finitely
many ways of threading automaton states through a right-hand side.
-/

namespace UAM.ContextFree

universe u

variable {N T σ : Type u}

/-! ## Homomorphic images -/

theorem finitary_homGrammar {g : Grammar N T} (h : g.Finitary) {T' : Type u} (f : T → List T') :
    (homGrammar g f).Finitary := by
  refine Set.Finite.subset (h.image (fun p => (p.1, subst f p.2))) ?_
  rintro ⟨A, γ⟩ ⟨β, hβ, rfl⟩
  exact ⟨(A, β), hβ, rfl⟩

/-- **Context-free languages are closed under homomorphic images.** -/
theorem IsCFL.hom {L : Language T} (h : IsCFL L) {T' : Type u} (f : T → List T') :
    IsCFL {w' : List T' | ∃ w ∈ L, w' = hom f w} := by
  obtain ⟨N, g, hf, rfl⟩ := h
  exact ⟨N, homGrammar g f, finitary_homGrammar hf f, homGrammar_language g f⟩

/-! ## Threading finitely many ways -/

/-- For fixed endpoints, a right-hand side can be threaded with automaton states
in only finitely many ways. -/
theorem finite_threaded [Finite σ] (M : DFA T σ) (p q : σ) (β : List (N ⊕ T)) :
    {γ : List ((Option (σ × N × σ)) ⊕ T) | Threaded M p β γ q}.Finite := by
  induction β generalizing p with
  | nil =>
    refine Set.Finite.subset (Set.finite_singleton ([] : List ((Option (σ × N × σ)) ⊕ T))) ?_
    rintro γ hγ
    cases hγ
    exact rfl
  | cons x β ih =>
    match x with
    | Sum.inr a =>
      refine Set.Finite.subset ((ih (M.step p a)).image (fun γ => Sum.inr a :: γ)) ?_
      rintro γ hγ
      cases hγ with
      | term hrest => exact ⟨_, hrest, rfl⟩
    | Sum.inl A =>
      have hfin : (Set.univ : Set σ).Finite := Set.finite_univ
      refine Set.Finite.subset
        (hfin.biUnion (fun r _ => (ih r).image
          (fun γ => Sum.inl (some (p, A, r)) :: γ))) ?_
      rintro γ hγ
      cases hγ with
      | nonterm hrest =>
        rename_i r _
        exact Set.mem_biUnion (Set.mem_univ r) ⟨_, hrest, rfl⟩

theorem finitary_prodGrammar [Finite σ] {g : Grammar N T} (h : g.Finitary) (M : DFA T σ) :
    (prodGrammar g M).Finitary := by
  classical
  have hstart :
      {p : Option (σ × N × σ) × List ((Option (σ × N × σ)) ⊕ T) |
        p.1 = none ∧ ∃ f : σ, p.2 = [Sum.inl (some (M.start, g.start, f))]}.Finite := by
    refine Set.Finite.subset ((Set.finite_univ (α := σ)).image
      (fun f : σ => ((none : Option (σ × N × σ)),
        [Sum.inl (some (M.start, g.start, f))]))) ?_
    rintro ⟨C, γ⟩ ⟨rfl, f, rfl⟩
    exact ⟨f, Set.mem_univ f, rfl⟩
  have hbody :
      {p : Option (σ × N × σ) × List ((Option (σ × N × σ)) ⊕ T) |
        ∃ (A : N) (β : List (N ⊕ T)) (r s : σ), g.rule A β ∧ p.1 = some (r, A, s) ∧
          Threaded M r β p.2 s}.Finite := by
    have hprod : ((g.rules ×ˢ (Set.univ : Set (σ × σ)))).Finite :=
      h.prod (Set.finite_univ)
    refine Set.Finite.subset
      (hprod.biUnion (fun x _ =>
        (finite_threaded M x.2.1 x.2.2 x.1.2).image
          (fun γ => ((some (x.2.1, x.1.1, x.2.2) : Option (σ × N × σ)), γ)))) ?_
    rintro ⟨C, γ⟩ ⟨A, β, r, s, hrule, rfl, hthread⟩
    have hmem : (((A, β), (r, s)) : (N × List (N ⊕ T)) × σ × σ) ∈
        g.rules ×ˢ (Set.univ : Set (σ × σ)) := Set.mem_prod.2 ⟨hrule, Set.mem_univ _⟩
    exact Set.mem_biUnion hmem ⟨γ, hthread, rfl⟩
  refine Set.Finite.subset (hstart.union hbody) ?_
  rintro ⟨C, γ⟩ hr
  match C with
  | none =>
    obtain ⟨f, hf, hγ⟩ := hr
    exact Or.inl ⟨rfl, f, hγ⟩
  | some (r, A, s) =>
    obtain ⟨β, hβ, hthread⟩ := hr
    exact Or.inr ⟨A, β, r, s, hβ, rfl, hthread⟩

/-- **Context-free ∩ regular is context-free.** -/
theorem IsCFL.inter_regular {L R : Language T} (hL : IsCFL L) (hR : R.IsRegular) :
    IsCFL (L ⊓ R) := by
  obtain ⟨N, g, hfin, rfl⟩ := hL
  obtain ⟨τ, hτ, M, rfl⟩ := hR
  have : Finite τ := hτ.finite
  have : Finite (ULift.{u} τ) := Finite.of_equiv _ Equiv.ulift.symm
  refine ⟨Option (ULift.{u} τ × N × ULift.{u} τ),
    prodGrammar g (DFA.reindex Equiv.ulift.symm M), finitary_prodGrammar hfin _, ?_⟩
  rw [prodGrammar_language, DFA.accepts_reindex]

/-- Context-free languages are closed under intersection with a regular language
on either side. -/
theorem IsCFL.regular_inter {L R : Language T} (hR : R.IsRegular) (hL : IsCFL L) :
    IsCFL (R ⊓ L) := by
  have h := hL.inter_regular hR
  rwa [inf_comm] at h

end UAM.ContextFree
