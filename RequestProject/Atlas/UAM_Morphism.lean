import RequestProject.Atlas.UAM_Free

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Recognizability by finite monoids

A language `L` is *recognized* by a monoid `M` when there is a letter assignment
`f : α → M` and a subset `P ⊆ M` with `x ∈ L ↔ eval f x ∈ P`, i.e. `L` is the
preimage of `P` under the monoid homomorphism extending `f`.

The main theorem of this module is

* `isRegular_iff_isRecognizable` — a language is regular exactly when it is
  recognized by a *finite* monoid.

The two directions are the two standard constructions:

* `ofMonoid`, the automaton whose states are monoid elements, gives
  recognizable → regular;
* `transitionLetter`, the transition monoid of an automaton (the opposite of the
  monoid of state maps), gives regular → recognizable.
-/

namespace UAM.Morphism

open UAM.Free

universe u

variable {α : Type u}

/-! ## Recognition -/

/-- `f` together with the accepting set `P` recognizes `L`. -/
def Recognizes {M : Type} [Monoid M] (f : α → M) (P : Set M) (L : Language α) : Prop :=
  ∀ x : List α, x ∈ L ↔ eval f x ∈ P

/-- A language is recognizable when some finite monoid recognizes it. -/
def IsRecognizable (L : Language α) : Prop :=
  ∃ (M : Type) (_ : Monoid M) (_ : Finite M) (f : α → M) (P : Set M), Recognizes f P L

/-! ## From a monoid to an automaton -/

/-- The automaton whose states are the elements of `M`, reading a letter by
multiplying on the right. -/
def ofMonoid {M : Type} [Monoid M] (f : α → M) (P : Set M) : DFA α M where
  step m a := m * f a
  start := 1
  accept := P

theorem evalFrom_ofMonoid {M : Type} [Monoid M] (f : α → M) (P : Set M) (m : M) (x : List α) :
    (ofMonoid f P).evalFrom m x = m * eval f x := by
  induction x generalizing m with
  | nil => simp [ofMonoid]
  | cons a t ih => simp [DFA.evalFrom, ofMonoid] at ih ⊢; rw [ih, mul_assoc]

theorem accepts_ofMonoid {M : Type} [Monoid M] (f : α → M) (P : Set M) :
    (ofMonoid f P).accepts = {x : List α | eval f x ∈ P} := by
  ext x
  rw [DFA.mem_accepts, DFA.eval, evalFrom_ofMonoid]
  show (1 : M) * eval f x ∈ P ↔ eval f x ∈ P
  rw [one_mul]

/-- A language recognized by a finite monoid is regular. -/
theorem IsRecognizable.isRegular {L : Language α} (h : IsRecognizable L) : L.IsRegular := by
  obtain ⟨M, _, _, f, P, hrec⟩ := h
  have : Fintype M := Fintype.ofFinite M
  refine ⟨M, this, ofMonoid f P, ?_⟩
  rw [accepts_ofMonoid]
  ext x
  exact (hrec x).symm

/-! ## From an automaton to its transition monoid -/

variable {σ : Type}

/-- The action of a single letter on the states of an automaton, viewed in the
opposite of the monoid of self-maps (so that composition matches word order). -/
def transitionLetter (M : DFA α σ) (a : α) : (Function.End σ)ᵐᵒᵖ :=
  MulOpposite.op (fun q => M.step q a)

/-- Running the automaton on a word is applying the transition-monoid element of
that word. -/
theorem evalFrom_eq_transition (M : DFA α σ) (q : σ) (x : List α) :
    M.evalFrom q x = (eval (transitionLetter M) x).unop q := by
  induction x generalizing q with
  | nil => rfl
  | cons a t ih =>
    rw [DFA.evalFrom, List.foldl_cons, ← DFA.evalFrom, ih (M.step q a)]
    rfl

/-- Every regular language is recognized by a finite monoid, namely the
transition monoid of a recognizing automaton. -/
theorem IsRegular.isRecognizable {L : Language α} (h : L.IsRegular) : IsRecognizable L := by
  obtain ⟨σ, _, M, hM⟩ := h
  classical
  have hfin : Finite (Function.End σ)ᵐᵒᵖ :=
    Finite.of_equiv (σ → σ) (MulOpposite.opEquiv (α := Function.End σ))
  refine ⟨(Function.End σ)ᵐᵒᵖ, inferInstance, hfin, transitionLetter M,
    {g | g.unop M.start ∈ M.accept}, ?_⟩
  intro x
  rw [← hM]
  simp only [DFA.mem_accepts, DFA.eval, evalFrom_eq_transition, Set.mem_setOf_eq]

/-- **Regular = recognizable.**  A language is regular exactly when some finite
monoid recognizes it. -/
theorem isRegular_iff_isRecognizable (L : Language α) :
    L.IsRegular ↔ IsRecognizable L :=
  ⟨IsRegular.isRecognizable, IsRecognizable.isRegular⟩

end UAM.Morphism
