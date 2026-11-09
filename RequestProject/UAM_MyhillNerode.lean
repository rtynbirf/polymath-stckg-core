import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Myhill–Nerode relation and minimality of the Nerode automaton

`MyhillNerodeEquiv L x y` holds when `x` and `y` have the same right context in
`L`.  It is an equivalence relation and a right congruence, and its quotient
`NerodeClasses L` is in bijection with the set of left quotients of `L`.  Hence:

* `myhill_nerode_finite_iff_regular` — `L` is regular exactly when the relation
  has finite index;
* `card_nerodeClasses_le_card_states` — every automaton recognising `L` has at
  least as many states as `L` has Nerode classes, i.e. the Nerode automaton
  `nerodeDFA` (which accepts `L`, `nerodeDFA_accepts`) is state-minimal.
-/

namespace UAM.MyhillNerode

variable {α : Type*}

/-- The Myhill–Nerode relation: `x` and `y` admit exactly the same
continuations in `L`. -/
def MyhillNerodeEquiv (L : Language α) (x y : List α) : Prop :=
  ∀ w : List α, x ++ w ∈ L ↔ y ++ w ∈ L

theorem myhillNerodeEquiv_iff_leftQuotient (L : Language α) (x y : List α) :
    MyhillNerodeEquiv L x y ↔ L.leftQuotient x = L.leftQuotient y := by
  constructor
  · intro h
    ext w
    simpa [Language.mem_leftQuotient] using h w
  · intro h w
    have : w ∈ L.leftQuotient x ↔ w ∈ L.leftQuotient y := by rw [h]
    simpa [Language.mem_leftQuotient] using this

theorem myhillNerodeEquiv_refl (L : Language α) (x : List α) : MyhillNerodeEquiv L x x :=
  fun _ => Iff.rfl

theorem myhillNerodeEquiv_symm {L : Language α} {x y : List α}
    (h : MyhillNerodeEquiv L x y) : MyhillNerodeEquiv L y x := fun w => (h w).symm

theorem myhillNerodeEquiv_trans {L : Language α} {x y z : List α}
    (h₁ : MyhillNerodeEquiv L x y) (h₂ : MyhillNerodeEquiv L y z) :
    MyhillNerodeEquiv L x z := fun w => (h₁ w).trans (h₂ w)

/-- The Myhill–Nerode relation is a right congruence. -/
theorem myhillNerodeEquiv_right_congruence {L : Language α} {x y : List α}
    (h : MyhillNerodeEquiv L x y) (z : List α) :
    MyhillNerodeEquiv L (x ++ z) (y ++ z) := by
  intro w
  simpa [List.append_assoc] using h (z ++ w)

/-- The Myhill–Nerode relation as a setoid. -/
def nerodeSetoid (L : Language α) : Setoid (List α) where
  r := MyhillNerodeEquiv L
  iseqv :=
    ⟨myhillNerodeEquiv_refl L, myhillNerodeEquiv_symm, myhillNerodeEquiv_trans⟩

/-- The Nerode classes of a language. -/
def NerodeClasses (L : Language α) : Type _ := Quotient (nerodeSetoid L)

/-- The class of a word. -/
def nerodeClass (L : Language α) (x : List α) : NerodeClasses L :=
  Quotient.mk (nerodeSetoid L) x

theorem nerodeClass_eq_iff (L : Language α) (x y : List α) :
    nerodeClass L x = nerodeClass L y ↔ MyhillNerodeEquiv L x y :=
  Quotient.eq (r := nerodeSetoid L)

/-- Nerode classes are exactly the left quotients of the language. -/
noncomputable def nerodeClassesEquivLeftQuotients (L : Language α) :
    NerodeClasses L ≃ Set.range L.leftQuotient := by
  refine Equiv.ofBijective
    (Quotient.lift (fun x => (⟨L.leftQuotient x, ⟨x, rfl⟩⟩ : Set.range L.leftQuotient))
      ?_) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext ((myhillNerodeEquiv_iff_leftQuotient L x y).1 hxy)
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        exact (nerodeClass_eq_iff L x y).2
          ((myhillNerodeEquiv_iff_leftQuotient L x y).2 (Subtype.ext_iff.1 hab))
  · rintro ⟨s, x, rfl⟩
    exact ⟨nerodeClass L x, rfl⟩

/-- **Myhill–Nerode theorem.** A language is regular exactly when its Nerode
relation has finite index. -/
theorem myhill_nerode_finite_iff_regular (L : Language α) :
    Finite (NerodeClasses L) ↔ L.IsRegular := by
  rw [Language.isRegular_iff_finite_range_leftQuotient, ← Set.finite_coe_iff]
  exact ⟨fun _ => Finite.of_equiv _ (nerodeClassesEquivLeftQuotients L),
    fun _ => Finite.of_equiv _ (nerodeClassesEquivLeftQuotients L).symm⟩

/-- The Nerode automaton of a language: its states are the left quotients. -/
def nerodeDFA (L : Language α) : DFA α (Set.range L.leftQuotient) := L.toDFA

theorem nerodeDFA_accepts (L : Language α) : (nerodeDFA L).accepts = L :=
  Language.accepts_toDFA L

/-- States of an automaton recognising `L` that agree determine the same Nerode
class. -/
theorem myhillNerodeEquiv_of_eval_eq {σ : Type*} (M : DFA α σ) {x y : List α}
    (h : M.eval x = M.eval y) : MyhillNerodeEquiv M.accepts x y := by
  intro w
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
  rw [show M.evalFrom M.start x = M.evalFrom M.start y from h]

/-- **Minimality.** Any automaton recognising `L` has at least as many states as
`L` has Nerode classes. -/
theorem card_nerodeClasses_le_card_states {σ : Type*} [Fintype σ] (M : DFA α σ) :
    Nat.card (NerodeClasses M.accepts) ≤ Fintype.card σ := by
  classical
  set L := M.accepts with hL
  have hsurj : Function.Surjective
      (fun q : σ => if h : ∃ x : List α, M.eval x = q then nerodeClass L h.choose
        else nerodeClass L []) := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
      refine ⟨M.eval x, ?_⟩
      have hex : ∃ z : List α, M.eval z = M.eval x := ⟨x, rfl⟩
      show (if h : ∃ z : List α, M.eval z = M.eval x then nerodeClass L h.choose
        else nerodeClass L []) = nerodeClass L x
      rw [dif_pos hex]
      exact (nerodeClass_eq_iff L _ x).2 (myhillNerodeEquiv_of_eval_eq M hex.choose_spec)
  simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective _ hsurj

end UAM.MyhillNerode
