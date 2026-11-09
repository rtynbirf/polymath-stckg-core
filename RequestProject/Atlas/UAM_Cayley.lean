import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Morphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Cayley's theorem for monoids, and the automaton of a monoid

Left translation embeds any monoid into the monoid of self-maps of its
underlying set:

* `UAM.Cayley.leftMul` — the translation homomorphism `M →* Function.End M`;
* `UAM.Cayley.leftMul_injective` — it is injective, i.e. **Cayley's theorem**;
* `UAM.Cayley.cayleyEquiv` — consequently `M` is isomorphic to a submonoid of
  `Function.End M`;
* `UAM.Cayley.card_le_card_end` — a quantitative form for finite monoids.

The automaton `UAM.Morphism.ofMonoid` realises this embedding concretely: its
states are the monoid elements, and reading a word multiplies by its value.
`UAM.Cayley.evalFrom_ofMonoid_eq_leftMul` says that running the automaton *is*
applying the translation.
-/

namespace UAM.Cayley

open UAM.Free

universe u

variable {M : Type u} [Monoid M]

/-- Left translation, as a monoid homomorphism into the self-maps of `M`. -/
def leftMul (M : Type u) [Monoid M] : M →* Function.End M where
  toFun m := fun x => m * x
  map_one' := funext fun x => one_mul x
  map_mul' a b := funext fun x => mul_assoc a b x

@[simp] theorem leftMul_apply (m x : M) : leftMul M m x = m * x := rfl

/-- **Cayley's theorem for monoids.**  Left translation is injective, so every
monoid is isomorphic to a submonoid of the monoid of self-maps of a set. -/
theorem leftMul_injective : Function.Injective (leftMul M) := by
  intro a b hab
  have := congrFun (congrArg (fun f : Function.End M => (f : M → M)) hab) 1
  simpa using this

/-- Every monoid is isomorphic to the submonoid of `Function.End M` consisting
of the left translations. -/
noncomputable def cayleyEquiv : M ≃* MonoidHom.mrange (leftMul M) :=
  MulEquiv.ofBijective (MonoidHom.mrangeRestrict (leftMul M))
    ⟨fun _ _ hab => leftMul_injective (congrArg Subtype.val hab),
      MonoidHom.mrangeRestrict_surjective (leftMul M)⟩

/-- A finite monoid has at most as many elements as there are self-maps of its
underlying set. -/
theorem card_le_card_end [Fintype M] [DecidableEq M] :
    Fintype.card M ≤ Fintype.card (M → M) :=
  Fintype.card_le_of_injective (fun m => (leftMul M m : M → M))
    (fun _ _ hab => leftMul_injective hab)

/-! ## The automaton of a monoid -/

section Automaton

variable {N : Type} [Monoid N] {α : Type}

/-- Running the automaton of a monoid from a state is left translation by that
state applied to the value of the word. -/
theorem evalFrom_ofMonoid_eq_leftMul (f : α → N) (P : Set N) (m : N) (x : List α) :
    (UAM.Morphism.ofMonoid f P).evalFrom m x = leftMul N m (eval f x) :=
  UAM.Morphism.evalFrom_ofMonoid f P m x

/-- The words taking the automaton of a monoid from the initial state to `1` are
exactly those evaluating to `1`. -/
theorem eval_ofMonoid_eq_one_iff (f : α → N) (P : Set N) (x : List α) :
    (UAM.Morphism.ofMonoid f P).eval x = 1 ↔ eval f x = 1 := by
  rw [DFA.eval, UAM.Morphism.evalFrom_ofMonoid]
  show (1 : N) * eval f x = 1 ↔ eval f x = 1
  rw [one_mul]

end Automaton

end UAM.Cayley
