import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Gestalt self-reference: the diagonal barrier

Every diagonal argument in the project — Cantor's theorem, the impossibility of
a complete self-model, the halting-style barrier — is an instance of *Lawvere's
fixed-point theorem*:

`lawvere_fixedPoint`: if some `φ : A → (A → B)` is surjective, then every
`f : B → B` has a fixed point.

Contrapositively, if `B` carries a fixed-point-free endomap then no family of
`B`-valued predicates indexed by `A` can exhaust `A → B`
(`no_surjective_of_fixedPointFree`).  Specialising `B := Prop` with negation
gives Cantor's theorem (`no_surjective_to_predicates`), and specialising to a
cognitive system gives the self-model barrier
(`no_complete_selfModel`): no system can host an indexed family of behavioural
predicates rich enough to represent every predicate on its own states.
-/

namespace PolymathAtlas.Gestalt.SelfReference

universe u v

variable {A : Type u} {B : Type v}

/-- **Lawvere's fixed-point theorem.**  If `φ : A → (A → B)` is surjective then
every endomap of `B` has a fixed point. -/
theorem lawvere_fixedPoint {φ : A → A → B} (hφ : Function.Surjective φ) (f : B → B) :
    ∃ b : B, f b = b := by
  obtain ⟨a, ha⟩ := hφ (fun x => f (φ x x))
  refine ⟨φ a a, ?_⟩
  conv_rhs => rw [ha]

/-- Contrapositive form: a fixed-point-free endomap of `B` blocks every
surjection `A → (A → B)`. -/
theorem no_surjective_of_fixedPointFree {f : B → B} (hf : ∀ b, f b ≠ b) (φ : A → A → B) :
    ¬ Function.Surjective φ := by
  intro hφ
  obtain ⟨b, hb⟩ := lawvere_fixedPoint hφ f
  exact hf b hb

/-- **Cantor's theorem**, in the form used by the diagonal arguments below: no
family of predicates indexed by `A` exhausts the predicates on `A`. -/
theorem no_surjective_to_predicates (φ : A → A → Prop) : ¬ Function.Surjective φ :=
  no_surjective_of_fixedPointFree (f := Not) (fun p hp => by
    by_cases hpp : p
    · exact (hp ▸ hpp) hpp
    · exact hpp (hp ▸ hpp)) φ

/-- The diagonal predicate that witnesses the failure of surjectivity. -/
def diagonal (φ : A → A → Prop) : A → Prop := fun a => ¬ φ a a

theorem diagonal_not_mem_range (φ : A → A → Prop) : diagonal φ ∉ Set.range φ := by
  rintro ⟨a, ha⟩
  have h : φ a a ↔ ¬ φ a a := by
    conv_lhs => rw [ha]
    exact Iff.rfl
  exact (iff_not_self h)

/-! ## The self-model barrier for cognitive systems -/

/-- A *self-model* of a cognitive system on `S` is a family of predicates on
states indexed by the states themselves: state `s` encodes the predicate
`model s`. -/
structure SelfModel (S : Type u) where
  /-- The predicate encoded by a state. -/
  model : S → S → Prop

/-- A self-model is *complete* when every predicate on states is encoded by some
state. -/
def SelfModel.Complete {S : Type u} (M : SelfModel S) : Prop :=
  Function.Surjective M.model

/-- **No cognitive system has a complete self-model.**  Whatever family of
behavioural predicates the states of a system encode, the diagonal predicate
"the predicate I encode fails of me" is not among them. -/
theorem no_complete_selfModel {S : Type u} (M : SelfModel S) : ¬ M.Complete :=
  no_surjective_to_predicates M.model

/-- The explicit unrepresentable predicate of a self-model. -/
theorem exists_unrepresentable {S : Type u} (M : SelfModel S) :
    ∃ P : S → Prop, ∀ s : S, M.model s ≠ P :=
  ⟨diagonal M.model, fun s hs => diagonal_not_mem_range M.model ⟨s, hs⟩⟩

end PolymathAtlas.Gestalt.SelfReference
