import RequestProject.OSA4.Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 Identity: type lattice and object lifecycle

Two independent pieces of the law book live here.

* A **type lattice** `Ty` with a subtyping relation obtained as the reflexive
  transitive closure of a declared parent relation.  Reflexivity (LAW-001) and
  transitivity (LAW-002) then hold by construction.
* An **object lifecycle**: a world is a history of `Action`s, `phaseOf` computes
  the current phase of an identity, and `legal` says which action may be
  appended.  From this we get consume safety (LAW-005), the no-resurrection law
  (LAW-004) and the recreation-identity law (LAW-016).
-/

namespace Polymath.OSA4

/-! ## Type lattice -/

/-- A small type universe. -/
inductive Ty
  | Bot | Measurement | Model | Report | Datum | Top
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Declared immediate parents. -/
def Ty.direct : Ty → Ty → Bool
  | .Bot, .Measurement => true
  | .Bot, .Model => true
  | .Bot, .Report => true
  | .Measurement, .Datum => true
  | .Model, .Datum => true
  | .Report, .Top => true
  | .Datum, .Top => true
  | _, _ => false

/-- Subtyping is the reflexive transitive closure of the declared parent relation. -/
def IsSubtype (a b : Ty) : Prop := Relation.ReflTransGen (fun x y => Ty.direct x y = true) a b

/-- LAW-001 (type reflexivity). -/
theorem law001_subtype_refl (a : Ty) : IsSubtype a a := Relation.ReflTransGen.refl

/-- LAW-002 (type transitivity). -/
theorem law002_subtype_trans {a b c : Ty} (h₁ : IsSubtype a b) (h₂ : IsSubtype b c) :
    IsSubtype a c := Relation.ReflTransGen.trans h₁ h₂

theorem subtype_of_direct {a b : Ty} (h : Ty.direct a b = true) : IsSubtype a b :=
  Relation.ReflTransGen.single h

theorem measurement_subtype_top : IsSubtype .Measurement .Top :=
  law002_subtype_trans (b := Ty.Datum) (subtype_of_direct (a := Ty.Measurement) (b := Ty.Datum)
    (by decide)) (subtype_of_direct (a := Ty.Datum) (b := Ty.Top) (by decide))

theorem bot_subtype_datum : IsSubtype .Bot .Datum :=
  law002_subtype_trans (b := Ty.Measurement) (subtype_of_direct (a := Ty.Bot)
    (b := Ty.Measurement) (by decide))
    (subtype_of_direct (a := Ty.Measurement) (b := Ty.Datum) (by decide))

/-! ## Object lifecycle -/

/-- Lifecycle phase of an object identity. -/
inductive Phase
  | Fresh | Available | Consumed | Destroyed
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- An object identity: a name together with a version. -/
structure ObjId where
  name : String
  version : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Lifecycle actions. -/
inductive Action
  | create (i : ObjId)
  | consume (i : ObjId)
  | destroy (i : ObjId)
  | recreate (old new : ObjId)
  deriving DecidableEq, Repr, Inhabited

/-- A world is a history of actions, most recent first. -/
abbrev World := List Action

/-- The current phase of an identity in a world. -/
def phaseOf : World → ObjId → Phase
  | [], _ => .Fresh
  | .create j :: t, i => if j = i then .Available else phaseOf t i
  | .consume j :: t, i => if j = i then .Consumed else phaseOf t i
  | .destroy j :: t, i => if j = i then .Destroyed else phaseOf t i
  | .recreate old new :: t, i =>
      if new = i then .Available else if old = i then .Destroyed else phaseOf t i

/-- Which action may legally be appended to a world. -/
def legal (w : World) : Action → Prop
  | .create i => phaseOf w i = .Fresh
  | .consume i => phaseOf w i = .Available
  | .destroy i => phaseOf w i = .Available
  | .recreate old new => phaseOf w old = .Destroyed ∧ new ≠ old ∧ phaseOf w new = .Fresh

/-- LAW-005 (consume safety): an object may be consumed exactly when available. -/
theorem law005_consume_legal_iff (w : World) (i : ObjId) :
    legal w (.consume i) ↔ phaseOf w i = .Available := Iff.rfl

/-- LAW-004 (no resurrection): a destroyed identity can be neither created afresh
nor used as the target of a recreation.  Destruction is permanent for that
identity; continuity must be carried by a *new* identity. -/
theorem law004_no_resurrection {w : World} {i : ObjId} (h : phaseOf w i = .Destroyed) :
    ¬ legal w (.create i) ∧ ∀ old : ObjId, ¬ legal w (.recreate old i) := by
  constructor
  · intro hc
    rw [legal, h] at hc
    cases hc
  · intro old hr
    obtain ⟨-, -, h3⟩ := hr
    rw [h] at h3
    cases h3

/-- LAW-016 (recreation identity): a recreation must introduce a genuinely new
identity. -/
theorem law016_recreate_new_ne_old {w : World} {old new : ObjId}
    (h : legal w (.recreate old new)) : new ≠ old := h.2.1

/-- A destroyed object stays destroyed under any action that does not mention it. -/
theorem phaseOf_destroy_persists {w : World} {i j : ObjId} (hne : j ≠ i)
    (h : phaseOf w i = .Destroyed) :
    phaseOf (.destroy j :: w) i = .Destroyed := by
  rw [phaseOf, if_neg hne, h]

/-- After a legal recreation, the old identity is destroyed and the new one is
available. -/
theorem phaseOf_after_recreate (w : World) (old new : ObjId) (h : new ≠ old) :
    phaseOf (.recreate old new :: w) new = .Available ∧
    phaseOf (.recreate old new :: w) old = .Destroyed := by
  refine ⟨by rw [phaseOf, if_pos rfl], ?_⟩
  rw [phaseOf, if_neg h, if_pos rfl]

end Polymath.OSA4
