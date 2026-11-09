import RequestProject.OSA4.Effects
import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# Classification axes of operators

Every operator is classified along four independent axes: its effect level, its
authorization requirement, whether it destroys facts, and whether it invalidates
variables.  The `profile` of an operator collects the four coordinates.

* `Polymath.OSA4.Op.profile` — the four-coordinate classification;
* `Polymath.OSA4.nonDestructive_iff_not_destructive` — the destructiveness axis
  agrees with the semantic notion `NonDestructive`;
* `Polymath.OSA4.factStatus_exec_of_not_destructive`,
  `Polymath.OSA4.varValue_exec_of_not_mutating` — each axis controls exactly the
  part of the state it names;
* the profiles of the seventeen registry operators, computed by `decide`.
-/

namespace Polymath.OSA4

/-- The four classification axes. -/
inductive Axis
  | effect | authorization | destructiveness | mutation
  deriving DecidableEq, Repr, Fintype, Inhabited

theorem axis_card : Fintype.card Axis = 4 := by decide

namespace Op

/-- Does the operator destroy facts? -/
def isDestructive (o : Op) : Bool := !o.kill.isEmpty

/-- Does the operator invalidate variables? -/
def isMutating (o : Op) : Bool := !o.modifies.isEmpty

/-- The four-coordinate classification of an operator. -/
structure Profile where
  /-- The effect level. -/
  effect : EffectLevel
  /-- Does the operator need authorization? -/
  auth : Bool
  /-- Does the operator destroy facts? -/
  destructive : Bool
  /-- Does the operator invalidate variables? -/
  mutating : Bool
  deriving DecidableEq, Repr

/-- The profile of an operator. -/
def profile (o : Op) : Profile :=
  ⟨o.effect, o.requiresAuth, o.isDestructive, o.isMutating⟩

@[simp] theorem profile_effect (o : Op) : (profile o).effect = o.effect := rfl
@[simp] theorem profile_auth (o : Op) : (profile o).auth = o.requiresAuth := rfl
@[simp] theorem profile_destructive (o : Op) : (profile o).destructive = o.isDestructive := rfl
@[simp] theorem profile_mutating (o : Op) : (profile o).mutating = o.isMutating := rfl

end Op

/-! ## The axes control exactly what they name -/

/-- The destructiveness axis is the semantic notion of non-destructiveness. -/
theorem nonDestructive_iff_not_destructive (o : Op) :
    NonDestructive o ↔ o.isDestructive = false := by
  unfold NonDestructive Op.isDestructive
  cases h : o.kill with
  | nil => simp
  | cons a t => simp

/-- A non-destructive operator never turns a known fact off. -/
theorem factStatus_exec_of_not_destructive {o : Op} (ho : o.isDestructive = false)
    (s : KState) {f : FactId} (hf : s.factStatus f = PT.TRUE_KNOWN) :
    (o.exec s).factStatus f = PT.TRUE_KNOWN :=
  factStatus_exec_of_nonDestructive ((nonDestructive_iff_not_destructive o).2 ho) s hf

/-- A non-mutating operator never changes a variable. -/
theorem varValue_exec_of_not_mutating {o : Op} (ho : o.isMutating = false) (s : KState)
    (v : VarName) : (o.exec s).varValue v = s.varValue v := by
  have hmod : o.modifies = [] := by
    unfold Op.isMutating at ho
    cases h : o.modifies with
    | nil => rfl
    | cons a t => rw [h] at ho; simp at ho
  exact Op.varValue_exec_untouched o s (by rw [hmod]; simp)

/-- An unauthorized-by-default operator imposes no authorization obligation. -/
theorem execAllowed_iff_enabled_of_no_auth {o : Op} (ho : o.requiresAuth = false)
    (s : KState) : o.execAllowed s ↔ o.enabled s := by
  unfold Op.execAllowed
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun hr => absurd (hr.symm.trans ho) (by simp)⟩

/-! ## Profiles of the standard registry -/

theorem profile_opMEASURE : Op.profile opMEASURE = ⟨EffectLevel.E1, false, false, false⟩ := rfl

theorem profile_opDELETE_SAMPLE :
    Op.profile opDELETE_SAMPLE = ⟨EffectLevel.E3, false, true, false⟩ := rfl

theorem profile_opMODIFY : Op.profile opMODIFY = ⟨EffectLevel.E2, false, true, true⟩ := rfl

theorem profile_opDEPLOY : Op.profile opDEPLOY = ⟨EffectLevel.E4, true, false, false⟩ := rfl

/-- Exactly four operators of the registry destroy facts. -/
theorem destructive_registry_ops :
    registry.filter (fun o => o.isDestructive) =
      [opMODIFY, opDELETE_SAMPLE, opDELETE_Y, opCONSUME_X] := by
  decide

/-- Exactly one operator of the registry invalidates a variable. -/
theorem mutating_registry_ops :
    registry.filter (fun o => o.isMutating) = [opMODIFY] := by decide

/-- Exactly one operator of the registry needs authorization. -/
theorem auth_registry_ops :
    registry.filter (fun o => o.requiresAuth) = [opDEPLOY] := by decide

/-- In the standard registry, destroying facts always costs at least effect
level `E2`. -/
theorem destructive_effect_ge :
    ∀ o ∈ registry, o.isDestructive = true → EffectLevel.E2 ≤ o.effect := by decide

/-- In the standard registry, only the top effect level requires authorization. -/
theorem auth_effect_eq_E4 :
    ∀ o ∈ registry, o.requiresAuth = true → o.effect = EffectLevel.E4 := by decide

end Polymath.OSA4
