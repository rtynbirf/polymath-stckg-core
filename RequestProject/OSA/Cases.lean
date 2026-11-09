import RequestProject.OSA.Conformance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# Conformance case set

Six conformance cases over the gold specifications, each with its expected
outcome, all decided by kernel computation.
-/

namespace Polymath.OSA

open Polymath.OSA4 Polymath.OSA.Gold

/-- Identifiers of the six conformance cases. -/
inductive CaseId
  | C1 | C2 | C3 | C4 | C5 | C6
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- What each case asserts. -/
def CaseId.claim : CaseId → Prop
  -- C1: the gold model plan conforms.
  | .C1 => modelSpec.Satisfies s0 modelPlan
  -- C2: skipping the sufficiency check does not conform.
  | .C2 => ¬ modelSpec.Satisfies s0 [opMEASURE, opMODEL]
  -- C3: the report plan conforms.
  | .C3 => reportSpec.Satisfies s0 reportPlan
  -- C4: deploying without authorization does not conform.
  | .C4 => ¬ deploySpec.Satisfies s0 [opDEPLOY]
  -- C5: authorizing first makes deployment conform.
  | .C5 => deploySpec.Satisfies s0 deployPlan
  -- C6: the conformance checker selects the gold plan from a candidate list.
  | .C6 => selectPlan modelSpec s0 [[opMEASURE], [opMEASURE, opMODEL], modelPlan] = some modelPlan

/-- Every conformance case comes out as expected. -/
theorem cases_all_pass : ∀ c : CaseId, c.claim := by
  intro c
  cases c with
  | C1 => exact modelPlan_satisfies
  | C2 => exact modelPlan_shortcut_fails
  | C3 => exact reportPlan_satisfies
  | C4 => exact deployPlan_unauthorized_fails
  | C5 => exact deployPlan_satisfies
  | C6 => exact selectPlan_gold

theorem cases_card : Fintype.card CaseId = 6 := by decide

end Polymath.OSA
