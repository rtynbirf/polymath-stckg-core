import RequestProject.OSA.Theorems
import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

/-!
# Gold-standard specifications and plans

Three reference specifications over the standard registry, each with a plan
that satisfies it, and near-miss plans that do not.  Every statement is
discharged by kernel computation.
-/

namespace Polymath.OSA.Gold

open Polymath.OSA Polymath.OSA4

/-- Build a model from measurements, at effect level `E1`. -/
def modelSpec : Spec := ⟨"MODEL-V1", registry, .factExists "Model", .E1⟩

/-- Produce a report, at effect level `E1`. -/
def reportSpec : Spec := ⟨"REPORT-V1", registry, .factExists "Report", .E1⟩

/-- Deploy, which is irreversible and needs authorization. -/
def deploySpec : Spec := ⟨"DEPLOY-V1", registry, .factExists "Deployed", .E4⟩

/-- The gold plan for `modelSpec`. -/
def modelPlan : List Op := [opMEASURE, opCHECK_SUFFICIENCY, opMODEL]

/-- The gold plan for `reportSpec`. -/
def reportPlan : List Op := [opMEASURE, opCHECK_SUFFICIENCY, opMODEL, opREPORT]

/-- The gold plan for `deploySpec`: obtain authorization first. -/
def deployPlan : List Op := [opGRANT_AUTH_DEPLOY, opDEPLOY]

theorem modelPlan_satisfies : modelSpec.Satisfies s0 modelPlan := by decide

theorem reportPlan_satisfies : reportSpec.Satisfies s0 reportPlan := by decide

theorem deployPlan_satisfies : deploySpec.Satisfies s0 deployPlan := by decide

/-- Skipping the sufficiency check leaves `MODEL` disabled. -/
theorem modelPlan_shortcut_fails : ¬ modelSpec.Satisfies s0 [opMEASURE, opMODEL] := by decide

/-- Deploying without authorization is not conforming. -/
theorem deployPlan_unauthorized_fails : ¬ deploySpec.Satisfies s0 [opDEPLOY] := by decide

/-- Deployment does not fit in an `E3` budget. -/
theorem deployPlan_budget_too_tight :
    ¬ Spec.Satisfies { deploySpec with budget := .E3 } s0 deployPlan := by decide

/-- The gold set: three specifications, each with a conforming plan. -/
theorem gold_all_satisfy :
    modelSpec.Satisfies s0 modelPlan ∧
    reportSpec.Satisfies s0 reportPlan ∧
    deploySpec.Satisfies s0 deployPlan :=
  ⟨modelPlan_satisfies, reportPlan_satisfies, deployPlan_satisfies⟩

end Polymath.OSA.Gold
