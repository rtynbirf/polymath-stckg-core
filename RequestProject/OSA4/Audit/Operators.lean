import RequestProject.OSA4.Criteria
import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Audit: operator contracts

Two kinds of check.  Generic contracts, proved for every operator:

* `produces_true_after_exec`, `kill_not_true_after_exec`, `produces_disjoint_kill`.

And concrete checks on the seventeen operators of the standard registry, all
discharged by kernel computation:

* `registry_names_nodup` — operator names identify operators;
* `registry_auth_iff_deploy` — deployment is the only authorized operator;
* `registry_irreversible_iff_deploy` — deployment is the only `E4` operator;
* `registry_destroys_iff` — exactly four operators destroy facts.
-/

namespace Polymath.OSA4.Audit

open Polymath.OSA4

/-! ## Generic contracts -/

/-- Everything an operator produces is known after it runs. -/
theorem produces_true_after_exec (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.produces) :
    (o.exec s).factStatus f = PT.TRUE_KNOWN := Op.factStatus_exec_produces o s hf

/-- Everything an operator destroys is no longer known after it runs. -/
theorem kill_not_true_after_exec (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.kill) :
    (o.exec s).factStatus f ≠ PT.TRUE_KNOWN := by
  rw [Op.factStatus_exec_kill o s hf]
  decide

/-- No operator both produces and destroys the same fact. -/
theorem produces_disjoint_kill (o : Op) {f : FactId} (hf : f ∈ o.produces) : f ∉ o.kill :=
  Op.notMem_kill_of_mem_produces hf

/-- An operator that requires no authorization is always authorized. -/
theorem authorized_of_not_requiresAuth {o : Op} (h : o.requiresAuth = false) (s : KState) :
    o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN := by
  rw [h]; intro hc; cases hc

/-! ## The standard registry -/

theorem registry_names_nodup : (registry.map (·.name)).Nodup := by decide

theorem registry_auth_iff_deploy :
    ∀ o ∈ registry, (o.requiresAuth = true ↔ o.name = "DEPLOY") := by decide

theorem registry_irreversible_iff_deploy :
    ∀ o ∈ registry, (o.effect = EffectLevel.E4 ↔ o.name = "DEPLOY") := by decide

theorem registry_destroys_iff :
    ∀ o ∈ registry, (o.kill ≠ [] ↔
      o.name ∈ ["MODIFY", "DELETE_SAMPLE", "DELETE_Y", "CONSUME_X"]) := by decide

/-- Every registry operator produces at most one fact. -/
theorem registry_produces_length_le_one : ∀ o ∈ registry, o.produces.length ≤ 1 := by decide

/-- The measurement chain is a low-effect chain. -/
theorem measurement_chain_effect :
    chainEffect [opMEASURE, opCHECK_SUFFICIENCY, opMODEL] = EffectLevel.E1 := by decide

/-- Deployment is irreversible. -/
theorem deploy_chain_effect : chainEffect [opDEPLOY] = EffectLevel.E4 := by decide

/-- The measurement chain stays within an `E1` budget; the deployment chain does
not. -/
theorem budget_audit :
    WithinBudget EffectLevel.E1 [opMEASURE, opCHECK_SUFFICIENCY, opMODEL] ∧
    ¬ WithinBudget EffectLevel.E1 [opDEPLOY] := by
  constructor
  · decide
  · decide

end Polymath.OSA4.Audit
