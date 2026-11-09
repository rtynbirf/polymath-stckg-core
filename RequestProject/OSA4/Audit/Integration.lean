import RequestProject.OSA4.Lawbook
import RequestProject.OSA4.Audit.Torture20

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

/-!
# OSA-4.0 Audit: integration tests

Six checks that exercise several modules at once: the lawbook, the extended
torture suite, the weakest-precondition transformer, the compiler on a concrete
scenario, one-step repair, and the epistemic reading of invalidation.
-/

namespace Polymath.OSA4

/-- The six integration tests. -/
inductive IntegrationTest
  | I1 | I2 | I3 | I4 | I5 | I6
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- What each integration test claims. -/
def IntegrationTest.claim : IntegrationTest → Prop
  -- I1: every law of the lawbook holds.
  | .I1 => ∀ l : LawId, l.holds
  -- I2: the extended torture suite passes.
  | .I2 => ∀ t : TortureId20, t.claim
  -- I3: the weakest-precondition transformer agrees with execution, for every
  -- operator, state and postcondition.
  | .I3 => ∀ (o : Op) (s : KState) (q : Pred), eval s (o.wp q) = eval (o.exec s) q
  -- I4: the repaired measurement chain compiles to PASS.
  | .I4 => (compile (scen [opMEASURE, opCHECK_SUFFICIENCY, opMODEL] (.factExists "Model"))).verdict
      = Verdict.PASS
  -- I5: an unauthorized deployment is repaired by obtaining authorization, and
  -- the repaired scenario passes.
  | .I5 => bestRepair deployScenario = some ⟨[opGRANT_AUTH_DEPLOY]⟩ ∧
      (compile ((⟨[opGRANT_AUTH_DEPLOY]⟩ : RepairPlan).apply deployScenario)).verdict = Verdict.PASS
  -- I6: invalidating a fact never refutes it.
  | .I6 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill →
      eval (o.exec s) (.pnot (.factExists f)) ≠ PT.TRUE_KNOWN

/-- All six integration tests hold. -/
theorem integration_all_pass : ∀ t : IntegrationTest, t.claim := by
  intro t
  cases t with
  | I1 => exact lawbook_holds
  | I2 => exact torture20_all_pass
  | I3 => exact fun o s q => Op.eval_wp o s q
  | I4 =>
    show (compile (scen [opMEASURE, opCHECK_SUFFICIENCY, opMODEL] (.factExists "Model"))).verdict
      = Verdict.PASS
    decide
  | I5 => exact ⟨deploy_bestRepair, deploy_repaired_passes⟩
  | I6 => exact fun o s _ hf => Op.law017_invalidate_not_refute o s hf

theorem integration_card : Fintype.card IntegrationTest = 6 := by decide

end Polymath.OSA4
