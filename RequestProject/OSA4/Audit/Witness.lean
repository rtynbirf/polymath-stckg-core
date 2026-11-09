import RequestProject.OSA4.Audit.Operators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

/-!
# Audit: witnesses for every verdict and every error

An audit is only meaningful if the checks it performs can actually fire.  This
module exhibits a concrete scenario for each of the four verdicts and for each
of the five compile errors, so no branch of the compiler is dead code.

* `verdict_witness` and `every_verdict_reachable`;
* `unknownOperator_witness`, `invariantViolation_witness`,
  `livenessViolation_witness`, `authMissing_witness`, `authDenied_witness`, and
  the bundle `every_error_reachable`.
-/

namespace Polymath.OSA4.Audit

open Polymath.OSA4

/-- A state in which deployment authorization has been refused. -/
def sDenied : KState := ⟨[("AUTH:DEPLOY", PT.FALSE_KNOWN)], []⟩

/-- A scenario realizing each verdict. -/
def verdictWitness : Verdict → Scenario
  | .PASS => scen [opMEASURE, opCHECK_SUFFICIENCY, opMODEL] (.factExists "Model")
  | .REJECT => scen [opTELEPORT] (.factExists "Teleported")
  | .REPAIR => scen [opDEPLOY] (.factExists "Deployed")
  | .UNDECIDABLE => scen [opMEASURE] (.factExists "Model")

theorem verdict_witness (v : Verdict) : (compile (verdictWitness v)).verdict = v := by
  cases v <;> decide

/-- Every verdict of the compiler is reachable. -/
theorem every_verdict_reachable : ∀ v : Verdict, ∃ sc : Scenario, (compile sc).verdict = v :=
  fun v => ⟨verdictWitness v, verdict_witness v⟩

/-! ## Errors -/

theorem unknownOperator_witness :
    (compile (scen [opTELEPORT] (.factExists "Teleported"))).errors =
      [CompileError.E_UNKNOWN_OPERATOR "TELEPORT"] := by decide

theorem invariantViolation_witness :
    (compile (scen [opCONSUME_X] (.factExists "ConsumedX"))).errors =
      [CompileError.E_INVARIANT_VIOLATION "CONSUME_X" "X"] := by decide

theorem livenessViolation_witness :
    (compile (scen [opMODEL] (.factExists "Model"))).errors =
      [CompileError.E_LIVENESS_VIOLATION "MODEL"] := by decide

theorem authMissing_witness :
    (compile (scen [opDEPLOY] (.factExists "Deployed"))).errors =
      [CompileError.E_AUTH_MISSING "DEPLOY"] := by decide

theorem authDenied_witness :
    (compile ⟨registry, sDenied, [opDEPLOY], .factExists "Deployed"⟩).errors =
      [CompileError.E_AUTH_DENIED "DEPLOY"] := by decide

/-- Each of the five compile errors is produced by some scenario. -/
theorem every_error_reachable :
    (∃ sc, (compile sc).errors = [CompileError.E_UNKNOWN_OPERATOR "TELEPORT"]) ∧
    (∃ sc, (compile sc).errors = [CompileError.E_INVARIANT_VIOLATION "CONSUME_X" "X"]) ∧
    (∃ sc, (compile sc).errors = [CompileError.E_LIVENESS_VIOLATION "MODEL"]) ∧
    (∃ sc, (compile sc).errors = [CompileError.E_AUTH_MISSING "DEPLOY"]) ∧
    (∃ sc, (compile sc).errors = [CompileError.E_AUTH_DENIED "DEPLOY"]) :=
  ⟨⟨_, unknownOperator_witness⟩, ⟨_, invariantViolation_witness⟩,
   ⟨_, livenessViolation_witness⟩, ⟨_, authMissing_witness⟩, ⟨_, authDenied_witness⟩⟩

end Polymath.OSA4.Audit
