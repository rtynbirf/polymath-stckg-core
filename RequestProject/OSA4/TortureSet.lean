import RequestProject.OSA4.Compiler

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# OSA-4.0 Torture set T01–T15

A concrete operator registry together with fifteen adversarial scenarios.  Each
scenario states the verdict the compiler is expected to produce, and each claim
is settled by kernel computation (`decide`), so the suite is a genuine executable
conformance test rather than a paper exercise.
-/

namespace Polymath.OSA4

/-- Convenience constructor for operators. -/
def mkOp (name : String) (requires : List Pred) (produces consumes invalidates : List FactId)
    (modifies : List VarName) (effect : EffectLevel) (auth : Bool) : Op :=
  ⟨name, requires, produces, consumes, invalidates, modifies, effect, auth⟩

/-! ## The registry -/

def opMEASURE : Op := mkOp "MEASURE" [] ["Measurement"] [] [] [] .E1 false
def opCHECK_SUFFICIENCY : Op :=
  mkOp "CHECK_SUFFICIENCY" [.factExists "Measurement"] ["DataSufficient"] [] [] [] .E0 false
def opMODEL : Op := mkOp "MODEL" [.factExists "DataSufficient"] ["Model"] [] [] [] .E1 false
def opREPORT : Op := mkOp "REPORT" [.factExists "Model"] ["Report"] [] [] [] .E1 false
def opCALIBRATE : Op := mkOp "CALIBRATE" [.factExists "Measurement"] ["Calibrated"] [] [] [] .E1 false
def opMODIFY : Op := mkOp "MODIFY" [] ["Modified"] [] ["Calibrated"] ["sufficiency"] .E2 false
def opANALYZE_CALIBRATED : Op :=
  mkOp "ANALYZE_CALIBRATED" [.factExists "Calibrated"] ["CalibratedAnalysis"] [] [] [] .E1 false
def opACQUIRE_SAMPLE : Op := mkOp "ACQUIRE_SAMPLE" [] ["Sample"] [] [] [] .E1 false
def opDELETE_SAMPLE : Op :=
  mkOp "DELETE_SAMPLE" [.factExists "Sample"] ["Deleted"] [] ["Sample"] [] .E3 false
def opANALYZE : Op := mkOp "ANALYZE" [.factExists "Sample"] ["Analysis"] [] [] [] .E1 false
def opPRODUCE_X : Op := mkOp "PRODUCE_X" [] ["X"] [] [] [] .E1 false
def opPRODUCE_Y : Op := mkOp "PRODUCE_Y" [] ["Y"] [] [] [] .E1 false
def opDELETE_Y : Op := mkOp "DELETE_Y" [.factExists "Y"] ["DeletedY"] [] ["Y"] [] .E3 false
def opCONSUME_X : Op := mkOp "CONSUME_X" [.factExists "X"] ["ConsumedX"] ["X"] [] [] .E2 false
def opDEPLOY : Op := mkOp "DEPLOY" [] ["Deployed"] [] [] [] .E4 true
def opGRANT_AUTH_DEPLOY : Op := mkOp "GRANT_AUTH_DEPLOY" [] ["AUTH:DEPLOY"] [] [] [] .E1 false
def opDENY_AUTH_DEPLOY : Op := mkOp "DENY_AUTH_DEPLOY" [] [] [] [] [] .E1 false

/-- An operator deliberately left out of the registry. -/
def opTELEPORT : Op := mkOp "TELEPORT" [] ["Teleported"] [] [] [] .E4 false

/-- The seventeen known operators. -/
def registry : List Op :=
  [opMEASURE, opCHECK_SUFFICIENCY, opMODEL, opREPORT, opCALIBRATE, opMODIFY,
   opANALYZE_CALIBRATED, opACQUIRE_SAMPLE, opDELETE_SAMPLE, opANALYZE, opPRODUCE_X,
   opPRODUCE_Y, opDELETE_Y, opCONSUME_X, opDEPLOY, opGRANT_AUTH_DEPLOY, opDENY_AUTH_DEPLOY]

theorem registry_card : registry.length = 17 := rfl

theorem teleport_not_in_registry : opTELEPORT.name ∉ registry.map (·.name) := by decide

/-- The empty initial state. -/
def s0 : KState := ⟨[], []⟩

/-- Build a scenario over the standard registry starting from `s0`. -/
def scen (chain : List Op) (goal : Pred) : Scenario := ⟨registry, s0, chain, goal⟩

/-! ## The fifteen tests -/

inductive TortureId
  | T01 | T02 | T03 | T04 | T05 | T06 | T07 | T08 | T09 | T10 | T11 | T12 | T13 | T14 | T15
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- What each torture test asserts. -/
def TortureId.claim : TortureId → Prop
  -- T01: modelling without a declared sufficiency check is rejected.
  | .T01 => (compile (scen [opMEASURE, opMODEL] (.factExists "Model"))).verdict = .REJECT
  -- T02: destroying `Y` leaves `X` untouched.
  | .T02 => (compile (scen [opPRODUCE_X, opPRODUCE_Y, opDELETE_Y] (.factExists "X"))).verdict
      = .PASS
  -- T03: destroy-then-analyze is a liveness violation.
  | .T03 => (compile (scen [opACQUIRE_SAMPLE, opDELETE_SAMPLE, opANALYZE]
      (.factExists "Analysis"))).errors = [.E_LIVENESS_VIOLATION "ANALYZE"]
  -- T04: re-acquiring the resource makes the analysis legal again.
  | .T04 => (compile (scen [opACQUIRE_SAMPLE, opDELETE_SAMPLE, opACQUIRE_SAMPLE, opANALYZE]
      (.factExists "Analysis"))).verdict = .PASS
  -- T05: an unproved fact is `UNKNOWN`, not `FALSE`.
  | .T05 => (compile (scen [opMEASURE] (.factExists "DataSufficient"))).verdict = .UNDECIDABLE
  -- T06: a genuinely refuted goal is rejected, unlike an unknown one.
  | .T06 => (compile (scen [opMEASURE] (.pnot (.factExists "Measurement")))).verdict = .REJECT
  -- T07: an operator outside the registry is rejected by name.
  | .T07 => (compile (scen [opMEASURE, opTELEPORT] (.factExists "Teleported"))).errors
      = [.E_UNKNOWN_OPERATOR "TELEPORT"]
  -- T08: merging two agreeing beliefs is idempotent.
  | .T08 => PT.join PT.TRUE_KNOWN PT.TRUE_KNOWN = PT.TRUE_KNOWN
  -- T09: merging contradictory beliefs yields `CONFLICT`, not silent truth.
  | .T09 => PT.join PT.TRUE_KNOWN PT.FALSE_KNOWN = PT.CONFLICT
  -- T10: branches genuinely diverge — one produces `X`, the other does not.
  | .T10 => (execChain [opPRODUCE_X] s0).factStatus "X" = PT.TRUE_KNOWN ∧
      (execChain [opPRODUCE_Y] s0).factStatus "X" = PT.UNKNOWN
  -- T11: invalidating a live predicate is caught.
  | .T11 => (compile (scen [opMEASURE, opCALIBRATE, opMODIFY, opANALYZE_CALIBRATED]
      (.factExists "CalibratedAnalysis"))).errors = [.E_LIVENESS_VIOLATION "ANALYZE_CALIBRATED"]
  -- T12: double consumption is an invariant violation, not a liveness one.
  | .T12 => (compile (scen [opPRODUCE_X, opCONSUME_X, opCONSUME_X]
      (.factExists "ConsumedX"))).errors = [.E_INVARIANT_VIOLATION "CONSUME_X" "X"]
  -- T13: an unauthorized irreversible action is repairable, and the repair works.
  | .T13 => (compile (scen [opDEPLOY] (.factExists "Deployed"))).verdict = .REPAIR ∧
      (compile (scen [opGRANT_AUTH_DEPLOY, opDEPLOY] (.factExists "Deployed"))).verdict = .PASS
  -- T14: a legal chain that simply does not reach the goal is undecidable, not false.
  | .T14 => (compile (scen [opMEASURE, opCHECK_SUFFICIENCY] (.factExists "Model"))).verdict
      = .UNDECIDABLE
  -- T15: the fully repaired chain passes.
  | .T15 => (compile (scen [opMEASURE, opCHECK_SUFFICIENCY, opMODEL]
      (.factExists "Model"))).verdict = .PASS

instance : DecidablePred TortureId.claim := by
  intro t; cases t <;> (unfold TortureId.claim; infer_instance)

/-- A torture test passes when its claim holds. -/
def TortureId.passed (t : TortureId) : Prop := t.claim

instance : DecidablePred TortureId.passed := fun t => inferInstanceAs (Decidable t.claim)

theorem torture_all_pass : ∀ t : TortureId, t.passed := by decide

theorem torture_card : Fintype.card TortureId = 15 := by decide

end Polymath.OSA4
