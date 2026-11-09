import RequestProject.OSA4.Basis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# Witnesses for the OSA-4.0 basis

The basis facts of `RequestProject.OSA4.Basis` are universally quantified.  This
module exhibits concrete *witnesses* for them inside the standard seventeen
operator registry: states in which the hypotheses of each fact really are
satisfied, and states in which they fail.  Every witness is decided by
computation, so the basis is demonstrably non-vacuous.

`witness_all_hold` proves all twenty-four witnesses; `witness_card` records
their number.
-/

namespace Polymath.OSA4

/-- Identifiers of the basis witnesses. -/
inductive WitnessId
  | W01 | W02 | W03 | W04 | W05 | W06 | W07 | W08 | W09 | W10 | W11 | W12
  | W13 | W14 | W15 | W16 | W17 | W18 | W19 | W20 | W21 | W22 | W23 | W24
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The basis item each witness illustrates. -/
def WitnessId.item : WitnessId → BasisId
  | .W01 => .B44 | .W02 => .B46 | .W03 => .B41 | .W04 => .B45
  | .W05 => .B49 | .W06 => .B50 | .W07 => .B75 | .W08 => .B75
  | .W09 => .B62 | .W10 => .B74 | .W11 => .B74 | .W12 => .B30
  | .W13 => .B29 | .W14 => .B29 | .W15 => .B79 | .W16 => .B45
  | .W17 => .B48 | .W18 => .B89 | .W19 => .B85 | .W20 => .B14
  | .W21 => .B58 | .W22 => .B58 | .W23 => .B73 | .W24 => .B73

/-- The concrete claim made by each witness. -/
def WitnessId.claim : WitnessId → Prop
  | .W01 => (opMEASURE.exec s0).factStatus "Measurement" = PT.TRUE_KNOWN
  | .W02 => (opMEASURE.exec s0).factStatus "Model" = PT.UNKNOWN
  | .W03 => opDELETE_SAMPLE.kill = ["Sample"]
  | .W04 => (opDELETE_SAMPLE.exec (opACQUIRE_SAMPLE.exec s0)).factStatus "Sample" = PT.UNKNOWN
  | .W05 => eval (execChain [opACQUIRE_SAMPLE, opDELETE_SAMPLE] s0)
      (.factExists "Sample") ≠ PT.TRUE_KNOWN
  | .W06 => eval (execChain [opACQUIRE_SAMPLE, opDELETE_SAMPLE] s0)
      (.pnot (.factExists "Sample")) ≠ PT.TRUE_KNOWN
  | .W07 => opMODEL.enabled (execChain [opMEASURE, opCHECK_SUFFICIENCY] s0)
  | .W08 => ¬ opMODEL.enabled s0
  | .W09 => eval s0 (wpChain [opMEASURE, opCHECK_SUFFICIENCY, opMODEL]
      (.factExists "Model")) = PT.TRUE_KNOWN
  | .W10 => (compile (scen [opMEASURE, opCHECK_SUFFICIENCY, opMODEL]
      (.factExists "Model"))).verdict = Verdict.PASS
  | .W11 => (compile (scen [opTELEPORT] (.factExists "Teleported"))).verdict = Verdict.REJECT
  | .W12 => chainEffect [opMEASURE, opDEPLOY] = EffectLevel.E4
  | .W13 => WithinBudget EffectLevel.E1 [opMEASURE, opCHECK_SUFFICIENCY]
  | .W14 => ¬ WithinBudget EffectLevel.E1 [opMODIFY]
  | .W15 => (compile (scen [opGRANT_AUTH_DEPLOY, opDEPLOY]
      (.factExists "Deployed"))).verdict = Verdict.PASS
  | .W16 => (opMODIFY.exec (opCALIBRATE.exec (opMEASURE.exec s0))).factStatus "Calibrated"
      = PT.UNKNOWN
  | .W17 => (opMODIFY.exec s0).varValue "sufficiency" = none
  | .W18 => registry.length = 17 ∧ opTELEPORT.name ∉ registry.map (·.name)
  | .W19 => mergeBeliefs [PT.TRUE_KNOWN, PT.FALSE_KNOWN] = PT.CONFLICT
  | .W20 => PT.join PT.TRUE_KNOWN PT.UNKNOWN = PT.TRUE_KNOWN
  | .W21 => eval s0 (conj [Pred.ctrue, Pred.ctrue]) = PT.TRUE_KNOWN
  | .W22 => eval s0 (conj [Pred.ctrue, Pred.cunknown]) ≠ PT.TRUE_KNOWN
  | .W23 => ChainOk registry [opMEASURE, opCHECK_SUFFICIENCY] s0
  | .W24 => ¬ ChainOk registry [opMODEL] s0

instance : DecidablePred WitnessId.claim := by
  intro w
  cases w <;> (unfold WitnessId.claim; infer_instance)

/-- Every witness holds, by computation. -/
theorem witness_all_hold : ∀ w : WitnessId, w.claim := by decide

/-- There are twenty-four witnesses. -/
theorem witness_card : Fintype.card WitnessId = 24 := by decide

/-- Each witness is attached to a basis item that really is a theorem. -/
theorem witness_item_covered (w : WitnessId) : w.item.claim :=
  basis_all_covered w.item

end Polymath.OSA4
