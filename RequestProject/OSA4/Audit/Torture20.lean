import RequestProject.OSA4.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

/-!
# OSA-4.0 Audit: torture set extended to T20

Five further scenarios (T16–T20) exercising the frame property, effect
aggregation, the weakest-precondition transformer, the four-valued algebra and
repair selection.  `TortureId20` bundles them with the original fifteen.
-/

namespace Polymath.OSA4

inductive TortureId20
  | old (t : TortureId)
  | T16 | T17 | T18 | T19 | T20
  deriving DecidableEq, Repr, Inhabited

instance : Fintype TortureId20 where
  elems := (Finset.univ.image TortureId20.old) ∪
    {TortureId20.T16, TortureId20.T17, TortureId20.T18, TortureId20.T19, TortureId20.T20}
  complete := by
    intro t
    cases t <;> simp

/-- What each of the five new tests asserts. -/
def TortureId20.claim : TortureId20 → Prop
  | .old t => t.passed
  -- T16: the frame property in action — measuring does not disturb the sample.
  | .T16 => (execChain [opACQUIRE_SAMPLE, opMEASURE] s0).factStatus "Sample" = PT.TRUE_KNOWN
  -- T17: effect levels aggregate to the maximum along a chain.
  | .T17 => aggregate ([opMEASURE, opGRANT_AUTH_DEPLOY, opDEPLOY].map (·.effect)) = EffectLevel.E4
  -- T18: the weakest precondition of a produced fact is trivially satisfiable.
  | .T18 => eval s0 (opMEASURE.wp (.factExists "Measurement")) = PT.TRUE_KNOWN
  -- T19: absence of information is not conflict.
  | .T19 => PT.join PT.UNKNOWN PT.TRUE_KNOWN = PT.TRUE_KNOWN ∧ PT.neg PT.UNKNOWN = PT.UNKNOWN
  -- T20: the cheapest repair for an unauthorized deployment is to seek authorization.
  | .T20 => bestRepair deployScenario = some ⟨[opGRANT_AUTH_DEPLOY]⟩

instance : DecidablePred TortureId20.claim := by
  intro t
  cases t
  · exact inferInstanceAs (Decidable (TortureId.passed _))
  all_goals (unfold TortureId20.claim; infer_instance)

def TortureId20.passed (t : TortureId20) : Prop := t.claim

instance : DecidablePred TortureId20.passed := fun t => inferInstanceAs (Decidable t.claim)

theorem torture20_all_pass : ∀ t : TortureId20, t.passed := by decide

theorem torture20_card : Fintype.card TortureId20 = 20 := by decide

end Polymath.OSA4
