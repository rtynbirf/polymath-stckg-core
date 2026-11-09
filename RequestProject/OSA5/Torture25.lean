import RequestProject.OSA5.Repair
import RequestProject.OSA4.Audit.Torture20

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/-!
# OSA-5.0 Torture set T21–T25

The five OSA-5.0 scenarios test the multistep repair search: that a repair of
length two is genuinely out of reach at depth one, that it is found at depth two,
that the repaired chain compiles, that iterative deepening returns the shortest
repair, and that an unreachable goal is reported as unreachable rather than
patched over.

`TortureId25` bundles these with the twenty earlier tests, and
`torture25_all_pass` settles all twenty-five by kernel computation.
-/

namespace Polymath.OSA5

open Polymath.OSA4

/-- The goal "make `MODEL` runnable and thereby obtain a model". -/
def modelGoal : Pred := chainPred [opMODEL] (.factExists "Model")

inductive TortureId25
  | old (t : TortureId20)
  | T21 | T22 | T23 | T24 | T25
  deriving DecidableEq, Repr, Inhabited

instance : Fintype TortureId25 where
  elems := (Finset.univ.image TortureId25.old) ∪
    {TortureId25.T21, TortureId25.T22, TortureId25.T23, TortureId25.T24, TortureId25.T25}
  complete := by
    intro t
    cases t <;> simp

/-- What each of the five OSA-5.0 tests asserts. -/
def TortureId25.claim : TortureId25 → Prop
  | .old t => t.passed
  -- T21: no single operator suffices.
  | .T21 => searchRepair registry modelGoal 1 s0 = none
  -- T22: at depth two the search finds the measure-then-check plan.
  | .T22 => searchRepair registry modelGoal 2 s0 = some [opMEASURE, opCHECK_SUFFICIENCY]
  -- T23: the repaired chain compiles cleanly.
  | .T23 => (compile ⟨registry, s0, [opMEASURE, opCHECK_SUFFICIENCY, opMODEL],
      Pred.factExists "Model"⟩).verdict = .PASS
  -- T24: iterative deepening returns the same, shortest, plan.
  | .T24 => minRepair registry modelGoal 4 s0 = some [opMEASURE, opCHECK_SUFFICIENCY]
  -- T25: an unreachable goal is not silently "repaired".
  | .T25 => searchRepair registry (.factExists "Teleported") 3 s0 = none

instance : DecidablePred TortureId25.claim := by
  intro t
  cases t
  · exact inferInstanceAs (Decidable (TortureId20.passed _))
  all_goals (unfold TortureId25.claim; infer_instance)

def TortureId25.passed (t : TortureId25) : Prop := t.claim

instance : DecidablePred TortureId25.passed := fun t => inferInstanceAs (Decidable t.claim)

theorem torture25_all_pass : ∀ t : TortureId25, t.passed := by decide

theorem torture25_card : Fintype.card TortureId25 = 25 := by decide

/-- The plan found at depth two is genuinely correct, not merely returned. -/
theorem t22_plan_correct :
    RepairCorrect registry modelGoal s0 [opMEASURE, opCHECK_SUFFICIENCY] :=
  (searchRepair_sound registry modelGoal 2 s0 _ (by decide)).1

/-- And no shorter plan exists. -/
theorem t22_plan_is_shortest :
    ∀ ops, RepairCorrect registry modelGoal s0 ops → ops.length ≤ 4 → 2 ≤ ops.length := by
  intro ops hc hlen
  have h := minRepair_length_le registry modelGoal 4 s0 [opMEASURE, opCHECK_SUFFICIENCY]
    (by decide) ops hc hlen
  simpa using h

end Polymath.OSA5
