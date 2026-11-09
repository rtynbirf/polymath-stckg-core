import RequestProject.OSA5.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/-!
# OSA-5.0 Pipeline: compile, repair, recheck

The compiler of OSA-4.0 and the bounded repair search of OSA-5.0 are combined
into a single decision procedure.  Given a scenario and a fuel bound the
pipeline either

* certifies the chain as it stands (`PipelineOutcome.verified`),
* prefixes it with a repair plan and certifies the result
  (`PipelineOutcome.repaired`), or
* reports that no repair of length at most the fuel exists
  (`PipelineOutcome.irreparable`).

The three outcomes are exactly justified:

* `pipeline_verified_pass` and `pipeline_repaired_pass` — whatever the pipeline
  returns compiles to `PASS`;
* `pipeline_irreparable_iff` — the failure report is exact: it is returned
  precisely when no correct repair within the fuel bound exists;
* `pipeline_complete` — consequently the pipeline never gives up while a repair
  is available, and `pipeline_mono` says more fuel never hurts.
-/

namespace Polymath.OSA5

open Polymath.OSA4

/-- What the pipeline can report. -/
inductive PipelineOutcome
  | verified (chain : List Op)
  | repaired (plan chain : List Op)
  | irreparable
  deriving DecidableEq, Repr, Inhabited

/-- Compile the scenario; on failure look for a repair prefix within the fuel
bound. -/
def pipeline (sc : Scenario) (fuel : ℕ) : PipelineOutcome :=
  if (compile sc).verdict = Verdict.PASS then
    .verified sc.chain
  else
    match searchRepair sc.registry (chainPred sc.chain sc.goal) fuel sc.init with
    | some plan => .repaired plan sc.chain
    | none => .irreparable

/-- A verified outcome means the original chain already compiles. -/
theorem pipeline_verified_pass {sc : Scenario} {fuel : ℕ} {chain : List Op}
    (h : pipeline sc fuel = .verified chain) :
    chain = sc.chain ∧ (compile sc).verdict = Verdict.PASS := by
  unfold pipeline at h
  split_ifs at h with hp
  · exact ⟨by simpa using h.symm, hp⟩
  · cases hs : searchRepair sc.registry (chainPred sc.chain sc.goal) fuel sc.init with
    | none => rw [hs] at h; simp at h
    | some ops => rw [hs] at h; simp at h

/-- A repaired outcome yields a chain that compiles to `PASS`. -/
theorem pipeline_repaired_pass {sc : Scenario} {fuel : ℕ} {plan chain : List Op}
    (hchain : ∀ o ∈ sc.chain, o ∈ sc.registry)
    (h : pipeline sc fuel = .repaired plan chain) :
    chain = sc.chain ∧
      (compile ⟨sc.registry, sc.init, plan ++ sc.chain, sc.goal⟩).verdict = Verdict.PASS := by
  unfold pipeline at h
  split_ifs at h with hp
  cases hs : searchRepair sc.registry (chainPred sc.chain sc.goal) fuel sc.init with
  | none => rw [hs] at h; simp at h
  | some ops =>
      rw [hs] at h
      simp only [PipelineOutcome.repaired.injEq] at h
      obtain ⟨hplan, hch⟩ := h
      subst hplan
      exact ⟨hch.symm, repaired_chain_compiles_pass sc.registry sc.chain sc.goal fuel sc.init ops
        hchain hs⟩

/-- The pipeline gives up exactly when no repair within the fuel bound exists. -/
theorem pipeline_irreparable_iff (sc : Scenario) (fuel : ℕ) :
    pipeline sc fuel = .irreparable ↔
      (compile sc).verdict ≠ Verdict.PASS ∧
        ¬ ∃ plan, RepairCorrect sc.registry (chainPred sc.chain sc.goal) sc.init plan ∧
          plan.length ≤ fuel := by
  unfold pipeline
  split_ifs with hp
  · constructor
    · intro h; simp at h
    · rintro ⟨hne, -⟩; exact absurd hp hne
  · cases hs : searchRepair sc.registry (chainPred sc.chain sc.goal) fuel sc.init with
    | some ops =>
      constructor
      · intro h; simp at h
      · rintro ⟨-, hno⟩
        refine absurd ?_ hno
        exact (searchRepair_isSome_iff sc.registry (chainPred sc.chain sc.goal) fuel sc.init).1
          (by rw [hs]; rfl)
    | none =>
      refine ⟨fun _ => ⟨hp, ?_⟩, fun _ => rfl⟩
      intro hex
      have hsome := (searchRepair_isSome_iff sc.registry (chainPred sc.chain sc.goal)
        fuel sc.init).2 hex
      rw [hs] at hsome
      simp at hsome

/-- If a repair exists within the fuel bound the pipeline produces one. -/
theorem pipeline_complete (sc : Scenario) (fuel : ℕ) {plan : List Op}
    (hc : RepairCorrect sc.registry (chainPred sc.chain sc.goal) sc.init plan)
    (hlen : plan.length ≤ fuel) :
    pipeline sc fuel ≠ .irreparable := by
  intro h
  exact ((pipeline_irreparable_iff sc fuel).1 h).2 ⟨plan, hc, hlen⟩

/-- More fuel never turns a success into a failure. -/
theorem pipeline_mono (sc : Scenario) {n m : ℕ} (hnm : n ≤ m)
    (h : pipeline sc n ≠ .irreparable) : pipeline sc m ≠ .irreparable := by
  intro hm
  obtain ⟨hp, hno⟩ := (pipeline_irreparable_iff sc m).1 hm
  refine h ((pipeline_irreparable_iff sc n).2 ⟨hp, ?_⟩)
  rintro ⟨plan, hc, hlen⟩
  exact hno ⟨plan, hc, le_trans hlen hnm⟩

/-! ## The pipeline on the OSA torture registry -/

/-- The failing scenario "produce a model with no preparation". -/
def modelScenario : Scenario := ⟨registry, s0, [opMODEL], Pred.factExists "Model"⟩

/-- Straight modelling is rejected by the compiler. -/
theorem modelScenario_not_pass : (compile modelScenario).verdict ≠ Verdict.PASS := by decide

/-- With two units of fuel the pipeline repairs it. -/
theorem pipeline_modelScenario :
    pipeline modelScenario 2 = .repaired [opMEASURE, opCHECK_SUFFICIENCY] [opMODEL] := by
  decide

/-- One unit of fuel is not enough. -/
theorem pipeline_modelScenario_one : pipeline modelScenario 1 = .irreparable := by decide

/-- The repaired chain the pipeline proposes really does compile. -/
theorem pipeline_modelScenario_pass :
    (compile ⟨registry, s0, [opMEASURE, opCHECK_SUFFICIENCY] ++ [opMODEL],
      Pred.factExists "Model"⟩).verdict = Verdict.PASS :=
  (pipeline_repaired_pass (sc := modelScenario) (fuel := 2)
    (by decide) pipeline_modelScenario).2

end Polymath.OSA5
