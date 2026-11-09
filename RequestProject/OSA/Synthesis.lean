import RequestProject.OSA.Gold
import RequestProject.OSA5.Repair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Synthesising plans for a specification

The OSA-5.0 search finds chains that establish a goal; a specification asks in
addition that the chain stay inside an effect budget.  Restricting the registry
to the operators the budget can afford turns the search into a *plan synthesiser*
for specifications, and transports its soundness, completeness and minimality
guarantees to `Spec.Satisfies`.

Main results:

* `Polymath.OSA.Spec.satisfies_iff_repairCorrect` — satisfaction of a
  specification is exactly correctness of a repair over the affordable registry;
* `Polymath.OSA.Spec.synthesize_sound` / `synthesize_complete` /
  `synthesize_isSome_iff` — the synthesiser returns a conforming plan whenever
  one exists within the fuel, and only conforming plans;
* `Polymath.OSA.Spec.synthesize_shortest` — the synthesised plan is a shortest
  conforming plan;
* `Polymath.OSA.Spec.synthesize_modelSpec` — the gold model specification is
  synthesised, and the answer is the gold plan.
-/

namespace Polymath.OSA

open Polymath.OSA4 Polymath.OSA5

/-- The operators of the registry whose effect the budget can afford. -/
def Spec.affordable (sp : Spec) : List Op :=
  sp.registry.filter (fun o => decide (o.effect ≤ sp.budget))

@[simp] theorem Spec.mem_affordable_iff (sp : Spec) (o : Op) :
    o ∈ sp.affordable ↔ o ∈ sp.registry ∧ o.effect ≤ sp.budget := by
  simp [Spec.affordable]

theorem Spec.affordable_subset (sp : Spec) {o : Op} (h : o ∈ sp.affordable) : o ∈ sp.registry :=
  ((sp.mem_affordable_iff o).1 h).1

/-- A chain built from affordable operators respects the budget. -/
theorem Spec.withinBudget_of_affordable (sp : Spec) {ops : List Op}
    (h : ∀ o ∈ ops, o ∈ sp.affordable) : WithinBudget sp.budget ops :=
  (withinBudget_iff sp.budget ops).2 fun o ho => ((sp.mem_affordable_iff o).1 (h o ho)).2

/-- A correct repair over the affordable registry is a conforming plan. -/
theorem Spec.satisfies_of_repairCorrect {sp : Spec} {init : KState} {ops : List Op}
    (h : RepairCorrect sp.affordable sp.goal init ops) : sp.Satisfies init ops := by
  obtain ⟨hreg, hadm, hgoal⟩ := h
  refine ⟨chainOk_of_chainAdmissible (fun o ho => sp.affordable_subset (hreg o ho)) hadm,
    hgoal, sp.withinBudget_of_affordable hreg⟩

/-- Conversely, a conforming plan drawn from the registry is a correct repair
over the affordable registry. -/
theorem Spec.repairCorrect_of_satisfies {sp : Spec} {init : KState} {ops : List Op}
    (hmem : ∀ o ∈ ops, o ∈ sp.registry) (h : sp.Satisfies init ops) :
    RepairCorrect sp.affordable sp.goal init ops := by
  obtain ⟨hok, hgoal, hbud⟩ := h
  refine ⟨fun o ho => ?_, chainAdmissible_of_chainOk hok, hgoal⟩
  exact (sp.mem_affordable_iff o).2 ⟨hmem o ho, (withinBudget_iff sp.budget ops).1 hbud o ho⟩

/-- Satisfaction of a specification and repair correctness over the affordable
registry are the same property, for plans drawn from the registry. -/
theorem Spec.satisfies_iff_repairCorrect {sp : Spec} {init : KState} {ops : List Op}
    (hmem : ∀ o ∈ ops, o ∈ sp.registry) :
    sp.Satisfies init ops ↔ RepairCorrect sp.affordable sp.goal init ops :=
  ⟨Spec.repairCorrect_of_satisfies hmem, Spec.satisfies_of_repairCorrect⟩

/-- Iterative-deepening plan synthesis for a specification. -/
def Spec.synthesize (sp : Spec) (init : KState) (fuel : ℕ) : Option (List Op) :=
  minRepair sp.affordable sp.goal fuel init

/-- **Soundness.** A synthesised plan conforms to the specification and is no
longer than the fuel. -/
theorem Spec.synthesize_sound {sp : Spec} {init : KState} {fuel : ℕ} {plan : List Op}
    (h : sp.synthesize init fuel = some plan) :
    sp.Satisfies init plan ∧ plan.length ≤ fuel := by
  obtain ⟨hc, hlen⟩ := minRepair_sound sp.affordable sp.goal fuel init plan h
  exact ⟨Spec.satisfies_of_repairCorrect hc, hlen⟩

/-- **Completeness.** If some conforming plan of length at most the fuel exists,
synthesis succeeds. -/
theorem Spec.synthesize_complete {sp : Spec} {init : KState} {fuel : ℕ} {plan : List Op}
    (hmem : ∀ o ∈ plan, o ∈ sp.registry) (h : sp.Satisfies init plan)
    (hlen : plan.length ≤ fuel) : (sp.synthesize init fuel).isSome := by
  rw [Spec.synthesize, minRepair_isSome_iff]
  exact searchRepair_complete sp.affordable sp.goal fuel init plan
    (Spec.repairCorrect_of_satisfies hmem h) hlen

/-- Synthesis succeeds exactly when a conforming plan within the fuel exists. -/
theorem Spec.synthesize_isSome_iff (sp : Spec) (init : KState) (fuel : ℕ) :
    (sp.synthesize init fuel).isSome ↔
      ∃ plan : List Op, (∀ o ∈ plan, o ∈ sp.registry) ∧ sp.Satisfies init plan ∧
        plan.length ≤ fuel := by
  constructor
  · intro h
    obtain ⟨plan, hplan⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hsat, hlen⟩ := Spec.synthesize_sound hplan
    have hreg := (minRepair_sound sp.affordable sp.goal fuel init plan hplan).1.1
    exact ⟨plan, fun o ho => sp.affordable_subset (hreg o ho), hsat, hlen⟩
  · rintro ⟨plan, hmem, hsat, hlen⟩
    exact Spec.synthesize_complete hmem hsat hlen

/-- **Minimality.** The synthesised plan is a shortest conforming plan within the
fuel. -/
theorem Spec.synthesize_shortest {sp : Spec} {init : KState} {fuel : ℕ} {plan : List Op}
    (h : sp.synthesize init fuel = some plan) (plan' : List Op)
    (hmem : ∀ o ∈ plan', o ∈ sp.registry) (hsat : sp.Satisfies init plan')
    (hlen : plan'.length ≤ fuel) : plan.length ≤ plan'.length :=
  minRepair_length_le sp.affordable sp.goal fuel init plan h plan'
    (Spec.repairCorrect_of_satisfies hmem hsat) hlen

/-- More fuel never loses a solution. -/
theorem Spec.synthesize_mono (sp : Spec) (init : KState) {n m : ℕ} (hnm : n ≤ m)
    (h : (sp.synthesize init n).isSome) : (sp.synthesize init m).isSome := by
  obtain ⟨plan, hmem, hsat, hlen⟩ := (sp.synthesize_isSome_iff init n).1 h
  exact (sp.synthesize_isSome_iff init m).2 ⟨plan, hmem, hsat, le_trans hlen hnm⟩

/-! ## The gold specification, synthesised -/

open Polymath.OSA.Gold

theorem Spec.synthesize_modelSpec : modelSpec.synthesize s0 3 = some modelPlan := by decide

theorem Spec.synthesize_modelSpec_satisfies : modelSpec.Satisfies s0 modelPlan :=
  (Spec.synthesize_sound Spec.synthesize_modelSpec).1

theorem Spec.synthesize_reportSpec_isSome : (reportSpec.synthesize s0 4).isSome := by decide

end Polymath.OSA
