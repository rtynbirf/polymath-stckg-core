import RequestProject.OSA.Spec
import RequestProject.OSA4.Effects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Structural theorems about specification satisfaction

* `chainOk_append_iff` — well-formedness splits along concatenation;
* `Spec.satisfies_budget_mono` — a satisfying plan still satisfies a looser
  budget;
* `Spec.satisfies_registry_mono` — enlarging the registry preserves
  satisfaction;
* `Spec.satisfies_append_nonDestructive` — appending non-destructive steps to a
  satisfying plan keeps a fact goal established;
* `Spec.satisfies_nil_iff` — the empty plan satisfies exactly the goals that
  already hold.
-/

namespace Polymath.OSA

open Polymath.OSA4

theorem chainOk_append_iff (reg x y : List Op) (s : KState) :
    ChainOk reg (x ++ y) s ↔ ChainOk reg x s ∧ ChainOk reg y (execChain x s) := by
  induction x generalizing s with
  | nil => simp
  | cons o t ih =>
      simp only [List.cons_append, ChainOk_cons, ih, execChain_cons, and_assoc]

/-- Well-formedness only refers to the registry through the operator names. -/
theorem chainOk_of_names_subset {reg reg' ops : List Op} {s : KState}
    (hsub : ∀ n ∈ reg.map (·.name), n ∈ reg'.map (·.name)) (h : ChainOk reg ops s) :
    ChainOk reg' ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons o t ih =>
      exact ⟨⟨hsub _ h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩, ih h.2⟩

/-- Loosening the budget preserves satisfaction. -/
theorem Spec.satisfies_budget_mono {sp : Spec} {init : KState} {chain : List Op}
    (h : sp.Satisfies init chain) {b : EffectLevel} (hb : sp.budget ≤ b) :
    Spec.Satisfies { sp with budget := b } init chain :=
  ⟨h.1, h.2.1, le_trans h.2.2 hb⟩

/-- Enlarging the registry preserves satisfaction. -/
theorem Spec.satisfies_registry_mono {sp : Spec} {init : KState} {chain : List Op}
    (h : sp.Satisfies init chain) {reg : List Op}
    (hsub : ∀ n ∈ sp.registry.map (·.name), n ∈ reg.map (·.name)) :
    Spec.Satisfies { sp with registry := reg } init chain :=
  ⟨chainOk_of_names_subset hsub h.1, h.2.1, h.2.2⟩

/-- The empty plan satisfies exactly the goals that already hold in the initial
state. -/
theorem Spec.satisfies_nil_iff (sp : Spec) (init : KState) :
    sp.Satisfies init [] ↔ eval init sp.goal = PT.TRUE_KNOWN := by
  constructor
  · intro h; simpa using h.2.1
  · intro h
    exact ⟨trivial, by simpa using h, by simp [WithinBudget]⟩

/-- Appending non-destructive, in-budget, well-formed steps to a satisfying plan
keeps a fact goal established. -/
theorem Spec.satisfies_append_nonDestructive {sp : Spec} {init : KState}
    {chain extra : List Op} {f : FactId} (hgoal : sp.goal = .factExists f)
    (h : sp.Satisfies init chain)
    (hok : ChainOk sp.registry extra (execChain chain init))
    (hnd : ∀ o ∈ extra, NonDestructive o)
    (hb : WithinBudget sp.budget extra) :
    sp.Satisfies init (chain ++ extra) := by
  refine ⟨(chainOk_append_iff _ _ _ _).2 ⟨h.1, hok⟩, ?_, ?_⟩
  · have hstatus : (execChain chain init).factStatus f = PT.TRUE_KNOWN := by
      have := h.2.1
      rw [hgoal] at this
      simpa [eval] using this
    rw [hgoal, execChain_append]
    simpa [eval] using factStatus_execChain_of_nonDestructive hnd _ hstatus
  · exact (withinBudget_append_iff _ _ _).2 ⟨h.2.2, hb⟩

/-- Satisfaction transfers along a change of specification that keeps the
registry, the goal and the budget. -/
theorem Spec.satisfies_congr {sp sp' : Spec} (hreg : sp.registry = sp'.registry)
    (hgoal : sp.goal = sp'.goal) (hbud : sp.budget = sp'.budget)
    {init : KState} {chain : List Op} (h : sp.Satisfies init chain) :
    sp'.Satisfies init chain := by
  refine ⟨hreg ▸ h.1, hgoal ▸ h.2.1, hbud ▸ h.2.2⟩

end Polymath.OSA
