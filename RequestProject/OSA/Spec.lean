import RequestProject.OSA4.Criteria

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA specifications

A *specification artifact* fixes what a plan must achieve and how much side
effect it is allowed to cause: a registry of admissible operators, a goal, and
an effect budget.

* `Spec` and `Spec.Satisfies` — the satisfaction relation, decidable;
* `Spec.satisfies_iff` — satisfaction unfolds into well-formedness, goal and
  budget;
* `Spec.satisfies_iff_pass` — satisfaction is exactly a `PASS` verdict of the
  OSA-4.0 compiler together with budget compliance.
-/

namespace Polymath.OSA

open Polymath.OSA4

/-- A specification: admissible operators, a goal to establish, an effect budget. -/
structure Spec where
  /-- Name of the specification. -/
  name : String
  /-- The operators a conforming plan may use. -/
  registry : List Op
  /-- The goal a conforming plan must establish. -/
  goal : Pred
  /-- The effect budget a conforming plan may not exceed. -/
  budget : EffectLevel

/-- The scenario a plan poses to the OSA-4.0 compiler. -/
def Spec.scenario (sp : Spec) (init : KState) (chain : List Op) : Scenario :=
  ⟨sp.registry, init, chain, sp.goal⟩

/-- A plan satisfies a specification when it is well-formed, establishes the
goal and respects the budget. -/
def Spec.Satisfies (sp : Spec) (init : KState) (chain : List Op) : Prop :=
  ChainOk sp.registry chain init ∧
    eval (execChain chain init) sp.goal = PT.TRUE_KNOWN ∧
    WithinBudget sp.budget chain

instance (sp : Spec) (init : KState) (chain : List Op) :
    Decidable (sp.Satisfies init chain) := by
  unfold Spec.Satisfies; infer_instance

theorem Spec.satisfies_iff (sp : Spec) (init : KState) (chain : List Op) :
    sp.Satisfies init chain ↔
      ChainOk sp.registry chain init ∧
        eval (execChain chain init) sp.goal = PT.TRUE_KNOWN ∧
        WithinBudget sp.budget chain := Iff.rfl

/-- Satisfaction is a `PASS` verdict plus budget compliance. -/
theorem Spec.satisfies_iff_pass (sp : Spec) (init : KState) (chain : List Op) :
    sp.Satisfies init chain ↔
      (compile (sp.scenario init chain)).verdict = .PASS ∧ WithinBudget sp.budget chain := by
  rw [Spec.Satisfies, compile_verdict_pass_iff]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨⟨h₁, h₂⟩, h₃⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact ⟨h₁, h₂, h₃⟩

/-- A satisfying plan meets the acceptance criteria of the compiler. -/
theorem Spec.criteria_of_satisfies {sp : Spec} {init : KState} {chain : List Op}
    (h : sp.Satisfies init chain) :
    Criterion.wellFormed.holds (sp.scenario init chain) ∧
      Criterion.achievesGoal.holds (sp.scenario init chain) :=
  ⟨h.1, h.2.1⟩

/-- A satisfying plan only uses declared operators. -/
theorem Spec.registered_of_satisfies {sp : Spec} {init : KState} {chain : List Op}
    (h : sp.Satisfies init chain) : ChainRegistered sp.registry chain :=
  chainRegistered_of_chainOk h.1

/-- A satisfying plan has every step enabled when it runs. -/
theorem Spec.chainEnabled_of_satisfies {sp : Spec} {init : KState} {chain : List Op}
    (h : sp.Satisfies init chain) : chainEnabled chain init :=
  law007_pass_chainEnabled _ _ _ h.1

end Polymath.OSA
