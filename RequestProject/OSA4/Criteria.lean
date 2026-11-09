import RequestProject.OSA4.Effects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Acceptance criteria

A scenario is judged against a handful of criteria: is every operator declared,
is every step enabled when it runs, is authorization in place, does the chain
respect its effect budget, and does it establish the goal?

* `ChainRegistered`, `ChainAuthorized` — the declarative forms of the registry
  and authorization checks, both implied by well-formedness
  (`chainRegistered_of_chainOk`, `chainAuthorized_of_chainOk`);
* `Criterion` and `Criterion.holds` — the criteria as data, each decidable;
* `pass_iff_criteria` — the compiler answers `PASS` exactly when the
  well-formedness and goal criteria hold.
-/

namespace Polymath.OSA4

/-- Every operator of the chain is declared in the registry. -/
def ChainRegistered (reg ops : List Op) : Prop := ∀ o ∈ ops, o.name ∈ reg.map (·.name)

/-- Authorization is in place for every step of the chain, in the state the step
is reached in. -/
def ChainAuthorized : List Op → KState → Prop
  | [], _ => True
  | o :: t, s =>
      (o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN) ∧
        ChainAuthorized t (o.exec s)

@[simp] theorem chainAuthorized_nil (s : KState) : ChainAuthorized [] s := trivial

@[simp] theorem chainAuthorized_cons (o : Op) (t : List Op) (s : KState) :
    ChainAuthorized (o :: t) s ↔
      (o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN) ∧
        ChainAuthorized t (o.exec s) := Iff.rfl

theorem chainRegistered_of_chainOk {reg ops : List Op} {s : KState}
    (h : ChainOk reg ops s) : ChainRegistered reg ops := by
  induction ops generalizing s with
  | nil => intro o ho; cases ho
  | cons o t ih =>
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact h.1.1
      · exact ih h.2 p hp'

theorem chainAuthorized_of_chainOk {reg ops : List Op} {s : KState}
    (h : ChainOk reg ops s) : ChainAuthorized ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons o t ih => exact ⟨h.1.2.2.2, ih h.2⟩

/-- Well-formedness of a chain is decidable, because the compiler decides it. -/
instance (reg ops : List Op) (s : KState) : Decidable (ChainOk reg ops s) :=
  decidable_of_iff _ (compileGo_eq_none_iff reg ops s)

/-! ## Criteria as data -/

/-- The acceptance criteria a scenario can be judged against. -/
inductive Criterion
  | wellFormed
  | registered
  | authorized
  | achievesGoal
  | withinBudget (b : EffectLevel)
  deriving DecidableEq, Repr, Inhabited

/-- The meaning of each criterion. -/
def Criterion.holds : Criterion → Scenario → Prop
  | .wellFormed, sc => ChainOk sc.registry sc.chain sc.init
  | .registered, sc => ChainRegistered sc.registry sc.chain
  | .authorized, sc => ChainAuthorized sc.chain sc.init
  | .achievesGoal, sc => eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN
  | .withinBudget b, sc => WithinBudget b sc.chain

instance decChainRegistered (reg ops : List Op) : Decidable (ChainRegistered reg ops) := by
  unfold ChainRegistered; infer_instance

instance decChainAuthorized : ∀ (ops : List Op) (s : KState), Decidable (ChainAuthorized ops s)
  | [], _ => isTrue trivial
  | o :: t, s => by
      have := decChainAuthorized t (o.exec s)
      rw [chainAuthorized_cons]
      infer_instance

instance (c : Criterion) (sc : Scenario) : Decidable (c.holds sc) := by
  cases c <;> unfold Criterion.holds <;> infer_instance

/-- Well-formedness subsumes the registry and authorization criteria. -/
theorem wellFormed_implies (sc : Scenario) (h : Criterion.wellFormed.holds sc) :
    Criterion.registered.holds sc ∧ Criterion.authorized.holds sc :=
  ⟨chainRegistered_of_chainOk h, chainAuthorized_of_chainOk h⟩

/-- The compiler answers `PASS` exactly when the two headline criteria hold. -/
theorem pass_iff_criteria (sc : Scenario) :
    (compile sc).verdict = .PASS ↔
      Criterion.wellFormed.holds sc ∧ Criterion.achievesGoal.holds sc :=
  compile_verdict_pass_iff sc

/-- A passing scenario meets the registry and authorization criteria too. -/
theorem pass_implies_registered_authorized (sc : Scenario)
    (h : (compile sc).verdict = .PASS) :
    Criterion.registered.holds sc ∧ Criterion.authorized.holds sc :=
  wellFormed_implies sc ((pass_iff_criteria sc).1 h).1

/-- Budget compliance only depends on the chain, so it survives truncation. -/
theorem withinBudget_holds_of_sublist {sc sc' : Scenario} {b : EffectLevel}
    (hsub : sc'.chain.Sublist sc.chain) (h : (Criterion.withinBudget b).holds sc) :
    (Criterion.withinBudget b).holds sc' :=
  WithinBudget.sublist hsub h

end Polymath.OSA4
