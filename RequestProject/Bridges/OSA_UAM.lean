import RequestProject.OSA4.Compiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: OSA operator chains as a free monoid action

Operator chains form the free monoid on the registry, and execution is a monoid
action of that free monoid on `KState`: `execAction_hom` is the homomorphism
law.  The set of chains that compile to `PASS` is a language over the alphabet
of operators (`opLanguage`), and `ChainEquiv` — "same resulting state, same
well-formedness" — is a right congruence refining the Myhill–Nerode relation
`GoalEquiv` of that language.
-/

namespace Polymath.Bridges

open Polymath.OSA4

/-! ## Execution is a free monoid action -/

/-- The action of a chain of operators on states. -/
def execAction (ops : List Op) : KState → KState := execChain ops

@[simp] theorem execAction_nil : execAction [] = id := rfl

@[simp] theorem execAction_cons (o : Op) (t : List Op) :
    execAction (o :: t) = execAction t ∘ o.exec := rfl

/-- Execution is a homomorphism from the free monoid of chains to the monoid of
state transformers (acting on the right). -/
theorem execAction_hom (x y : List Op) :
    execAction (x ++ y) = execAction y ∘ execAction x := by
  funext s
  simpa [execAction, Function.comp] using execChain_append x y s

/-- The homomorphism law, applied to a state. -/
theorem execAction_append_apply (x y : List Op) (s : KState) :
    execAction (x ++ y) s = execAction y (execAction x s) := by
  rw [execAction_hom]; rfl

/-! ## Well-formedness splits along concatenation -/

theorem chainOk_append (reg x y : List Op) (s : KState) :
    ChainOk reg (x ++ y) s ↔ ChainOk reg x s ∧ ChainOk reg y (execChain x s) := by
  induction x generalizing s with
  | nil => simp
  | cons o t ih => simp [ih, and_assoc]

/-! ## The language of successful chains -/

/-- The chains that are well-formed in `s` and establish `goal`. -/
def opLanguage (reg : List Op) (s : KState) (goal : Pred) : Set (List Op) :=
  {ops | ChainOk reg ops s ∧ eval (execChain ops s) goal = PT.TRUE_KNOWN}

/-- Membership in `opLanguage` is exactly a `PASS` verdict of the compiler. -/
theorem mem_opLanguage_iff_pass (reg : List Op) (s : KState) (goal : Pred) (ops : List Op) :
    ops ∈ opLanguage reg s goal ↔
      (compile ⟨reg, s, ops, goal⟩).verdict = Verdict.PASS :=
  (compile_verdict_pass_iff ⟨reg, s, ops, goal⟩).symm

/-- A chain in the language compiles to `PASS`. -/
theorem mem_opLanguage_compiles_pass {reg : List Op} {s : KState} {goal : Pred} {ops : List Op}
    (h : ops ∈ opLanguage reg s goal) :
    (compile ⟨reg, s, ops, goal⟩).verdict = Verdict.PASS :=
  (mem_opLanguage_iff_pass reg s goal ops).1 h

/-! ## Chain equivalence and the Nerode relation -/

/-- Two chains are equivalent when they reach the same state and are jointly
well-formed or jointly ill-formed. -/
def ChainEquiv (reg : List Op) (s : KState) (x y : List Op) : Prop :=
  execChain x s = execChain y s ∧ (ChainOk reg x s ↔ ChainOk reg y s)

theorem chainEquiv_refl (reg : List Op) (s : KState) (x : List Op) :
    ChainEquiv reg s x x := ⟨rfl, Iff.rfl⟩

theorem chainEquiv_symm {reg : List Op} {s : KState} {x y : List Op}
    (h : ChainEquiv reg s x y) : ChainEquiv reg s y x := ⟨h.1.symm, h.2.symm⟩

theorem chainEquiv_trans {reg : List Op} {s : KState} {x y z : List Op}
    (h₁ : ChainEquiv reg s x y) (h₂ : ChainEquiv reg s y z) : ChainEquiv reg s x z :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- `ChainEquiv` is a right congruence: it is preserved by appending a suffix. -/
theorem chainEquiv_right_congruence {reg : List Op} {s : KState} {x y : List Op}
    (h : ChainEquiv reg s x y) (z : List Op) : ChainEquiv reg s (x ++ z) (y ++ z) := by
  refine ⟨?_, ?_⟩
  · rw [execChain_append, execChain_append, h.1]
  · rw [chainOk_append, chainOk_append, h.1]
    exact and_congr_left' h.2

/-- The Myhill–Nerode relation of the language `opLanguage reg s goal`. -/
def GoalEquiv (reg : List Op) (s : KState) (goal : Pred) (x y : List Op) : Prop :=
  ∀ z : List Op, (x ++ z ∈ opLanguage reg s goal ↔ y ++ z ∈ opLanguage reg s goal)

/-- Chain equivalence refines the Nerode relation of the goal language. -/
theorem chainEquiv_refines_nerode {reg : List Op} {s : KState} {goal : Pred} {x y : List Op}
    (h : ChainEquiv reg s x y) : GoalEquiv reg s goal x y := by
  intro z
  have hz := chainEquiv_right_congruence h z
  simp only [opLanguage, Set.mem_setOf_eq, hz.1, hz.2]

/-- The Nerode relation is an equivalence relation. -/
theorem goalEquiv_refl (reg : List Op) (s : KState) (goal : Pred) (x : List Op) :
    GoalEquiv reg s goal x x := fun _ => Iff.rfl

theorem goalEquiv_symm {reg : List Op} {s : KState} {goal : Pred} {x y : List Op}
    (h : GoalEquiv reg s goal x y) : GoalEquiv reg s goal y x := fun z => (h z).symm

theorem goalEquiv_trans {reg : List Op} {s : KState} {goal : Pred} {x y z : List Op}
    (h₁ : GoalEquiv reg s goal x y) (h₂ : GoalEquiv reg s goal y z) :
    GoalEquiv reg s goal x z := fun w => (h₁ w).trans (h₂ w)

/-- The Nerode relation is itself a right congruence. -/
theorem goalEquiv_right_congruence {reg : List Op} {s : KState} {goal : Pred} {x y : List Op}
    (h : GoalEquiv reg s goal x y) (z : List Op) : GoalEquiv reg s goal (x ++ z) (y ++ z) := by
  intro w
  simpa [List.append_assoc] using h (z ++ w)

end Polymath.Bridges
