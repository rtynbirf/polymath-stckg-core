import RequestProject.OSA.Gold

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

/-!
# The conformance checker

`conforms` decides satisfaction, and `selectPlan` searches a list of candidate
plans for a conforming one.  Both are proved correct:

* `conforms_eq_true_iff` — the checker is sound and complete;
* `selectPlan_sound` — a selected plan conforms;
* `selectPlan_complete` — if a conforming plan is offered, one is selected;
* `selectPlan_isSome_iff` — the exact criterion.
-/

namespace Polymath.OSA

open Polymath.OSA4

/-- Decide whether a plan conforms to a specification. -/
def conforms (sp : Spec) (init : KState) (chain : List Op) : Bool :=
  decide (sp.Satisfies init chain)

theorem conforms_eq_true_iff (sp : Spec) (init : KState) (chain : List Op) :
    conforms sp init chain = true ↔ sp.Satisfies init chain := by
  simp [conforms]

/-- Search a list of candidate plans for a conforming one. -/
def selectPlan (sp : Spec) (init : KState) (candidates : List (List Op)) : Option (List Op) :=
  candidates.find? (conforms sp init)

theorem selectPlan_sound {sp : Spec} {init : KState} {candidates : List (List Op)}
    {chain : List Op} (h : selectPlan sp init candidates = some chain) :
    sp.Satisfies init chain ∧ chain ∈ candidates := by
  have hmem := List.mem_of_find?_eq_some h
  have hprop := List.find?_some h
  exact ⟨(conforms_eq_true_iff sp init chain).1 hprop, hmem⟩

theorem selectPlan_complete {sp : Spec} {init : KState} {candidates : List (List Op)}
    {chain : List Op} (hmem : chain ∈ candidates) (hsat : sp.Satisfies init chain) :
    (selectPlan sp init candidates).isSome := by
  rw [selectPlan, Option.isSome_iff_exists]
  rcases hfind : candidates.find? (conforms sp init) with _ | c
  · rw [List.find?_eq_none] at hfind
    exact absurd ((conforms_eq_true_iff sp init chain).2 hsat) (by simpa using hfind chain hmem)
  · exact ⟨c, rfl⟩

/-- The search succeeds exactly when some candidate conforms. -/
theorem selectPlan_isSome_iff (sp : Spec) (init : KState) (candidates : List (List Op)) :
    (selectPlan sp init candidates).isSome ↔ ∃ chain ∈ candidates, sp.Satisfies init chain := by
  constructor
  · intro h
    obtain ⟨chain, hchain⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hsat, hmem⟩ := selectPlan_sound hchain
    exact ⟨chain, hmem, hsat⟩
  · rintro ⟨chain, hmem, hsat⟩
    exact selectPlan_complete hmem hsat

/-- A worked example: the gold plan is selected out of a list of candidates. -/
theorem selectPlan_gold :
    selectPlan Gold.modelSpec s0 [[opMEASURE], [opMEASURE, opMODEL], Gold.modelPlan] =
      some Gold.modelPlan := by decide

end Polymath.OSA
