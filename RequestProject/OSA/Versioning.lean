import RequestProject.OSA.Gold

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Versioning specifications

A new version of a specification *refines* the old one when every plan it
accepts was already accepted before.

* `Refines`, with `refines_refl` and `refines_trans`;
* `refines_of_budget_le` — tightening the effect budget refines;
* `refines_of_registry_subset` — shrinking the registry refines;
* `SpecVersion` and `versions_refine` — a chain of versions refines
  step by step.
-/

namespace Polymath.OSA

open Polymath.OSA4

/-- `sp'` refines `sp`: everything `sp'` accepts, `sp` already accepted. -/
def Refines (sp' sp : Spec) : Prop :=
  ∀ init chain, sp'.Satisfies init chain → sp.Satisfies init chain

theorem refines_refl (sp : Spec) : Refines sp sp := fun _ _ h => h

theorem refines_trans {a b c : Spec} (hab : Refines a b) (hbc : Refines b c) : Refines a c :=
  fun init chain h => hbc init chain (hab init chain h)

/-- Tightening the budget refines the specification. -/
theorem refines_of_budget_le (sp : Spec) {b : EffectLevel} (hb : b ≤ sp.budget) :
    Refines { sp with budget := b } sp :=
  fun _ _ h => ⟨h.1, h.2.1, le_trans h.2.2 hb⟩

/-- Shrinking the registry refines the specification. -/
theorem refines_of_registry_subset (sp : Spec) {reg : List Op}
    (hsub : ∀ n ∈ reg.map (·.name), n ∈ sp.registry.map (·.name)) :
    Refines { sp with registry := reg } sp :=
  fun _ _ h => ⟨chainOk_of_names_subset hsub h.1, h.2.1, h.2.2⟩

/-- A numbered version of a specification. -/
structure SpecVersion where
  /-- Version number. -/
  version : ℕ
  /-- The specification at this version. -/
  spec : Spec

/-- A release history refines step by step. -/
def IsRefinementChain : List SpecVersion → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => Refines a.spec b.spec ∧ IsRefinementChain (b :: t)

/-- Along a refinement chain, the first version refines the last. -/
theorem refines_of_chain : ∀ {l : List SpecVersion} {a b : SpecVersion},
    IsRefinementChain (a :: l ++ [b]) → Refines a.spec b.spec := by
  intro l
  induction l with
  | nil => intro a b h; exact h.1
  | cons c t ih =>
      intro a b h
      exact refines_trans h.1 (ih h.2)

/-- Tightening the budget of the deployment specification gives a proper
refinement: strictly fewer plans are accepted. -/
theorem deploy_budget_refinement_proper :
    Refines { Gold.deploySpec with budget := .E3 } Gold.deploySpec ∧
    ¬ Refines Gold.deploySpec { Gold.deploySpec with budget := .E3 } := by
  refine ⟨refines_of_budget_le _ (by decide), fun hcon => ?_⟩
  exact Gold.deployPlan_budget_too_tight (hcon s0 Gold.deployPlan Gold.deployPlan_satisfies)

end Polymath.OSA
