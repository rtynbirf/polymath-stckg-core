import RequestProject.STCKG.Composition
import RequestProject.STCKG.IndexedFamily
import RequestProject.STCKG.EvolutionAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Foundational Audit, assembled

This module collects the ten audit hypotheses H1–H10 of the directive into one
enumerated type, attaches to each the *formal statement that was actually
proved* about it, and proves them all (`foundational_audit_holds`).

The verdicts are deliberately modest.  Each `verdict` is a Lean statement about
the ST-CKG kernel defined in this directory, not about the informal architecture
it models: a proof of `foundational_audit_holds` establishes exactly the listed
formal statements and nothing more.
-/

namespace Polymath.STCKG

open Polymath Polymath.Dependency Polymath.Verification Polymath.Evolution

/-- The ten hypotheses of the Foundational Audit. -/
inductive AuditHypothesis
  | H1 | H2 | H3 | H4 | H5 | H6 | H7 | H8 | H9 | H10
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Short title of each hypothesis. -/
def AuditHypothesis.title : AuditHypothesis → String
  | .H1 => "Referential unity"
  | .H2 => "Referent / View / Avatar"
  | .H3 => "Correspondence deserves a type"
  | .H4 => "Two-axis model"
  | .H5 => "Category applicability"
  | .H6 => "Grothendieck-fibration candidate"
  | .H7 => "Claim discipline"
  | .H8 => "Evolution"
  | .H9 => "Invariants"
  | .H10 => "Architectural novelty"

/-- The formal statement established for each hypothesis. -/
def AuditHypothesis.verdict : AuditHypothesis → Prop
  | .H1 =>
      (∃ a b : Avatar, CoRefers a b ∧ a.representation ≠ b.representation) ∧
      (∃ a b : Avatar, a.representation = b.representation ∧ ¬ CoRefers a b)
  | .H2 =>
      (∃ a b : Avatar, a.referent = b.referent ∧ a.view = b.view ∧ a ≠ b) ∧
      (avatarsAt ∅ feedback .physics).card = 0 ∧
      (avatarsAt {feedbackPhysics, feedbackBiology} feedback .physics).card = 1 ∧
      (avatarsAt {feedbackPhysics, feedbackPhysics', feedbackBiology} feedback .physics).card = 2
  | .H3 =>
      ∃ c₁ c₂ : Correspondence, c₁.source = c₂.source ∧ c₁.target = c₂.target ∧ c₁ ≠ c₂
  | .H4 =>
      Function.Surjective Correspondence.axes ∧
      Fintype.card (SemanticStrength × FormalRealization) = 32
  | .H5 =>
      Transitive Precedes ∧ ¬ Transitive Overlaps ∧
      (∃ C : Event → Event → Prop, (∀ e f, C e f → Precedes e f) ∧ ¬ Transitive C) ∧
      longPath ≠ shortPath
  | .H6 =>
      (∀ S : Set Avatar, HasLifts (viewProjection S) ↔ ViewComplete S) ∧
      ¬ HasLifts (viewProjection singletonStore) ∧
      HasLifts (viewProjection completedStore)
  | .H7 =>
      (∃ c₁ c₂ : Claim, ∃ k : Correspondence,
        c₁.subject = .correspondenceSubject k ∧ c₂.subject = .correspondenceSubject k ∧
        c₁ ≠ c₂) ∧
      (∃ c : Claim, Settled c ∧ c.epistemic = .conjecture)
  | .H8 =>
      (∀ g h : KnowledgeGraph, Extends g h → Extends h g → g = h) ∧
      (∃ (g : KnowledgeGraph) (o : KnowledgeObject) (ho : o ∈ g.objects) (m : Maturity),
        ¬ Extends g (promote g ho m)) ∧
      (∀ g h : KnowledgeGraph, Evolves g h → g.ids ⊆ h.ids)
  | .H9 =>
      Preserves PromoteStepRel Acyclic ∧
      ¬ Preserves Extends Acyclic ∧
      ¬ Preserves PromoteStepRel (fun g => Certified g Maturity.validated)
  | .H10 =>
      Function.Injective Avatar.split ∧
      ¬ Function.Injective EvidenceProfile.toBelief ∧
      ¬ Function.Surjective EvidenceProfile.toBelief

/-- **The Foundational Audit.**  Every one of the ten hypotheses has been given
a precise formal reading, and that reading is proved. -/
theorem foundational_audit_holds : ∀ h : AuditHypothesis, h.verdict := by
  intro h
  cases h with
  | H1 => exact ⟨coRefers_not_same_representation, same_representation_not_coRefers⟩
  | H2 =>
    exact ⟨avatar_not_determined_by_referent_view, avatarsAt_card_zero, avatarsAt_card_one,
      avatarsAt_card_two⟩
  | H3 => exact correspondence_not_determined_by_endpoints
  | H4 => exact ⟨axes_surjective, axes_card⟩
  | H5 =>
    exact ⟨precedes_trans, overlaps_not_transitive, causes_transitivity_not_automatic,
      two_distinct_concept_paths⟩
  | H6 =>
    exact ⟨hasLifts_iff_viewComplete, avatarStore_not_hasLifts, completedStore_hasLifts⟩
  | H7 =>
    refine ⟨claim_not_correspondence, ?_⟩
    obtain ⟨c, hs, he, -, -⟩ := settled_not_true
    exact ⟨c, hs, he⟩
  | H8 =>
    exact ⟨fun _ _ h₁ h₂ => extends_antisymm h₁ h₂, promote_not_extends,
      fun _ _ h => evolves_ids_subset h⟩
  | H9 =>
    exact ⟨promote_preserves_acyclic, extends_not_preserves_acyclic,
      promote_not_preserves_certified⟩
  | H10 =>
    exact ⟨avatar_to_core_injective, toBelief_not_injective, toBelief_not_surjective⟩

theorem audit_card : Fintype.card AuditHypothesis = 10 := by decide

/-! ## The minimal kernel (§39)

The kernel that survived the audit consists of exactly seven types, together
with two bridges to the existing verified core and one formal relation.  Nothing
else was needed, and the elements that failed their test — a universal
`Invariant` type, an `Evolution` functor, a global fibration — were not
introduced. -/

/-- The elements of the minimal ST-CKG kernel that survived the audit. -/
inductive KernelElement
  | referent | view | avatar | correspondence | evidence | provenance | claim
  deriving DecidableEq, Repr, Inhabited, Fintype

theorem kernel_card : Fintype.card KernelElement = 7 := by decide

/-- Each kernel element is either bridged to the existing core or justified by
an explicit counterexample showing that no existing type subsumes it. -/
def KernelElement.justification : KernelElement → Prop
  | .referent => ∀ a b : Avatar, CoRefers a b ↔ a.referent = b.referent
  | .view => ∀ v : View, ViewLe v v
  | .avatar => Function.Injective Avatar.split
  | .correspondence =>
      ∃ c₁ c₂ : Correspondence, c₁.source = c₂.source ∧ c₁.target = c₂.target ∧ c₁ ≠ c₂
  | .evidence =>
      ¬ Function.Injective EvidenceProfile.toBelief ∧
      ¬ Function.Surjective EvidenceProfile.toBelief
  | .provenance => ∃ c : Claim, Settled c ∧ c.epistemic = .conjecture
  | .claim =>
      ∀ (base : Finset ℕ) (cs : List Claim) (c : Claim), c ∈ cs → c.assumptions = [] →
        Polymath.ProofGraph.Derivable (toProofs base cs) c.id

theorem kernel_justified : ∀ e : KernelElement, e.justification := by
  intro e
  cases e with
  | referent => exact fun _ _ => Iff.rfl
  | view => exact viewLe_refl
  | avatar => exact avatar_to_core_injective
  | correspondence => exact correspondence_not_determined_by_endpoints
  | evidence => exact ⟨toBelief_not_injective, toBelief_not_surjective⟩
  | provenance =>
    obtain ⟨c, hs, he, -, -⟩ := settled_not_true
    exact ⟨c, hs, he⟩
  | claim => exact fun _ _ _ hc h => derivable_of_no_assumptions hc h

end Polymath.STCKG
