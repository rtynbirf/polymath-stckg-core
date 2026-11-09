import RequestProject.STCKG.Correspondence
import RequestProject.ProofGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ST-CKG claims and their bridge to the existing proof graph

Audit question H7 (claim discipline, §7).

A `Claim` is a separate type.  It never *becomes* a morphism, a relation or a
correspondence; at most it records that one was asserted, and it carries its own
epistemic status, formal status, evidence, provenance and lifecycle state — five
independent dimensions (§3.1).

Formal findings:

* `claim_not_correspondence` — two distinct claims may be about one and the same
  correspondence, so claims are not correspondences;
* `settled_not_true` — a claim can be `SETTLED` (project lifecycle) while its
  epistemic status is only `CONJECTURE`, and simultaneously Lean-verified: the
  three dimensions do not collapse;
* `statuses_independent` — every combination of lifecycle state and epistemic
  status is realizable;
* **bridge**: `toProofs` interprets a claim set as a `Polymath.ProofGraph.Proofs`
  object, and `derivable_of_assumptions_derivable` transports derivability.  The
  bridge is *structural only*: `derivable_does_not_imply_established` shows that
  graph-derivability says nothing about the epistemic status of the claim.
-/

namespace Polymath.STCKG

open Polymath.ProofGraph

/-! ## The claim type -/

/-- What a claim can be about.  A claim about a correspondence is *not* the
correspondence. -/
inductive ClaimSubject
  | referentSubject (r : Referent)
  | avatarSubject (a : Avatar)
  | correspondenceSubject (c : Correspondence)
  | leanDeclaration (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Operational lifecycle of a claim inside the project (§7). -/
inductive ClaimState
  | proposed | active | contested | refuted | retired
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Epistemic status of a claim (§3.1); independent of its lifecycle state and
of its formal status. -/
inductive EpistemicStatus
  | unknown | conjecture | supported | derived | established | refutedStatus
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A claim: a typed assertion with its own evidence, provenance and status. -/
structure Claim where
  /-- Identifier of the claim. -/
  id : ℕ
  /-- What the claim is about. -/
  subject : ClaimSubject
  /-- What is asserted. -/
  predicate : String
  /-- The context in which it is asserted. -/
  context : String
  /-- Identifiers of the claims assumed. -/
  assumptions : List ℕ
  /-- Evidence for the claim. -/
  evidence : EvidenceProfile
  /-- Where the claim came from. -/
  provenance : Provenance
  /-- Lean declaration realizing the claim, if any. -/
  formalization : Option String
  /-- Operational lifecycle state. -/
  state : ClaimState
  /-- Epistemic status. -/
  epistemic : EpistemicStatus
  deriving DecidableEq, Repr, Inhabited

/-- A minimal claim about a correspondence. -/
def sampleCorrespondence : Correspondence :=
  ⟨feedbackPhysics, feedbackBiology, .structural, .none, EvidenceProfile.blank, auditProv⟩

/-- One claim about `sampleCorrespondence`. -/
def claimA : Claim :=
  ⟨0, .correspondenceSubject sampleCorrespondence, "the correspondence is structural", "audit",
    [], EvidenceProfile.blank, auditProv, none, .proposed, .conjecture⟩

/-- A second, different claim about the *same* correspondence. -/
def claimB : Claim :=
  ⟨1, .correspondenceSubject sampleCorrespondence, "the correspondence is not functorial",
    "audit", [], EvidenceProfile.blank, auditProv, none, .contested, .unknown⟩

/-- **H7 / §7.** A claim is not its subject: distinct claims may share one
correspondence. -/
theorem claim_not_correspondence :
    ∃ c₁ c₂ : Claim, ∃ k : Correspondence,
      c₁.subject = .correspondenceSubject k ∧ c₂.subject = .correspondenceSubject k ∧ c₁ ≠ c₂ :=
  ⟨claimA, claimB, sampleCorrespondence, rfl, rfl, by decide⟩

/-! ## `SETTLED` is a lifecycle predicate, not truth -/

/-- The operational criterion of §7: interpretation fixed (the claim has left
`proposed`), formalization fixed, scope explicit, provenance complete, and no
open conflict. -/
def Settled (c : Claim) : Prop :=
  c.state ≠ .proposed ∧ c.state ≠ .contested ∧ c.formalization.isSome = true ∧
    c.evidence.scope ≠ "" ∧ c.provenance.source ≠ "" ∧
    c.evidence.conflictLevel ≠ .contradiction

instance (c : Claim) : Decidable (Settled c) := by unfold Settled; infer_instance

/-- A settled, Lean-verified claim whose epistemic status is still a conjecture:
the informal statement is broader than what was formalized. -/
def settledConjecture : Claim :=
  ⟨2, .leanDeclaration "Polymath.STCKG.axes_surjective",
    "the two axes are independent", "audit", [],
    EvidenceProfile.leanVerified "the 32 combinations of the two axes", auditProv,
    some "Polymath.STCKG.axes_surjective", .active, .conjecture⟩

/-- **§7.** `SETTLED` does not mean `TRUE`, `VERIFIED` or `ESTABLISHED`: a claim
may be settled and Lean-verified while its epistemic status is `CONJECTURE`. -/
theorem settled_not_true :
    ∃ c : Claim, Settled c ∧ c.epistemic = .conjecture ∧
      c.evidence.formalStatus = .verified ∧ c.evidence.toBelief = Polymath.OSA4.PT.TRUE_KNOWN :=
  ⟨settledConjecture, by decide, rfl, rfl, rfl⟩

/-- Lifecycle state and epistemic status are independent dimensions. -/
theorem statuses_independent (s : ClaimState) (e : EpistemicStatus) :
    ∃ c : Claim, c.state = s ∧ c.epistemic = e :=
  ⟨{ claimA with state := s, epistemic := e }, rfl, rfl⟩

/-- A refuted claim is retained, with its refutation recorded; it is not
deleted. -/
theorem refutation_is_recorded :
    ∃ c : Claim, c.state = .refuted ∧ c.epistemic = .refutedStatus :=
  ⟨{ claimA with state := .refuted, epistemic := .refutedStatus }, rfl, rfl⟩

/-! ## Bridge to `Polymath.ProofGraph` -/

/-- The inference step induced by a claim: its identifier is justified by the
identifiers it assumes. -/
def Claim.toStep (c : Claim) : Step := ⟨c.id, c.assumptions⟩

/-- A claim set, together with a base of accepted identifiers, is a proof
graph. -/
def toProofs (base : Finset ℕ) (cs : List Claim) : Proofs :=
  ⟨base, cs.map Claim.toStep⟩

@[simp] theorem toStep_conclusion (c : Claim) : c.toStep.conclusion = c.id := rfl

@[simp] theorem toStep_premises (c : Claim) : c.toStep.premises = c.assumptions := rfl

theorem mem_steps_toProofs {base : Finset ℕ} {cs : List Claim} {c : Claim} (hc : c ∈ cs) :
    c.toStep ∈ (toProofs base cs).steps := List.mem_map_of_mem hc

/-- **Bridge theorem.**  If every assumption of a claim is derivable in the
induced proof graph, the claim itself is derivable. -/
theorem derivable_of_assumptions_derivable {base : Finset ℕ} {cs : List Claim} {c : Claim}
    (hc : c ∈ cs) (h : ∀ p ∈ c.assumptions, Derivable (toProofs base cs) p) :
    Derivable (toProofs base cs) c.id :=
  Derivable.infer (mem_steps_toProofs hc) h

/-- A claim with no assumptions is derivable as soon as it is in the graph. -/
theorem derivable_of_no_assumptions {base : Finset ℕ} {cs : List Claim} {c : Claim}
    (hc : c ∈ cs) (h : c.assumptions = []) : Derivable (toProofs base cs) c.id :=
  derivable_of_assumptions_derivable hc (by simp [h])

/-- Derivability is monotone: enlarging the claim set never removes
derivations. -/
theorem derivable_mono {P Q : Proofs} (hassum : P.assumptions ⊆ Q.assumptions)
    (hsteps : ∀ s ∈ P.steps, s ∈ Q.steps) {x : ℕ} (h : Derivable P x) : Derivable Q x := by
  induction h with
  | assumption hn => exact Derivable.assumption (hassum hn)
  | @infer s hs _ ih => exact Derivable.infer (hsteps s hs) ih

/-- Adding claims preserves all previous derivations. -/
theorem derivable_append {base : Finset ℕ} {cs ds : List Claim} {x : ℕ}
    (h : Derivable (toProofs base cs) x) : Derivable (toProofs base (cs ++ ds)) x :=
  derivable_mono (by simp [toProofs]) (by
    intro s hs
    simpa [toProofs, List.mem_append] using Or.inl (by simpa [toProofs] using hs)) h

/-- **The bridge is structural only.**  Derivability inside the claim graph is a
statement about the graph, not about the world: a derivable claim may still be a
mere conjecture with no evidence at all. -/
theorem derivable_does_not_imply_established :
    ∃ (base : Finset ℕ) (cs : List Claim) (c : Claim),
      c ∈ cs ∧ Derivable (toProofs base cs) c.id ∧ c.epistemic = .conjecture ∧
        c.evidence.toBelief = Polymath.OSA4.PT.UNKNOWN := by
  refine ⟨∅, [claimA], claimA, by simp, ?_, rfl, rfl⟩
  exact derivable_of_no_assumptions (by simp) rfl

/-- `Claim.toStep` is not injective: two claims with the same `id` and
`assumptions` but different `predicate` produce the same `Step`.
This formalizes the information loss of the Claim → ProofGraph.Step bridge.

**Witness:** `claimA` with `predicate := "X"` and `claimA` with `predicate := "Y"`.
Both map to `⟨0, []⟩` because `toStep` only reads `id` and `assumptions`.
The claims differ in `predicate`, so they are distinct. -/
theorem toStep_not_injective : ¬ Function.Injective Claim.toStep := by
  intro h
  -- CONCRETE WITNESS: two claims, same id/assumptions, different predicate
  have h_eq : Claim.toStep { claimA with predicate := "X" } =
      Claim.toStep { claimA with predicate := "Y" } := by
    simp [Claim.toStep, claimA]
  -- COMPUTABLE DISTINCTION: the witness claims are not equal
  have h_ne : { claimA with predicate := "X" } ≠ { claimA with predicate := "Y" } := by
    simp [claimA]
  -- CONCLUSION: injectivity would force equal claims from equal steps
  exact h_ne (h h_eq)


end Polymath.STCKG
