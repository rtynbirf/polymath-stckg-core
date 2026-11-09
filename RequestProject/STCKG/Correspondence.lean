import RequestProject.STCKG.Evidence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ST-CKG correspondences: two independent axes

Audit questions H3 (does `Correspondence` deserve its own type?) and H4 (are the
two axes independent?).

`Correspondence` is a *semantic record*: it says that somebody asserted a
correspondence between two avatars, with a recorded semantic strength, a
recorded formal realization, evidence and provenance.  It is deliberately **not**
a relation, a function, a morphism or a functor (§15).

Formal findings:

* `correspondence_not_determined_by_endpoints` — the pair `(source, target)`
  does not determine the record, so a correspondence is not a binary relation
  on avatars: H3 answered positively, the type is needed.
* `axes_surjective` and `axes_card` — the map to
  `SemanticStrength × FormalRealization` is onto, so all 32 combinations occur:
  the two axes are independent (H4).
* `realization_tag_does_not_entail_relation` — tagging a correspondence
  `formalRealization = RELATION` does not make any particular relation hold; the
  tag is bookkeeping, the relation must be supplied and proved separately.
* `Realizes` / `realizes_of_functionLike` — the honest way to attach a formal
  realization: a separate predicate connecting the tag to an actual relation.
-/

namespace Polymath.STCKG

/-! ## The two axes -/

/-- Axis A: how strong the *semantic* correspondence is claimed to be. -/
inductive SemanticStrength
  | analogical | structural | semanticallySpecified | semanticallyEstablished
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Axis B: which *formal* realization (if any) has been exhibited. -/
inductive FormalRealization
  | none | relation | function | mapping | morphism | functor | naturalTransformation | other
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A correspondence between two avatars: a semantic record, not a mathematical
relation. -/
structure Correspondence where
  /-- Source avatar. -/
  source : Avatar
  /-- Target avatar. -/
  target : Avatar
  /-- Axis A. -/
  semanticStrength : SemanticStrength
  /-- Axis B. -/
  formalRealization : FormalRealization
  /-- Evidence for the correspondence. -/
  evidence : EvidenceProfile
  /-- Where the correspondence came from. -/
  provenance : Provenance
  deriving DecidableEq, Repr, Inhabited

/-- The pair of axis values of a correspondence. -/
def Correspondence.axes (c : Correspondence) : SemanticStrength × FormalRealization :=
  (c.semanticStrength, c.formalRealization)

/-! ## H4 — independence of the axes -/

/-- **H4.** Every combination of semantic strength and formal realization is
realizable, so the two axes are independent: neither determines the other. -/
theorem axes_surjective : Function.Surjective Correspondence.axes := by
  rintro ⟨s, f⟩
  exact ⟨⟨feedbackPhysics, feedbackBiology, s, f, EvidenceProfile.blank, auditProv⟩, rfl⟩

/-- There are 32 legal combinations of the two axes; none is excluded. -/
theorem axes_card : Fintype.card (SemanticStrength × FormalRealization) = 32 := by decide

/-- A formally realized correspondence may still be only an analogy. -/
theorem realization_not_determine_strength :
    ∃ c₁ c₂ : Correspondence,
      c₁.formalRealization = c₂.formalRealization ∧
      c₁.semanticStrength ≠ c₂.semanticStrength :=
  ⟨⟨feedbackPhysics, feedbackBiology, .analogical, .functor, EvidenceProfile.blank, auditProv⟩,
   ⟨feedbackPhysics, feedbackBiology, .semanticallyEstablished, .functor,
     EvidenceProfile.blank, auditProv⟩, rfl, by decide⟩

/-- A semantically established correspondence may have no formalization at all. -/
theorem strength_not_determine_realization :
    ∃ c₁ c₂ : Correspondence,
      c₁.semanticStrength = c₂.semanticStrength ∧
      c₁.formalRealization ≠ c₂.formalRealization :=
  ⟨⟨feedbackPhysics, feedbackBiology, .semanticallyEstablished, .none,
     EvidenceProfile.blank, auditProv⟩,
   ⟨feedbackPhysics, feedbackBiology, .semanticallyEstablished, .functor,
     EvidenceProfile.blank, auditProv⟩, rfl, by decide⟩

/-! ## H3 — the type is not subsumed by a relation -/

/-- **H3.** Two different correspondences may share both endpoints, so
`Correspondence` is not a binary relation on avatars: the endpoints do not
determine the record. -/
theorem correspondence_not_determined_by_endpoints :
    ∃ c₁ c₂ : Correspondence,
      c₁.source = c₂.source ∧ c₁.target = c₂.target ∧ c₁ ≠ c₂ :=
  ⟨⟨feedbackPhysics, feedbackBiology, .analogical, .none, EvidenceProfile.blank, auditProv⟩,
   ⟨feedbackPhysics, feedbackBiology, .structural, .morphism, EvidenceProfile.blank, auditProv⟩,
   rfl, rfl, by decide⟩

/-- **§15.** The `RELATION` tag by itself entails nothing: there are
correspondences tagged as realized by a relation for which a given relation
simply fails to hold. -/
theorem realization_tag_does_not_entail_relation :
    ∃ (c : Correspondence) (R : Avatar → Avatar → Prop),
      c.formalRealization = .relation ∧ ¬ R c.source c.target :=
  ⟨⟨feedbackPhysics, feedbackBiology, .structural, .relation, EvidenceProfile.blank, auditProv⟩,
    fun _ _ => False, rfl, id⟩

/-- The honest reading of "this correspondence is realized by the relation `R`":
the tag *and* the relation, stated together and provable separately. -/
def Realizes (c : Correspondence) (R : Avatar → Avatar → Prop) : Prop :=
  c.formalRealization = .relation ∧ R c.source c.target

/-- Co-reference is a legitimate formal realization of a correspondence between
two avatars of one referent. -/
theorem realizes_coRefers
    (c : Correspondence) (h : c.formalRealization = .relation)
    (hc : CoRefers c.source c.target) : Realizes c CoRefers := ⟨h, hc⟩

/-- Realization is preserved when the relation is weakened, and nothing else is
claimed by it. -/
theorem Realizes.mono {c : Correspondence} {R S : Avatar → Avatar → Prop}
    (h : Realizes c R) (hRS : ∀ a b, R a b → S a b) : Realizes c S :=
  ⟨h.1, hRS _ _ h.2⟩

/-- Claiming a functor is a strictly stronger bookkeeping act than claiming a
relation, but neither tag by itself upgrades the semantic axis. -/
theorem tag_change_preserves_semantics (c : Correspondence) (f : FormalRealization) :
    ({ c with formalRealization := f }).semanticStrength = c.semanticStrength := rfl

end Polymath.STCKG
