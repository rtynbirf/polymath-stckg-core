import RequestProject.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ST-CKG core: referents, views and avatars

This is the minimal kernel of the ST-CKG *semantic layer*.  It is deliberately
built **on top of** the existing `Polymath.Core` ontology (`ObjectKind`,
`KnowledgeObject`, `Maturity`) and never replaces it.

The audit questions answered here are H1 (referential unity), H2 (referent /
view / avatar) and H10 (architectural novelty).

Findings formalised below:

* `Avatar` is a **record**, not a function of `(Referent, View)`:
  `avatar_not_determined_by_referent_view` exhibits two distinct avatars of the
  same referent in the same view, and `avatarsAt_card_zero/one/two` show that a
  `(referent, view)` pair may carry `0`, `1` or `N` avatars.
* Co-reference is an equivalence relation on avatars (`coRefers_equivalence`)
  but it neither forces equal representations
  (`coRefers_not_same_representation`) nor is forced by them
  (`same_representation_not_coRefers`).  So "same referent" and "same
  representation" are genuinely independent statements (§17 anti-conflation).
* The avatar layer is an **architectural extension**, not a new formal
  structure: `Avatar.split` is an explicit injection of `Avatar` into
  `KnowledgeObject`-data together with the extra labelled fields.
-/

namespace Polymath.STCKG

open Polymath

/-! ## Referents, views, provenance -/

/-- Identifier of a referent.  Deliberately *not* a claim that the referent
exists independently of the model (§12): it is a database identity. -/
abbrev ReferentId := ℕ

/-- A referent: the abstract thing that representations are *about*.
The `note` field is documentation only and carries no semantics. -/
structure Referent where
  /-- Database identity of the referent. -/
  id : ReferentId
  /-- Informal note (documentation only). -/
  note : String
  deriving DecidableEq, Repr, Inhabited

/-- A view: a domain, context or aspect in which a referent is represented. -/
inductive View
  | physics | biology | economics | controlTheory | informationTheory
  | mathematics | leanFormalization | stckg
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Provenance data (§28).  `Provenance ≠ proof`: it records where something
came from, not that it is true. -/
structure Provenance where
  /-- Source document or dataset. -/
  source : String
  /-- Author or agent responsible. -/
  author : String
  /-- Logical timestamp. -/
  timestamp : ℕ
  /-- Derivation trail. -/
  derivation : List String
  deriving DecidableEq, Repr, Inhabited

/-- Version counter of an avatar. -/
abbrev Version := ℕ

/-- The role an avatar plays for its referent. -/
inductive AvatarRole
  | definitional | model | metaphor | measurement | formalization
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- A representation reuses the existing `ObjectKind` vocabulary of
`Polymath.Core`; it is *not* a new ontology. -/
structure Representation where
  /-- Kind, taken from the existing core ontology. -/
  kind : ObjectKind
  /-- Label of the representation. -/
  label : String
  deriving DecidableEq, Repr, Inhabited

/-- An avatar: one representation of one referent inside one view.
Per §14 this is a record, not a function `Referent × View → Representation`. -/
structure Avatar where
  /-- The referent this avatar represents. -/
  referent : Referent
  /-- The view the avatar lives in. -/
  view : View
  /-- The representation itself. -/
  representation : Representation
  /-- The role the avatar plays. -/
  role : AvatarRole
  /-- Where the avatar came from. -/
  provenance : Provenance
  /-- Version of the avatar. -/
  version : Version
  deriving DecidableEq, Repr, Inhabited

/-! ## H1 — referential unity as an equivalence, not an identification -/

/-- Two avatars co-refer when they represent the same referent. -/
def CoRefers (a b : Avatar) : Prop := a.referent = b.referent

instance (a b : Avatar) : Decidable (CoRefers a b) := by
  unfold CoRefers; infer_instance

theorem coRefers_equivalence : Equivalence CoRefers :=
  ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/-! ### Concrete witnesses used by the counterexamples -/

/-- A sample provenance record. -/
def auditProv : Provenance := ⟨"foundational-audit", "aristotle", 0, []⟩

/-- The referent "feedback". -/
def feedback : Referent := ⟨0, "feedback"⟩

/-- The referent "resonance". -/
def resonance : Referent := ⟨1, "resonance"⟩

/-- Feedback seen in physics, as a control loop. -/
def feedbackPhysics : Avatar :=
  ⟨feedback, .physics, ⟨.mechanism, "control loop"⟩, .model, auditProv, 0⟩

/-- Feedback seen in physics again, as a damping mechanism: a *second* avatar of
the same referent in the same view. -/
def feedbackPhysics' : Avatar :=
  ⟨feedback, .physics, ⟨.mechanism, "damping"⟩, .model, auditProv, 0⟩

/-- Feedback seen in biology. -/
def feedbackBiology : Avatar :=
  ⟨feedback, .biology, ⟨.mechanism, "homeostasis"⟩, .model, auditProv, 0⟩

/-- Resonance seen in physics, carrying *the same representation label* as
`feedbackPhysics`: representations do not determine referents. -/
def resonancePhysics : Avatar :=
  ⟨resonance, .physics, ⟨.mechanism, "control loop"⟩, .model, auditProv, 0⟩

/-- **H1.** Co-reference does not force equal representations. -/
theorem coRefers_not_same_representation :
    ∃ a b : Avatar, CoRefers a b ∧ a.representation ≠ b.representation :=
  ⟨feedbackPhysics, feedbackBiology, rfl, by decide⟩

/-- **H1 / §17.** Equal representations do not force co-reference. -/
theorem same_representation_not_coRefers :
    ∃ a b : Avatar, a.representation = b.representation ∧ ¬ CoRefers a b :=
  ⟨feedbackPhysics, resonancePhysics, rfl, by decide⟩

/-! ## H2 — avatars of a `(referent, view)` pair -/

/-- The avatars of `r` in view `v` inside a finite avatar store. -/
def avatarsAt (S : Finset Avatar) (r : Referent) (v : View) : Finset Avatar :=
  S.filter (fun a => a.referent = r ∧ a.view = v)

/-- **H2.** `Avatar` is not a function of `(Referent, View)`. -/
theorem avatar_not_determined_by_referent_view :
    ∃ a b : Avatar, a.referent = b.referent ∧ a.view = b.view ∧ a ≠ b :=
  ⟨feedbackPhysics, feedbackPhysics', rfl, rfl, by decide⟩

/-- A `(referent, view)` pair may carry no avatar. -/
theorem avatarsAt_card_zero : (avatarsAt ∅ feedback .physics).card = 0 := by decide

/-- A `(referent, view)` pair may carry exactly one avatar. -/
theorem avatarsAt_card_one :
    (avatarsAt {feedbackPhysics, feedbackBiology} feedback .physics).card = 1 := by decide

/-- A `(referent, view)` pair may carry several avatars. -/
theorem avatarsAt_card_two :
    (avatarsAt {feedbackPhysics, feedbackPhysics', feedbackBiology} feedback .physics).card
      = 2 := by decide

/-- Every avatar of `avatarsAt S r v` really is an avatar of `r` in `v`. -/
theorem mem_avatarsAt_iff (S : Finset Avatar) (r : Referent) (v : View) (a : Avatar) :
    a ∈ avatarsAt S r v ↔ a ∈ S ∧ a.referent = r ∧ a.view = v := by
  simp [avatarsAt]

/-- Avatar identity is extensional in its six fields. -/
theorem avatar_ext_iff (a b : Avatar) :
    a = b ↔ a.referent = b.referent ∧ a.view = b.view ∧
      a.representation = b.representation ∧ a.role = b.role ∧
      a.provenance = b.provenance ∧ a.version = b.version := by
  cases a; cases b
  simp [Avatar.mk.injEq]

/-- An avatar may change between versions while keeping referent and view. -/
theorem avatar_version_change :
    ∃ a b : Avatar, CoRefers a b ∧ a.view = b.view ∧ a.version ≠ b.version ∧ a ≠ b :=
  ⟨feedbackPhysics, { feedbackPhysics with version := 1 }, rfl, rfl, by decide, by decide⟩

/-! ## H10 — the avatar layer is an extension of the existing core -/

/-- The core payload an avatar contributes to the existing `KnowledgeObject`
ontology: identifier, kind and label. -/
def Avatar.toKnowledgeObject (a : Avatar) (m : Maturity) (conf : ℤ) : KnowledgeObject :=
  ⟨a.referent.id, a.representation.kind, a.representation.label, m, conf⟩

/-- The extra, purely semantic-layer data of an avatar. -/
abbrev AvatarExtra := View × AvatarRole × Provenance × Version × String

/-- Split an avatar into existing-core data plus the extra labelled fields. -/
def Avatar.split (a : Avatar) : KnowledgeObject × AvatarExtra :=
  (a.toKnowledgeObject .hypothesis 0, (a.view, a.role, a.provenance, a.version, a.referent.note))

/-- Reassemble an avatar from core data plus extra fields. -/
def unsplit (p : KnowledgeObject × AvatarExtra) : Avatar :=
  ⟨⟨p.1.id, p.2.2.2.2.2⟩, p.2.1, ⟨p.1.kind, p.1.label⟩, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1⟩

@[simp] theorem unsplit_split (a : Avatar) : unsplit a.split = a := rfl

/-- **H10.** The avatar layer adds exactly a fixed tuple of labelled fields on
top of the existing `KnowledgeObject` data: the splitting map is injective, so
no information is invented and none is lost.  Novelty status of the layer is
therefore *architectural extension*, not *new formal structure*. -/
theorem avatar_to_core_injective : Function.Injective Avatar.split :=
  Function.LeftInverse.injective unsplit_split

/-- The image of `Avatar.split` is exactly the pairs whose maturity and
confidence are the default ones, so the correspondence is a bijection onto that
image. -/
theorem split_unsplit_of_default (p : KnowledgeObject × AvatarExtra)
    (hm : p.1.maturity = .hypothesis) (hc : p.1.confidence = 0) :
    (unsplit p).split = p := by
  obtain ⟨o, v, r, pr, ver, note⟩ := p
  cases o
  simp_all [Avatar.split, Avatar.toKnowledgeObject, unsplit]

/-- The image of `Avatar.split` is exactly the pairs whose
`KnowledgeObject` component carries the default maturity and confidence.
This completes the bridge characterization: `Avatar` is in bijection
with the restricted set `{p | p.1.maturity = .hypothesis ∧ p.1.confidence = 0}`. -/
theorem avatar_split_image_characterization (p : KnowledgeObject × AvatarExtra) :
    p ∈ Set.range Avatar.split ↔
      p.1.maturity = .hypothesis ∧ p.1.confidence = 0 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    subst ha
    simp [Avatar.split, Avatar.toKnowledgeObject]
  · intro ⟨hm, hc⟩
    exact ⟨unsplit p, split_unsplit_of_default p hm hc⟩


end Polymath.STCKG
