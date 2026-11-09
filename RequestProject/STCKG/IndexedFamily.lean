import RequestProject.STCKG.CategoryGate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The minimal correct alternative to a fibration, and the version layer

§16 of the directive asks, once the fibration claim has been rejected, for the
*minimal correct construction*.  It is an **indexed family**: the avatars of a
store, indexed by `(referent, view)`.

* `storeFamily` is that family, and `mem_storeFamily_self` / `storeFamily_disjoint`
  say that it partitions the store — every avatar lies in exactly one fibre.  No
  categorical structure is needed for this, and none is introduced.
* `viewComplete_iff_family_nonempty` connects the indexed family back to the
  fibration criterion of `CategoryGate.lean`: the projection is a fibration
  exactly when the relevant fibres of the family are non-empty.  This is the
  honest replacement for "the architecture is a Grothendieck fibration".

§21 asks whether versions form a category.  Patches are *partial* maps on
avatars, so the right structure is the Kleisli category of `Option`:
`patchComp_assoc`, `patchId_comp` and `patchComp_id` show the Category Gate is
passed, while `patch_not_invertible` shows it is a category and **not** a
groupoid — a patch may destroy information.
-/

namespace Polymath.STCKG

/-! ## The indexed family of avatars -/

/-- The fibre of a store over an index `(referent, view)`. -/
def storeFamily (S : Finset Avatar) (i : Referent × View) : Finset Avatar :=
  avatarsAt S i.1 i.2

theorem mem_storeFamily_iff (S : Finset Avatar) (i : Referent × View) (a : Avatar) :
    a ∈ storeFamily S i ↔ a ∈ S ∧ a.referent = i.1 ∧ a.view = i.2 :=
  mem_avatarsAt_iff S i.1 i.2 a

/-- Every avatar of the store lies in the fibre of its own index. -/
theorem mem_storeFamily_self {S : Finset Avatar} {a : Avatar} (ha : a ∈ S) :
    a ∈ storeFamily S (a.referent, a.view) :=
  (mem_storeFamily_iff S _ a).2 ⟨ha, rfl, rfl⟩

/-- Fibres over different indices are disjoint, so the family really is a
partition of the store: the indexed family carries exactly the information of
the store, with no choice of cartesian lifts involved. -/
theorem storeFamily_disjoint (S : Finset Avatar) {i j : Referent × View} (hij : i ≠ j) :
    Disjoint (storeFamily S i) (storeFamily S j) := by
  rw [Finset.disjoint_left]
  intro a hi hj
  rw [mem_storeFamily_iff] at hi hj
  exact hij (Prod.ext (hi.2.1.symm.trans hj.2.1) (hi.2.2.symm.trans hj.2.2))

/-- Each fibre consists of avatars of the announced index. -/
theorem storeFamily_subset (S : Finset Avatar) (i : Referent × View) :
    storeFamily S i ⊆ S := fun _ ha => ((mem_storeFamily_iff S i _).1 ha).1

/-- **The bridge to the fibration criterion.**  For a store given by a finite
family, being view-complete — i.e. being a fibration, by
`hasLifts_iff_viewComplete` — is exactly non-emptiness of the fibres below each
inhabited index. -/
theorem viewComplete_iff_family_nonempty (S : Finset Avatar) :
    ViewComplete (↑S : Set Avatar) ↔
      ∀ a ∈ S, ∀ v : View, ViewLe v a.view → (storeFamily S (a.referent, v)).Nonempty := by
  constructor
  · intro h a ha v hv
    obtain ⟨b, hb, href, hview⟩ := h a (by simpa using ha) v hv
    exact ⟨b, (mem_storeFamily_iff S _ b).2 ⟨by simpa using hb, href, hview⟩⟩
  · intro h a ha v hv
    obtain ⟨b, hb⟩ := h a (by simpa using ha) v hv
    rw [mem_storeFamily_iff] at hb
    exact ⟨b, by simpa using hb.1, hb.2.1, hb.2.2⟩

/-! ## The version layer as a Kleisli category (§21) -/

/-- A patch is a *partial* transformation of avatars. -/
def Patch := Avatar → Option Avatar

/-- The identity patch. -/
def patchId : Patch := fun a => some a

/-- Composition of patches: apply `p` first, then `q`, failing if either fails. -/
def patchComp (p q : Patch) : Patch := fun a => (p a).bind q

theorem patchComp_assoc (p q r : Patch) :
    patchComp (patchComp p q) r = patchComp p (patchComp q r) := by
  funext a
  cases h : p a <;> simp [patchComp, h]

theorem patchId_comp (p : Patch) : patchComp patchId p = p := by
  funext a; simp [patchComp, patchId]

theorem patchComp_id (p : Patch) : patchComp p patchId = p := by
  funext a
  cases h : p a <;> simp [patchComp, patchId, h]

/-- **Category Gate, versions: PASSED**, as the Kleisli category of `Option` on
one object — i.e. as a monoid of partial transformations.  Objects, morphisms,
identity, composition, associativity and the identity laws are all present. -/
def patchMonoid : Monoid Patch where
  mul := patchComp
  one := patchId
  mul_assoc := patchComp_assoc
  one_mul := patchId_comp
  mul_one := patchComp_id

/-- The patch that raises the version counter of every avatar. -/
def bumpVersion : Patch := fun a => some { a with version := a.version + 1 }

/-- The patch that forgets the provenance of every avatar. -/
def forgetProvenance : Patch := fun a => some { a with provenance := ⟨"", "", 0, []⟩ }

/-- **…but it is not a groupoid.**  A patch that erases provenance has no
inverse: two avatars differing only in provenance become equal, so no patch can
undo it. -/
theorem patch_not_invertible :
    ¬ ∃ q : Patch, patchComp forgetProvenance q = patchId := by
  rintro ⟨q, hq⟩
  have h₁ : q { feedbackPhysics with provenance := ⟨"", "", 0, []⟩ } = some feedbackPhysics :=
    congrFun hq feedbackPhysics
  have h₂ : q { feedbackPhysics with provenance := ⟨"", "", 0, []⟩ }
      = some { feedbackPhysics with provenance := ⟨"other", "", 0, []⟩ } :=
    congrFun hq { feedbackPhysics with provenance := ⟨"other", "", 0, []⟩ }
  rw [h₁] at h₂
  exact absurd h₂ (by decide)

/-- Bumping the version is, by contrast, injective on avatars, so it is a legal
step of the version layer that loses no information. -/
theorem bumpVersion_injective {a b : Avatar} (h : bumpVersion a = bumpVersion b) : a = b := by
  simp only [bumpVersion, Option.some.injEq, Avatar.mk.injEq, add_left_inj] at h
  rw [avatar_ext_iff]
  exact h

end Polymath.STCKG
