import RequestProject.STCKG.Correspondence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Category Gate (§18) and the fibration hypothesis (§16)

Audit questions H5 and H6.

## What is checked here

* **Events (§19).**  For each proposed relation on events the six category
  requirements are checked separately.
  * `precedes` is transitive (`precedes_trans`) and its reflexive closure is a
    preorder (`eventPreorder`), so the *preorder category* exists — no extra
    category-theoretic machinery is needed, and none is introduced.
  * `overlaps` is reflexive and symmetric but **not transitive**
    (`overlaps_not_transitive`): it is a tolerance relation, not a category.
  * `causes` is *not* automatically transitive even when contained in
    `precedes` (`causes_transitivity_not_automatic`): a causal relation must be
    checked case by case before any categorical language is used.
* **Concepts (§20).**  The one thing a free category has that a preorder does
  not is *distinct parallel morphisms*: `two_distinct_concept_paths` exhibits
  two different paths with the same endpoints, while
  `reachability_collapses_paths` shows the preorder identifies them.  That is
  the concrete extra capability which justifies a free category — and only that.
* **Fibration (§16).**  The claim "REFERENT → VIEW → AVATAR is already a
  Grothendieck fibration" is **rejected**.  In the thin setting all morphisms
  with a given source and target are equal, so the cartesian condition reduces
  to existence of lifts; `avatarStore_not_hasLifts` gives a concrete avatar
  store with no lift, and `hasLifts_iff_viewComplete` characterises exactly when
  the projection *is* a fibration: precisely when the avatar store is complete
  along the view order.
-/

namespace Polymath.STCKG

/-! ## A minimal notion of thin category

A thin (preorder) category is a reflexive transitive relation.  Hom-"sets" are
propositions, hence subsingletons: identity, composition, associativity and the
identity laws hold automatically, which is exactly why the Category Gate is
passed by preorders without any extra structure. -/

/-- A thin category: objects plus a reflexive transitive hom-relation. -/
structure ThinCat (X : Type _) where
  /-- The hom-relation. -/
  hom : X → X → Prop
  /-- Identity morphisms. -/
  id' : ∀ x, hom x x
  /-- Composition. -/
  comp' : ∀ {x y z}, hom x y → hom y z → hom x z

/-- In a thin category all parallel morphisms are equal, so associativity and
the identity laws are automatic. -/
theorem ThinCat.hom_subsingleton {X : Type _} (C : ThinCat X) (x y : X)
    (f g : C.hom x y) : f = g := rfl

/-- A functor between thin categories: a map preserving the hom-relation. -/
structure ThinFunctor {E B : Type _} (CE : ThinCat E) (CB : ThinCat B) where
  /-- Action on objects. -/
  obj : E → B
  /-- Action on morphisms. -/
  map : ∀ {x y}, CE.hom x y → CB.hom (obj x) (obj y)

/-- The lifting condition defining a fibration in the thin setting: every
morphism of the base ending at `p e` lifts to a morphism ending at `e`. -/
def HasLifts {E B : Type _} {CE : ThinCat E} {CB : ThinCat B}
    (p : ThinFunctor CE CB) : Prop :=
  ∀ (e : E) (b : B), CB.hom b (p.obj e) → ∃ e', p.obj e' = b ∧ CE.hom e' e

/-! ## H5 — the category of events -/

/-- An event occupies a time interval. -/
structure Event where
  /-- Start time. -/
  start : ℕ
  /-- End time. -/
  stop : ℕ
  /-- Events last a non-negative amount of time. -/
  le : start ≤ stop

/-- Strict temporal precedence. -/
def Precedes (e f : Event) : Prop := e.stop ≤ f.start

/-- Precedence is transitive: this uses `Event.le`, i.e. that events are
well-formed intervals. -/
theorem precedes_trans : Transitive Precedes :=
  fun _ f _ hef hfg => le_trans hef (le_trans f.le hfg)

/-- Precedence is irreflexive on events of positive duration. -/
theorem precedes_irrefl_of_pos {e : Event} (h : e.start < e.stop) : ¬ Precedes e e :=
  fun hp => absurd hp (not_le.2 h)

/-- The reflexive closure of precedence. -/
def PrecedesEq (e f : Event) : Prop := Precedes e f ∨ e = f

theorem precedesEq_refl (e : Event) : PrecedesEq e e := Or.inr rfl

theorem precedesEq_trans : Transitive PrecedesEq := by
  rintro e f g (hef | rfl) (hfg | rfl)
  · exact Or.inl (precedes_trans hef hfg)
  · exact Or.inl hef
  · exact Or.inl hfg
  · exact Or.inr rfl

/-- **Category Gate, `precedes`: PASSED, as a preorder.**  Objects, morphisms,
identities, composition, associativity and the identity laws are all present,
and nothing beyond a preorder is needed. -/
def eventThinCat : ThinCat Event where
  hom := PrecedesEq
  id' := precedesEq_refl
  comp' := fun h k => precedesEq_trans h k

/-- The preorder instance behind `eventThinCat`. -/
def eventPreorder : Preorder Event where
  le := PrecedesEq
  le_refl := precedesEq_refl
  le_trans := fun _ _ _ h k => precedesEq_trans h k

/-- Two events overlap when their intervals intersect. -/
def Overlaps (e f : Event) : Prop := e.start ≤ f.stop ∧ f.start ≤ e.stop

theorem overlaps_refl (e : Event) : Overlaps e e := ⟨e.le, e.le⟩

theorem overlaps_symm {e f : Event} (h : Overlaps e f) : Overlaps f e := ⟨h.2, h.1⟩

/-- The event `[0,1]`. -/
def ev01 : Event := ⟨0, 1, by norm_num⟩

/-- The event `[1,2]`. -/
def ev12 : Event := ⟨1, 2, by norm_num⟩

/-- The event `[2,3]`. -/
def ev23 : Event := ⟨2, 3, by norm_num⟩

/-- **Category Gate, `overlaps`: FAILED.**  Overlapping is reflexive and
symmetric but not transitive, so it admits no composition and is not a
category; it is a tolerance relation. -/
theorem overlaps_not_transitive : ¬ Transitive Overlaps := by
  intro h
  have h₁ : Overlaps ev01 ev12 := ⟨by norm_num [ev01, ev12], by norm_num [ev01, ev12]⟩
  have h₂ : Overlaps ev12 ev23 := ⟨by norm_num [ev12, ev23], by norm_num [ev12, ev23]⟩
  have h₃ : Overlaps ev01 ev23 := h h₁ h₂
  have := h₃.2
  norm_num [ev01, ev23] at this

/-- The event `[4,5]`. -/
def ev45 : Event := ⟨4, 5, by norm_num⟩

/-- **Category Gate, `causes`: UNDECIDED in general.**  Even a causal relation
that always respects temporal precedence need not be transitive, so `causes`
must never be declared a class of morphisms by default. -/
theorem causes_transitivity_not_automatic :
    ∃ C : Event → Event → Prop, (∀ e f, C e f → Precedes e f) ∧ ¬ Transitive C := by
  classical
  refine ⟨fun e f => (e = ev01 ∧ f = ev23) ∨ (e = ev23 ∧ f = ev45), ?_, ?_⟩
  · rintro e f (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · norm_num [Precedes, ev01, ev23]
    · norm_num [Precedes, ev23, ev45]
  · intro h
    have h₁ : (ev01 = ev01 ∧ ev23 = ev23) ∨ (ev01 = ev23 ∧ ev23 = ev45) := Or.inl ⟨rfl, rfl⟩
    have h₂ : (ev23 = ev01 ∧ ev45 = ev23) ∨ (ev23 = ev23 ∧ ev45 = ev45) := Or.inr ⟨rfl, rfl⟩
    rcases h h₁ h₂ with ⟨_, h4⟩ | ⟨h5, _⟩
    · exact absurd (congrArg Event.stop h4) (by norm_num [ev23, ev45])
    · exact absurd (congrArg Event.start h5) (by norm_num [ev01, ev23])

/-! ## H5 — the category of concepts: what a free category adds -/

/-- Three concepts, used to compare the free category on a graph with the
reachability preorder. -/
inductive ConceptNode
  | feedbackC | regulationC | stabilityC
  deriving DecidableEq, Repr, Inhabited

/-- The generating graph: `feedback → regulation → stability` and a direct edge
`feedback → stability`. -/
inductive ConceptEdge : ConceptNode → ConceptNode → Type
  | refines : ConceptEdge .feedbackC .regulationC
  | explains : ConceptEdge .regulationC .stabilityC
  | shortcut : ConceptEdge .feedbackC .stabilityC

instance : Quiver ConceptNode := ⟨ConceptEdge⟩

/-- The composite path `feedback → regulation → stability`. -/
def longPath : Quiver.Path ConceptNode.feedbackC ConceptNode.stabilityC :=
  (Quiver.Path.nil.cons ConceptEdge.refines).cons ConceptEdge.explains

/-- The direct path `feedback → stability`. -/
def shortPath : Quiver.Path ConceptNode.feedbackC ConceptNode.stabilityC :=
  Quiver.Path.nil.cons ConceptEdge.shortcut

/-- **The free category on the concept graph distinguishes derivations.**  Two
parallel morphisms with the same endpoints are different, which a preorder can
never express. -/
theorem two_distinct_concept_paths : longPath ≠ shortPath := by
  intro h
  have : longPath.length = shortPath.length := congrArg Quiver.Path.length h
  simp [longPath, shortPath, Quiver.Path.length] at this

/-- Reachability in the concept graph. -/
def Reaches (a b : ConceptNode) : Prop := Nonempty (Quiver.Path a b)

/-- **…and the preorder collapses them.**  In the reachability preorder there is
at most one morphism between two objects, so the two derivations above are
identified.  This is the precise extra capability that justifies the free
category — and the only one claimed here. -/
theorem reachability_collapses_paths (a b : ConceptNode) (h k : Reaches a b) : h = k := rfl

theorem reaches_refl (a : ConceptNode) : Reaches a a := ⟨Quiver.Path.nil⟩

theorem reaches_trans {a b c : ConceptNode} (h : Reaches a b) (k : Reaches b c) : Reaches a c :=
  ⟨h.some.comp k.some⟩

/-- The reachability preorder as a thin category. -/
def conceptThinCat : ThinCat ConceptNode where
  hom := Reaches
  id' := reaches_refl
  comp' := reaches_trans

/-! ## H6 — the Grothendieck fibration hypothesis, rejected -/

/-- A minimal order on views: the mathematical view is an abstraction of every
view, and otherwise views are incomparable.  (Any preorder would do; the
counterexample below only needs one non-identity morphism.) -/
def ViewLe (v w : View) : Prop := v = w ∨ v = View.mathematics

instance (v w : View) : Decidable (ViewLe v w) := by unfold ViewLe; infer_instance

theorem viewLe_refl (v : View) : ViewLe v v := Or.inl rfl

theorem viewLe_trans {u v w : View} (h : ViewLe u v) (k : ViewLe v w) : ViewLe u w := by
  rcases h with rfl | rfl
  · exact k
  · exact Or.inr rfl

/-- The base thin category: views ordered by abstraction. -/
def viewThinCat : ThinCat View where
  hom := ViewLe
  id' := viewLe_refl
  comp' := viewLe_trans

/-- The total thin category over a store `S` of avatars: a morphism is a
co-referential move down the view order. -/
def avatarThinCat (S : Set Avatar) : ThinCat {a : Avatar // a ∈ S} where
  hom := fun a b => a.1.referent = b.1.referent ∧ ViewLe a.1.view b.1.view
  id' := fun _ => ⟨rfl, viewLe_refl _⟩
  comp' := fun h k => ⟨h.1.trans k.1, viewLe_trans h.2 k.2⟩

/-- The projection `avatar ↦ view`, a functor of thin categories. -/
def viewProjection (S : Set Avatar) : ThinFunctor (avatarThinCat S) viewThinCat where
  obj := fun a => a.1.view
  map := fun h => h.2

/-- An avatar store is *view-complete* when every avatar can be pulled back
along the view order: for each avatar in the store and each view below it, the
store contains an avatar of the same referent in that view. -/
def ViewComplete (S : Set Avatar) : Prop :=
  ∀ a ∈ S, ∀ v : View, ViewLe v a.view → ∃ b ∈ S, b.referent = a.referent ∧ b.view = v

/-- **The exact criterion.**  Since the categories are thin, every lift is
automatically cartesian, so the projection is a fibration precisely when the
avatar store is view-complete.  Fibration status is therefore a *property of the
data*, never an architectural given. -/
theorem hasLifts_iff_viewComplete (S : Set Avatar) :
    HasLifts (viewProjection S) ↔ ViewComplete S := by
  constructor
  · intro h a ha v hv
    obtain ⟨b, hb, hhom⟩ := h ⟨a, ha⟩ v hv
    exact ⟨b.1, b.2, hhom.1, hb⟩
  · intro h e v hv
    obtain ⟨b, hb, href, hview⟩ := h e.1 e.2 v hv
    exact ⟨⟨b, hb⟩, hview, href, hview ▸ hv⟩

/-- A store consisting of a single physics avatar. -/
def singletonStore : Set Avatar := {feedbackPhysics}

/-- **H6: REJECTED.**  `REFERENT → VIEW → AVATAR` is not a fibration in general:
here the mathematical view lies below physics, but the store contains no
mathematical avatar of the referent, so the required cartesian lift does not
exist. -/
theorem avatarStore_not_hasLifts : ¬ HasLifts (viewProjection singletonStore) := by
  rw [hasLifts_iff_viewComplete]
  intro h
  obtain ⟨b, hb, _, hview⟩ :=
    h feedbackPhysics rfl View.mathematics (Or.inr rfl)
  rw [show b = feedbackPhysics from hb] at hview
  exact absurd hview (by decide)

/-- **The positive half.**  A view-complete store does give a fibration, so the
architecture can *achieve* the fibration property by construction — it simply
does not have it for free. -/
theorem hasLifts_of_viewComplete {S : Set Avatar} (h : ViewComplete S) :
    HasLifts (viewProjection S) := (hasLifts_iff_viewComplete S).2 h

/-- Completing the store with the missing mathematical avatar repairs the
counterexample. -/
def completedStore : Set Avatar :=
  {feedbackPhysics, { feedbackPhysics with view := View.mathematics }}

theorem completedStore_viewComplete : ViewComplete completedStore := by
  have hmath : ({ feedbackPhysics with view := View.mathematics } : Avatar) ∈ completedStore :=
    Or.inr rfl
  intro a ha v hv
  simp only [completedStore, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases hv with rfl | rfl
  · exact ⟨a, ha, rfl, rfl⟩
  · rcases ha with rfl | rfl
    · exact ⟨_, hmath, rfl, rfl⟩
    · exact ⟨_, hmath, rfl, rfl⟩

theorem completedStore_hasLifts : HasLifts (viewProjection completedStore) :=
  hasLifts_of_viewComplete completedStore_viewComplete

end Polymath.STCKG
