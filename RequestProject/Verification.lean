import RequestProject.Dependency

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Verification status of a knowledge graph

An identifier is *resolved* by the object of the graph carrying it; by the
referential-integrity obligations of `KnowledgeGraph` that object is unique.
This module builds the verification vocabulary on top of that:

* `HasObject` and `hasObject_unique` — identifier resolution is functional;
* `MaturityAtLeast` and `Certified` — a graph is certified at level `m` when
  every one of its objects has reached maturity `m`;
* `Grounded` — an object is grounded when everything it depends on is at least
  as mature as the object itself, and `Grounded` propagates along whole
  dependency chains (`maturity_le_of_depends`);
* `confidenceOf` and `chain_confidence_le` — the confidence of a dependency
  chain is bounded by the confidence of each of its links.
-/

namespace Polymath.Verification

open Polymath Polymath.Dependency

/-- `o` is the object of `g` carrying identifier `a`. -/
def HasObject (g : KnowledgeGraph) (a : ℕ) (o : KnowledgeObject) : Prop :=
  o ∈ g.objects ∧ o.id = a

/-- Identifier resolution is functional: an identifier determines its object. -/
theorem hasObject_unique {g : KnowledgeGraph} {a : ℕ} {o p : KnowledgeObject}
    (ho : HasObject g a o) (hp : HasObject g a p) : o = p :=
  g.unique_id o ho.1 p hp.1 (ho.2.trans hp.2.symm)

/-- Every identifier of the graph is resolved. -/
theorem exists_hasObject {g : KnowledgeGraph} {a : ℕ} (ha : a ∈ g.ids) :
    ∃ o, HasObject g a o := by
  obtain ⟨o, ho, hid⟩ := (g.mem_ids_iff a).1 ha
  exact ⟨o, ho, hid⟩

theorem mem_ids_of_hasObject {g : KnowledgeGraph} {a : ℕ} {o : KnowledgeObject}
    (ho : HasObject g a o) : a ∈ g.ids :=
  (g.mem_ids_iff a).2 ⟨o, ho.1, ho.2⟩

/-! ## Maturity certification -/

/-- The object carrying `a` has reached maturity `m` or beyond. -/
def MaturityAtLeast (g : KnowledgeGraph) (m : Maturity) (a : ℕ) : Prop :=
  ∃ o, HasObject g a o ∧ m ≤ o.maturity

/-- A graph is certified at level `m` when all of its objects have reached `m`. -/
def Certified (g : KnowledgeGraph) (m : Maturity) : Prop :=
  ∀ a ∈ g.ids, MaturityAtLeast g m a

/-- Certification is monotone in the required maturity level. -/
theorem Certified.mono {g : KnowledgeGraph} {m m' : Maturity} (h : Certified g m)
    (hle : m' ≤ m) : Certified g m' := by
  intro a ha
  obtain ⟨o, ho, hm⟩ := h a ha
  exact ⟨o, ho, le_trans hle hm⟩

/-- Every graph is certified at the bottom of the lifecycle. -/
theorem certified_hypothesis (g : KnowledgeGraph) : Certified g Maturity.hypothesis := by
  intro a ha
  obtain ⟨o, ho⟩ := exists_hasObject ha
  exact ⟨o, ho, Maturity.hypothesis_le _⟩

/-- Deleting an object preserves certification of the remaining ones. -/
theorem Certified.eraseObj {g : KnowledgeGraph} {m : Maturity} (h : Certified g m)
    (o : KnowledgeObject) : Certified (g.eraseObj o) m := by
  intro a ha
  obtain ⟨p, hp, hid⟩ := ((g.eraseObj o).mem_ids_iff a).1 ha
  have hpg : p ∈ g.objects := g.eraseObj_objects_subset o hp
  obtain ⟨q, hq, hm⟩ := h a ((g.mem_ids_iff a).2 ⟨p, hpg, hid⟩)
  have : q = p := g.unique_id q hq.1 p hpg (hq.2.trans hid.symm)
  exact ⟨p, ⟨hp, hid⟩, this ▸ hm⟩

/-! ## Grounding -/

/-- An object is *grounded* when everything it depends on is at least as mature
as the object itself: no claim rests on weaker evidence. -/
def Grounded (g : KnowledgeGraph) (a : ℕ) : Prop :=
  ∀ b, Depends g a b → ∀ oa ob, HasObject g a oa → HasObject g b ob →
    oa.maturity ≤ ob.maturity

/-- Along a dependency chain out of a grounded object the maturity never drops. -/
theorem maturity_le_of_depends {g : KnowledgeGraph} {a b : ℕ} (h : Grounded g a)
    (hab : Depends g a b) {oa ob : KnowledgeObject}
    (hoa : HasObject g a oa) (hob : HasObject g b ob) :
    oa.maturity ≤ ob.maturity := h b hab oa ob hoa hob

/-- If a grounded object is certified at level `m`, so is everything it depends
on. -/
theorem maturityAtLeast_of_depends {g : KnowledgeGraph} {m : Maturity} {a b : ℕ}
    (hg : Grounded g a) (hab : Depends g a b) (ha : MaturityAtLeast g m a) :
    MaturityAtLeast g m b := by
  obtain ⟨oa, hoa, hm⟩ := ha
  obtain ⟨ob, hob⟩ := exists_hasObject (mem_ids_of_depends hab).2
  exact ⟨ob, hob, le_trans hm (hg b hab oa ob hoa hob)⟩

/-- Objects with nothing below them are vacuously grounded. -/
theorem grounded_of_no_dependency {g : KnowledgeGraph} {a : ℕ}
    (h : ∀ c, ¬ DependsDirect g a c) : Grounded g a := by
  intro b hab
  cases hab with
  | single hac => exact absurd hac (h _)
  | tail hstep _ =>
      rcases Relation.TransGen.head'_iff.1 hstep with ⟨c, hc, -⟩
      exact absurd hc (h c)

/-! ## Confidence of dependency chains -/

/-- The confidence attached to an identifier, or `0` when it is unresolved. -/
noncomputable def confidenceOf (g : KnowledgeGraph) (a : ℕ) : ℤ :=
  open Classical in
  if h : ∃ o, HasObject g a o then h.choose.confidence else 0

theorem confidenceOf_eq {g : KnowledgeGraph} {a : ℕ} {o : KnowledgeObject}
    (ho : HasObject g a o) : confidenceOf g a = o.confidence := by
  classical
  have hex : ∃ p, HasObject g a p := ⟨o, ho⟩
  rw [confidenceOf, dif_pos hex]
  exact congrArg KnowledgeObject.confidence (hasObject_unique hex.choose_spec ho)

/-- The confidence of a chain of objects is bounded by that of each link. -/
theorem chain_confidence_le (g : KnowledgeGraph) (l : List ℕ) {a : ℕ} (ha : a ∈ l) :
    chainConfidence (l.map (confidenceOf g)) ≤ confidenceOf g a :=
  chainConfidence_le (List.mem_map_of_mem ha)

/-- Splitting a chain takes the minimum of the two halves. -/
theorem chain_confidence_append (g : KnowledgeGraph) (l₁ l₂ : List ℕ) :
    chainConfidence ((l₁ ++ l₂).map (confidenceOf g)) =
      min (chainConfidence (l₁.map (confidenceOf g)))
        (chainConfidence (l₂.map (confidenceOf g))) := by
  rw [List.map_append, chainConfidence_append]

end Polymath.Verification
