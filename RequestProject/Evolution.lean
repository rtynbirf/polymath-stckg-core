import RequestProject.Certificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Evolution of a knowledge graph

Knowledge graphs grow by adding objects and relations, and by promoting the
maturity of objects already present.  This module makes both moves precise.

* `Extends` — the growth preorder on graphs, with `Extends.refl`,
  `Extends.trans`, `ids_subset` and monotonicity of the dependency relation
  (`dependsDirect_mono`, `depends_mono`);
* `promote` — raise the maturity of one object, leaving identifiers, relations
  and the dependency structure untouched (`promote_ids`, `promote_depends_iff`);
* `promote_maturity_le` and `certified_promote` — promotion never lowers
  maturity and preserves certification.
-/

namespace Polymath.Evolution

open Polymath Polymath.Dependency Polymath.Verification

/-- `h` extends `g` when it contains all of its objects and relations. -/
def Extends (g h : KnowledgeGraph) : Prop :=
  g.objects ⊆ h.objects ∧ g.relations ⊆ h.relations

theorem Extends.refl (g : KnowledgeGraph) : Extends g g := ⟨subset_rfl, subset_rfl⟩

theorem Extends.trans {g h k : KnowledgeGraph} (h₁ : Extends g h) (h₂ : Extends h k) :
    Extends g k := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem Extends.ids_subset {g h : KnowledgeGraph} (hgh : Extends g h) : g.ids ⊆ h.ids := by
  intro a ha
  obtain ⟨o, ho, hid⟩ := (g.mem_ids_iff a).1 ha
  exact (h.mem_ids_iff a).2 ⟨o, hgh.1 ho, hid⟩

theorem Extends.dependsDirect_mono {g h : KnowledgeGraph} (hgh : Extends g h) {a b : ℕ}
    (hab : DependsDirect g a b) : DependsDirect h a b := by
  obtain ⟨r, hr, hk, hs, ht⟩ := hab
  exact ⟨r, hgh.2 hr, hk, hs, ht⟩

theorem Extends.depends_mono {g h : KnowledgeGraph} (hgh : Extends g h) {a b : ℕ}
    (hab : Depends g a b) : Depends h a b := by
  induction hab with
  | single hab => exact depends_of_direct (hgh.dependsDirect_mono hab)
  | tail _ hbc ih => exact depends_trans ih (depends_of_direct (hgh.dependsDirect_mono hbc))

/-- Erasure is a step backwards along the growth preorder. -/
theorem extends_eraseObj (g : KnowledgeGraph) (o : KnowledgeObject) :
    Extends (g.eraseObj o) g :=
  ⟨g.eraseObj_objects_subset o, g.eraseObj_relations_subset o⟩

/-! ## Promotion -/

/-- The object `o` with its maturity raised to `m`. -/
def promoteObj (o : KnowledgeObject) (m : Maturity) : KnowledgeObject :=
  { o with maturity := m }

@[simp] theorem promoteObj_id (o : KnowledgeObject) (m : Maturity) :
    (promoteObj o m).id = o.id := rfl

@[simp] theorem promoteObj_maturity (o : KnowledgeObject) (m : Maturity) :
    (promoteObj o m).maturity = m := rfl


/-- Raise the maturity of one object of the graph.  The membership hypothesis is
what keeps identifiers unique after the replacement. -/
def promote (g : KnowledgeGraph) {o : KnowledgeObject} (ho : o ∈ g.objects)
    (m : Maturity) : KnowledgeGraph where
  objects := insert (promoteObj o m) (g.objects.erase o)
  relations := g.relations
  unique_id := by
    classical
    have key : ∀ p ∈ g.objects.erase o, p.id = o.id → False := by
      intro p hp hid
      exact (Finset.mem_erase.1 hp).1
        (g.unique_id p (Finset.mem_of_mem_erase hp) o ho hid)
    intro a ha b hb hab
    rcases Finset.mem_insert.1 ha with rfl | ha'
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · rfl
      · exact absurd (key b hb' hab.symm) not_false
    · rcases Finset.mem_insert.1 hb with rfl | hb'
      · exact absurd (key a ha' hab) not_false
      · exact g.unique_id a (Finset.mem_of_mem_erase ha') b (Finset.mem_of_mem_erase hb') hab
  src_closed := by
    classical
    intro r hr
    obtain ⟨p, hp, hid⟩ := g.src_closed r hr
    by_cases hpo : p = o
    · exact ⟨promoteObj o m, Finset.mem_insert_self _ _, by simpa [hpo] using hid⟩
    · exact ⟨p, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hpo, hp⟩), hid⟩
  tgt_closed := by
    classical
    intro r hr
    obtain ⟨p, hp, hid⟩ := g.tgt_closed r hr
    by_cases hpo : p = o
    · exact ⟨promoteObj o m, Finset.mem_insert_self _ _, by simpa [hpo] using hid⟩
    · exact ⟨p, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hpo, hp⟩), hid⟩

@[simp] theorem promote_relations (g : KnowledgeGraph) {o : KnowledgeObject}
    (ho : o ∈ g.objects) (m : Maturity) : (promote g ho m).relations = g.relations := rfl

/-- Promotion leaves the identifiers of the graph unchanged. -/
theorem promote_ids {g : KnowledgeGraph} {o : KnowledgeObject} (ho : o ∈ g.objects)
    (m : Maturity) : (promote g ho m).ids = g.ids := by
  classical
  ext a
  simp only [KnowledgeGraph.mem_ids_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases Finset.mem_insert.1 hp with rfl | hp'
    · exact ⟨o, ho, rfl⟩
    · exact ⟨p, Finset.mem_of_mem_erase hp', rfl⟩
  · rintro ⟨p, hp, rfl⟩
    by_cases hpo : p = o
    · exact ⟨promoteObj o m, Finset.mem_insert_self _ _, by simp [hpo]⟩
    · exact ⟨p, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hpo, hp⟩), rfl⟩

/-- Promotion does not change the dependency structure. -/
theorem promote_dependsDirect_iff (g : KnowledgeGraph) {o : KnowledgeObject}
    (ho : o ∈ g.objects) (m : Maturity) (a b : ℕ) :
    DependsDirect (promote g ho m) a b ↔ DependsDirect g a b := Iff.rfl

theorem promote_depends_iff (g : KnowledgeGraph) {o : KnowledgeObject}
    (ho : o ∈ g.objects) (m : Maturity) (a b : ℕ) :
    Depends (promote g ho m) a b ↔ Depends g a b := Iff.rfl

/-- Promotion preserves acyclicity. -/
theorem promote_acyclic {g : KnowledgeGraph} (hg : Acyclic g) {o : KnowledgeObject}
    (ho : o ∈ g.objects) (m : Maturity) : Acyclic (promote g ho m) := hg

/-- The promoted object resolves the identifier it had before. -/
theorem hasObject_promote (g : KnowledgeGraph) {o : KnowledgeObject} (ho : o ∈ g.objects)
    (m : Maturity) : HasObject (promote g ho m) o.id (promoteObj o m) :=
  ⟨Finset.mem_insert_self _ _, rfl⟩

/-- Promotion never lowers the maturity of the promoted object. -/
theorem promote_maturity_le {g : KnowledgeGraph} {o : KnowledgeObject} (ho : o ∈ g.objects)
    {m : Maturity} (hm : o.maturity ≤ m) :
    ∃ p, HasObject (promote g ho m) o.id p ∧ o.maturity ≤ p.maturity :=
  ⟨promoteObj o m, hasObject_promote g ho m, hm⟩

/-- Promotion preserves certification, provided the new level is at least the
certified one. -/
theorem certified_promote {g : KnowledgeGraph} {lvl : Maturity} (hc : Certified g lvl)
    {o : KnowledgeObject} (ho : o ∈ g.objects) {m : Maturity} (hm : lvl ≤ m) :
    Certified (promote g ho m) lvl := by
  classical
  intro a ha
  rw [promote_ids ho m] at ha
  obtain ⟨p, hp, hpm⟩ := hc a ha
  by_cases hpo : p = o
  · refine ⟨promoteObj o m, ⟨Finset.mem_insert_self _ _, ?_⟩, hm⟩
    simpa [promoteObj, hpo] using hp.2
  · exact ⟨p, ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hpo, hp.1⟩), hp.2⟩, hpm⟩

/-- Promotion to the top of the lifecycle makes the promoted object axiomatic. -/
theorem promote_axiomatic_maturity (g : KnowledgeGraph) {o : KnowledgeObject}
    (ho : o ∈ g.objects) :
    ∃ p, HasObject (promote g ho Maturity.axiomatic) o.id p ∧
      p.maturity = Maturity.axiomatic :=
  ⟨promoteObj o Maturity.axiomatic, hasObject_promote g ho Maturity.axiomatic, rfl⟩

end Polymath.Evolution
