import RequestProject.Agents

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Collective knowledge: merging graphs

Two graphs can be merged when they agree on the objects they share, i.e. when an
identifier occurring in both resolves to the same object (`Compatible`).  The
merge is then again a knowledge graph, and it is the least upper bound of the
two in the growth preorder.

* `graph_ext` — a knowledge graph is determined by its objects and relations;
* `merge`, `extends_merge_left/right`, `merge_least` — the merge is a join;
* `merge_comm`, `merge_self` — commutativity and idempotence;
* `merge_certified` — a merge of certified graphs is certified;
* `mergeAgent` — merging with a fixed background graph is an agent.
-/

namespace Polymath.Collective

open Polymath Polymath.Verification Polymath.Evolution Polymath.Agents

/-- A knowledge graph is determined by its objects and its relations. -/
theorem graph_ext {g h : KnowledgeGraph} (ho : g.objects = h.objects)
    (hr : g.relations = h.relations) : g = h := by
  cases g; cases h; cases ho; cases hr; rfl

/-- Two graphs are compatible when shared identifiers resolve to the same object. -/
def Compatible (g h : KnowledgeGraph) : Prop :=
  ∀ a ∈ g.objects, ∀ b ∈ h.objects, a.id = b.id → a = b

theorem Compatible.symm {g h : KnowledgeGraph} (hc : Compatible g h) : Compatible h g :=
  fun a ha b hb hid => (hc b hb a ha hid.symm).symm

theorem compatible_self (g : KnowledgeGraph) : Compatible g g := g.unique_id

/-- The union of two compatible knowledge graphs. -/
def merge (g h : KnowledgeGraph) (hc : Compatible g h) : KnowledgeGraph where
  objects := g.objects ∪ h.objects
  relations := g.relations ∪ h.relations
  unique_id := by
    intro a ha b hb hid
    rcases Finset.mem_union.1 ha with ha' | ha' <;> rcases Finset.mem_union.1 hb with hb' | hb'
    · exact g.unique_id a ha' b hb' hid
    · exact hc a ha' b hb' hid
    · exact (hc b hb' a ha' hid.symm).symm
    · exact h.unique_id a ha' b hb' hid
  src_closed := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr' | hr'
    · obtain ⟨o, ho, hid⟩ := g.src_closed r hr'
      exact ⟨o, Finset.mem_union_left _ ho, hid⟩
    · obtain ⟨o, ho, hid⟩ := h.src_closed r hr'
      exact ⟨o, Finset.mem_union_right _ ho, hid⟩
  tgt_closed := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr' | hr'
    · obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr'
      exact ⟨o, Finset.mem_union_left _ ho, hid⟩
    · obtain ⟨o, ho, hid⟩ := h.tgt_closed r hr'
      exact ⟨o, Finset.mem_union_right _ ho, hid⟩

@[simp] theorem merge_objects (g h : KnowledgeGraph) (hc : Compatible g h) :
    (merge g h hc).objects = g.objects ∪ h.objects := rfl

@[simp] theorem merge_relations (g h : KnowledgeGraph) (hc : Compatible g h) :
    (merge g h hc).relations = g.relations ∪ h.relations := rfl

theorem extends_merge_left (g h : KnowledgeGraph) (hc : Compatible g h) :
    Extends g (merge g h hc) := ⟨Finset.subset_union_left, Finset.subset_union_left⟩

theorem extends_merge_right (g h : KnowledgeGraph) (hc : Compatible g h) :
    Extends h (merge g h hc) := ⟨Finset.subset_union_right, Finset.subset_union_right⟩

/-- The merge is the least common extension. -/
theorem merge_least {g h k : KnowledgeGraph} (hc : Compatible g h)
    (hg : Extends g k) (hh : Extends h k) : Extends (merge g h hc) k :=
  ⟨Finset.union_subset hg.1 hh.1, Finset.union_subset hg.2 hh.2⟩

theorem merge_comm (g h : KnowledgeGraph) (hc : Compatible g h) :
    merge g h hc = merge h g hc.symm :=
  graph_ext (Finset.union_comm _ _) (Finset.union_comm _ _)

theorem merge_self (g : KnowledgeGraph) : merge g g (compatible_self g) = g :=
  graph_ext (Finset.union_self _) (Finset.union_self _)

theorem merge_ids (g h : KnowledgeGraph) (hc : Compatible g h) :
    (merge g h hc).ids = g.ids ∪ h.ids := by
  simp [KnowledgeGraph.ids, Finset.image_union]

/-- A merge of graphs certified at level `m` is certified at level `m`. -/
theorem merge_certified {g h : KnowledgeGraph} {m : Maturity} (hc : Compatible g h)
    (hg : Certified g m) (hh : Certified h m) : Certified (merge g h hc) m := by
  intro a ha
  rw [merge_ids] at ha
  rcases Finset.mem_union.1 ha with ha' | ha'
  · obtain ⟨o, ho, hm⟩ := hg a ha'
    exact ⟨o, ⟨Finset.mem_union_left _ ho.1, ho.2⟩, hm⟩
  · obtain ⟨o, ho, hm⟩ := hh a ha'
    exact ⟨o, ⟨Finset.mem_union_right _ ho.1, ho.2⟩, hm⟩

/-- Merging in a fixed background graph, when compatible with everything in
sight, is an agent. -/
def mergeAgent (b : KnowledgeGraph) (hb : ∀ g, Compatible g b) : Agent where
  act := fun g => merge g b (hb g)
  monotone := fun g => extends_merge_left g b (hb g)

theorem mergeAgent_act (b : KnowledgeGraph) (hb : ∀ g, Compatible g b) (g : KnowledgeGraph) :
    (mergeAgent b hb).act g = merge g b (hb g) := rfl

/-- A background graph already contained in `g` leaves `g` unchanged. -/
theorem mergeAgent_fixed {b : KnowledgeGraph} (hb : ∀ g, Compatible g b) {g : KnowledgeGraph}
    (hsub : Extends b g) : (mergeAgent b hb).Fixed g :=
  graph_ext (Finset.union_eq_left.2 hsub.1) (Finset.union_eq_left.2 hsub.2)

end Polymath.Collective
