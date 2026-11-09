import RequestProject.Collective

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Scale: how large can a knowledge graph be?

Referential integrity bounds the shape of a graph by the number of identifiers
it carries.

* `card_ids_le` — there are no more identifiers than objects (with equality for
  a graph whose identifiers are unique, `card_ids_eq`);
* `card_edgeShapes_le` — the number of distinct `(source, target, kind)` edge
  shapes is at most `9 * |ids|²`;
* `card_relations_le_of_simple` — a *simple* graph, one without parallel edges
  of the same kind and confidence, has at most `9 * |ids|²` relations.
-/

namespace Polymath.Scale

open Polymath

/-- The nine relation kinds. -/
instance : Fintype RelationKind where
  elems := {.uses, .dependsOn, .buildsOn, .causes, .explains, .contradicts, .instanceOf,
    .partOf, .similarTo}
  complete := by intro k; cases k <;> decide

theorem card_relationKind : Fintype.card RelationKind = 9 := by decide

theorem card_ids_le (g : KnowledgeGraph) : g.ids.card ≤ g.objects.card :=
  Finset.card_image_le

/-- Identifiers are in bijection with objects. -/
theorem card_ids_eq (g : KnowledgeGraph) : g.ids.card = g.objects.card := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb hab
  exact g.unique_id a ha b hb hab

/-- The shape of a relation: its endpoints and its kind. -/
def edgeShape (r : KnowledgeRelation) : ℕ × ℕ × RelationKind := (r.source, r.target, r.kind)

/-- Every edge shape of the graph lies in `ids × ids × kinds`. -/
theorem edgeShapes_subset (g : KnowledgeGraph) :
    g.relations.image edgeShape ⊆ g.ids ×ˢ (g.ids ×ˢ (Finset.univ : Finset RelationKind)) := by
  classical
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
  simp only [edgeShape, Finset.mem_product, Finset.mem_univ, and_true]
  exact ⟨g.src_mem_ids hr, g.tgt_mem_ids hr⟩

/-- A graph on `n` identifiers has at most `9 n²` distinct edge shapes. -/
theorem card_edgeShapes_le (g : KnowledgeGraph) :
    (g.relations.image edgeShape).card ≤ 9 * (g.ids.card * g.ids.card) := by
  classical
  have h := Finset.card_le_card (edgeShapes_subset g)
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, card_relationKind] at h
  calc (g.relations.image edgeShape).card
      ≤ g.ids.card * (g.ids.card * 9) := h
    _ = 9 * (g.ids.card * g.ids.card) := by ring

/-- A graph is *simple* when the shape of a relation determines it: no parallel
edges of the same kind. -/
def Simple (g : KnowledgeGraph) : Prop :=
  ∀ r ∈ g.relations, ∀ s ∈ g.relations, edgeShape r = edgeShape s → r = s

/-- A simple graph on `n` identifiers has at most `9 n²` relations. -/
theorem card_relations_le_of_simple {g : KnowledgeGraph} (hg : Simple g) :
    g.relations.card ≤ 9 * (g.ids.card * g.ids.card) := by
  classical
  have hinj : (g.relations.image edgeShape).card = g.relations.card :=
    Finset.card_image_of_injOn (fun r hr s hs h => hg r hr s hs h)
  rw [← hinj]
  exact card_edgeShapes_le g

/-- Objects and relations of a graph both bound the graph obtained by merging it
with another one. -/
theorem card_merge_le {g h : KnowledgeGraph} (hc : Collective.Compatible g h) :
    (Collective.merge g h hc).objects.card ≤ g.objects.card + h.objects.card := by
  simpa [Collective.merge_objects] using Finset.card_union_le g.objects h.objects

end Polymath.Scale
