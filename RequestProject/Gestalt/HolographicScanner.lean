import RequestProject.Dedup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The holographic scanner

Scanning a knowledge graph forgets identifiers and confidences and keeps only
*what* is recorded: the set of `(kind, label)` pairs.

* `scan`, `mem_scan_iff` — the scan of a graph;
* `scan_mono` — growth never loses content;
* `scan_card_le_card` — the scan is no larger than the graph;
* `exists_normalized_scan_eq` — deduplication is *holographic*: some normalized
  subgraph has exactly the same scan, so nothing is lost by removing duplicates;
* `normalized_scan_card` — on a normalized graph the scan has one entry per
  object.
-/

namespace PolymathAtlas.Gestalt.Scanner

open Polymath Polymath.Evolution Polymath.Dedup

/-- The content of a knowledge graph: its `(kind, label)` pairs. -/
noncomputable def scan (g : KnowledgeGraph) : Finset (ObjectKind × String) :=
  open Classical in g.objects.image (fun o => (o.kind, o.label))

theorem mem_scan_iff {g : KnowledgeGraph} {p : ObjectKind × String} :
    p ∈ scan g ↔ ∃ o ∈ g.objects, (o.kind, o.label) = p := by
  classical
  simp [scan]

/-- Growth never loses content. -/
theorem scan_mono {g h : KnowledgeGraph} (hgh : Extends g h) : scan g ⊆ scan h := by
  classical
  intro p hp
  obtain ⟨o, ho, rfl⟩ := mem_scan_iff.1 hp
  exact mem_scan_iff.2 ⟨o, hgh.1 ho, rfl⟩

theorem scan_card_le_card (g : KnowledgeGraph) : (scan g).card ≤ g.objects.card := by
  classical
  exact Finset.card_image_le

/-- Deduplication is holographic: a normalized subgraph records exactly the same
content. -/
theorem exists_normalized_scan_eq (g : KnowledgeGraph) :
    ∃ h : KnowledgeGraph, h.Normalized ∧ Extends h g ∧ scan h = scan g := by
  classical
  obtain ⟨h, hnorm, hext, hcov⟩ := exists_normalized_retraction g
  refine ⟨h, hnorm, hext, Finset.Subset.antisymm (scan_mono hext) ?_⟩
  intro p hp
  obtain ⟨o, ho, rfl⟩ := mem_scan_iff.1 hp
  obtain ⟨q, hq, hk, hl⟩ := hcov o ho
  exact mem_scan_iff.2 ⟨q, hq, by rw [hk, hl]⟩

/-- On a normalized graph the scan is faithful: one entry per object. -/
theorem normalized_scan_card {g : KnowledgeGraph} (hg : g.Normalized) :
    (scan g).card = g.objects.card := by
  classical
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb hab
  exact hg a ha b hb (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- Erasing an object can only shrink the scan. -/
theorem scan_eraseObj_subset (g : KnowledgeGraph) (o : KnowledgeObject) :
    scan (g.eraseObj o) ⊆ scan g := scan_mono (extends_eraseObj g o)

/-- Two graphs with the same scan record the same content, entry by entry. -/
theorem scan_eq_iff (g h : KnowledgeGraph) :
    scan g = scan h ↔
      ∀ k l, (∃ o ∈ g.objects, o.kind = k ∧ o.label = l) ↔
        (∃ o ∈ h.objects, o.kind = k ∧ o.label = l) := by
  constructor
  · intro hs k l
    constructor
    · rintro ⟨o, ho, rfl, rfl⟩
      obtain ⟨q, hq, hqk⟩ := mem_scan_iff.1 (hs ▸ mem_scan_iff.2 ⟨o, ho, rfl⟩)
      exact ⟨q, hq, congrArg Prod.fst hqk, congrArg Prod.snd hqk⟩
    · rintro ⟨o, ho, rfl, rfl⟩
      obtain ⟨q, hq, hqk⟩ := mem_scan_iff.1 (hs ▸ mem_scan_iff.2 ⟨o, ho, rfl⟩ : _ ∈ scan g)
      exact ⟨q, hq, congrArg Prod.fst hqk, congrArg Prod.snd hqk⟩
  · intro hall
    ext p
    constructor
    · intro hp
      obtain ⟨o, ho, rfl⟩ := mem_scan_iff.1 hp
      obtain ⟨q, hq, hk, hl⟩ := (hall o.kind o.label).1 ⟨o, ho, rfl, rfl⟩
      exact mem_scan_iff.2 ⟨q, hq, by rw [hk, hl]⟩
    · intro hp
      obtain ⟨o, ho, rfl⟩ := mem_scan_iff.1 hp
      obtain ⟨q, hq, hk, hl⟩ := (hall o.kind o.label).2 ⟨o, ho, rfl, rfl⟩
      exact mem_scan_iff.2 ⟨q, hq, by rw [hk, hl]⟩

end PolymathAtlas.Gestalt.Scanner
