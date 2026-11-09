import RequestProject.Agents

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The genesis engine: creating new knowledge

New objects must not collide with old ones.  `freshId` returns an identifier
strictly larger than every identifier in use, so inserting an object under it
keeps referential integrity.

* `freshId_notMem` — the fresh identifier is genuinely unused;
* `insertFresh` — the extended graph, with its integrity obligations proved;
* `insertFresh_extends`, `insertFresh_ids`, `insertFresh_card` — the extension
  adds exactly one object;
* `genesisAgent` — creation packaged as an agent, and `genesisAgent_not_fixed`:
  the engine never runs out of things to create.
-/

namespace PolymathAtlas.Gestalt.Genesis

open Polymath Polymath.Evolution Polymath.Agents

/-- An identifier larger than every identifier in use. -/
def freshId (g : KnowledgeGraph) : ℕ := g.ids.sup id + 1

theorem freshId_notMem (g : KnowledgeGraph) : freshId g ∉ g.ids := by
  intro h
  have hle : freshId g ≤ g.ids.sup id := Finset.le_sup (f := id) h
  rw [freshId] at hle
  omega

theorem lt_freshId {g : KnowledgeGraph} {a : ℕ} (ha : a ∈ g.ids) : a < freshId g :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)

/-- The object created by the engine. -/
def freshObject (g : KnowledgeGraph) (k : ObjectKind) (label : String) : KnowledgeObject :=
  { id := freshId g, kind := k, label := label, maturity := .hypothesis, confidence := 0 }

/-- Insert a new object under a fresh identifier. -/
def insertFresh (g : KnowledgeGraph) (k : ObjectKind) (label : String) : KnowledgeGraph where
  objects := insert (freshObject g k label) g.objects
  relations := g.relations
  unique_id := by
    classical
    have hne : ∀ p ∈ g.objects, p.id ≠ freshId g := by
      intro p hp hid
      exact freshId_notMem g ((g.mem_ids_iff _).2 ⟨p, hp, hid⟩)
    intro a ha b hb hab
    rcases Finset.mem_insert.1 ha with rfl | ha' <;> rcases Finset.mem_insert.1 hb with rfl | hb'
    · rfl
    · exact absurd hab.symm (hne b hb')
    · exact absurd hab (hne a ha')
    · exact g.unique_id a ha' b hb' hab
  src_closed := by
    intro r hr
    obtain ⟨o, ho, hid⟩ := g.src_closed r hr
    exact ⟨o, Finset.mem_insert_of_mem ho, hid⟩
  tgt_closed := by
    intro r hr
    obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr
    exact ⟨o, Finset.mem_insert_of_mem ho, hid⟩

theorem insertFresh_extends (g : KnowledgeGraph) (k : ObjectKind) (label : String) :
    Extends g (insertFresh g k label) := ⟨Finset.subset_insert _ _, subset_rfl⟩

theorem insertFresh_ids (g : KnowledgeGraph) (k : ObjectKind) (label : String) :
    (insertFresh g k label).ids = insert (freshId g) g.ids := by
  classical
  ext a
  rw [KnowledgeGraph.mem_ids_iff, Finset.mem_insert]
  constructor
  · rintro ⟨o, ho, rfl⟩
    have hmem : o ∈ insert (freshObject g k label) g.objects := ho
    rcases Finset.mem_insert.1 hmem with rfl | ho'
    · exact Or.inl rfl
    · exact Or.inr ((g.mem_ids_iff o.id).2 ⟨o, ho', rfl⟩)
  · rintro (rfl | ha)
    · exact ⟨freshObject g k label, Finset.mem_insert_self _ _, rfl⟩
    · obtain ⟨o, ho, hid⟩ := (g.mem_ids_iff a).1 ha
      exact ⟨o, Finset.mem_insert_of_mem ho, hid⟩

theorem insertFresh_card (g : KnowledgeGraph) (k : ObjectKind) (label : String) :
    (insertFresh g k label).objects.card = g.objects.card + 1 := by
  classical
  have hnot : freshObject g k label ∉ g.objects := by
    intro hmem
    exact freshId_notMem g ((g.mem_ids_iff _).2 ⟨_, hmem, rfl⟩)
  simpa [insertFresh] using Finset.card_insert_of_notMem hnot

/-- Creation, packaged as an agent. -/
def genesisAgent (k : ObjectKind) (label : String) : Agent where
  act := fun g => insertFresh g k label
  monotone := fun g => insertFresh_extends g k label

/-- The genesis engine always has something to add: it has no fixed point. -/
theorem genesisAgent_not_fixed (k : ObjectKind) (label : String) (g : KnowledgeGraph) :
    ¬ (genesisAgent k label).Fixed g := by
  intro h
  have hcard := insertFresh_card g k label
  have heq : insertFresh g k label = g := h
  rw [heq] at hcard
  omega

/-- After `n` creation steps the graph has grown by exactly `n` objects. -/
theorem genesisAgent_run_card (k : ObjectKind) (label : String) (g : KnowledgeGraph) (n : ℕ) :
    ((genesisAgent k label).run g n).objects.card = g.objects.card + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Agent.run_succ]
      show (insertFresh ((genesisAgent k label).run g n) k label).objects.card = _
      rw [insertFresh_card, ih]
      omega

end PolymathAtlas.Gestalt.Genesis
