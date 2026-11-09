import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Polymath Core: a knowledge-graph ontology

This module fixes the vocabulary used throughout the project: the kinds of
knowledge objects, a linearly ordered maturity lifecycle, the kinds of
relations between objects, and a `KnowledgeGraph` structure carrying
referential-integrity obligations.
-/

namespace Polymath

/-- The eight kinds of knowledge object tracked by the ontology. -/
inductive ObjectKind
  | symbol | concept | mechanism | invariant | step | proof | observation | transformation
  deriving DecidableEq, Repr, Inhabited

/-- Maturity lifecycle of a knowledge object, from `hypothesis` to `axiomatic`. -/
inductive Maturity
  | hypothesis | prototype | validated | canonical | axiomatic
  deriving DecidableEq, Repr, Inhabited

/-- Numerical rank of a maturity level, used to linearly order `Maturity`. -/
def Maturity.rank : Maturity → ℕ
  | .hypothesis => 0
  | .prototype => 1
  | .validated => 2
  | .canonical => 3
  | .axiomatic => 4

theorem Maturity.rank_injective : Function.Injective Maturity.rank := by
  intro a b h
  cases a <;> cases b <;> simp [Maturity.rank] at h ⊢

instance : LinearOrder Maturity := LinearOrder.lift' Maturity.rank Maturity.rank_injective

theorem Maturity.le_iff_rank_le (a b : Maturity) : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

theorem Maturity.lt_iff_rank_lt (a b : Maturity) : a < b ↔ a.rank < b.rank := Iff.rfl

/-- The maturity levels form a strictly increasing chain. -/
theorem Maturity.lifecycle_chain :
    Maturity.hypothesis < Maturity.prototype ∧
    Maturity.prototype < Maturity.validated ∧
    Maturity.validated < Maturity.canonical ∧
    Maturity.canonical < Maturity.axiomatic := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Maturity.lt_iff_rank_lt, Maturity.rank]

theorem Maturity.hypothesis_le (a : Maturity) : Maturity.hypothesis ≤ a := by
  cases a <;> simp [Maturity.le_iff_rank_le, Maturity.rank]

theorem Maturity.le_axiomatic (a : Maturity) : a ≤ Maturity.axiomatic := by
  cases a <;> simp [Maturity.le_iff_rank_le, Maturity.rank]

/-- The nine kinds of relation between knowledge objects. -/
inductive RelationKind
  | uses | dependsOn | buildsOn | causes | explains | contradicts | «instanceOf» | partOf
  | similarTo
  deriving DecidableEq, Repr, Inhabited

/-- Structural relations describe how objects are assembled. -/
def RelationKind.isStructural : RelationKind → Bool
  | .uses | .dependsOn | .buildsOn | .instanceOf | .partOf => true
  | _ => false

/-- Causal relations describe how objects influence each other. -/
def RelationKind.isCausal : RelationKind → Bool
  | .causes | .explains | .contradicts => true
  | _ => false

/-- No relation kind is both structural and causal. -/
theorem RelationKind.structural_ne_causal (k : RelationKind) :
    ¬(k.isStructural = true ∧ k.isCausal = true) := by
  cases k <;> simp [RelationKind.isStructural, RelationKind.isCausal]

/-- A node of the knowledge graph. -/
structure KnowledgeObject where
  id : ℕ
  kind : ObjectKind
  label : String
  maturity : Maturity
  confidence : ℤ
  deriving DecidableEq, Repr

/-- A directed, kinded edge of the knowledge graph. -/
structure KnowledgeRelation where
  source : ℕ
  target : ℕ
  kind : RelationKind
  confidence : ℤ
  deriving DecidableEq, Repr

/-- A knowledge graph: objects with unique ids, and relations whose endpoints resolve. -/
structure KnowledgeGraph where
  objects : Finset KnowledgeObject
  relations : Finset KnowledgeRelation
  unique_id : ∀ a ∈ objects, ∀ b ∈ objects, a.id = b.id → a = b
  src_closed : ∀ r ∈ relations, ∃ o ∈ objects, o.id = r.source
  tgt_closed : ∀ r ∈ relations, ∃ o ∈ objects, o.id = r.target

namespace KnowledgeGraph

/-- The set of identifiers occurring in the graph. -/
def ids (g : KnowledgeGraph) : Finset ℕ := g.objects.image (·.id)

theorem mem_ids_iff (g : KnowledgeGraph) (n : ℕ) :
    n ∈ g.ids ↔ ∃ o ∈ g.objects, o.id = n := by
  simp [ids]

theorem src_mem_ids (g : KnowledgeGraph) {r : KnowledgeRelation} (hr : r ∈ g.relations) :
    r.source ∈ g.ids := by
  obtain ⟨o, ho, hid⟩ := g.src_closed r hr
  exact (g.mem_ids_iff _).2 ⟨o, ho, hid⟩

theorem tgt_mem_ids (g : KnowledgeGraph) {r : KnowledgeRelation} (hr : r ∈ g.relations) :
    r.target ∈ g.ids := by
  obtain ⟨o, ho, hid⟩ := g.tgt_closed r hr
  exact (g.mem_ids_iff _).2 ⟨o, ho, hid⟩

/-- Every relation has both endpoints present in the graph. -/
theorem relation_resolves (g : KnowledgeGraph) {r : KnowledgeRelation} (hr : r ∈ g.relations) :
    r.source ∈ g.ids ∧ r.target ∈ g.ids :=
  ⟨g.src_mem_ids hr, g.tgt_mem_ids hr⟩

/-- Lookup by identifier is unambiguous. -/
theorem lookup_unique (g : KnowledgeGraph) {a b : KnowledgeObject}
    (ha : a ∈ g.objects) (hb : b ∈ g.objects) (h : a.id = b.id) : a = b :=
  g.unique_id a ha b hb h

/-- A graph is normalized when `(kind, label)` also determines an object. -/
def Normalized (g : KnowledgeGraph) : Prop :=
  ∀ a ∈ g.objects, ∀ b ∈ g.objects, a.kind = b.kind → a.label = b.label → a = b

theorem normalized_lookup_unique {g : KnowledgeGraph} (hg : g.Normalized)
    {a b : KnowledgeObject} (ha : a ∈ g.objects) (hb : b ∈ g.objects)
    (hk : a.kind = b.kind) (hl : a.label = b.label) : a = b :=
  hg a ha b hb hk hl

/-- Remove an object together with every relation incident to it. -/
def eraseObj (g : KnowledgeGraph) (o : KnowledgeObject) : KnowledgeGraph where
  objects := g.objects.erase o
  relations := g.relations.filter (fun r => r.source ≠ o.id ∧ r.target ≠ o.id)
  unique_id := by
    intro a ha b hb h
    exact g.unique_id a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) h
  src_closed := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, hs, _⟩ := hr
    obtain ⟨p, hp, hid⟩ := g.src_closed r hr
    refine ⟨p, Finset.mem_erase.2 ⟨?_, hp⟩, hid⟩
    rintro rfl
    exact hs hid.symm
  tgt_closed := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hr, _, ht⟩ := hr
    obtain ⟨p, hp, hid⟩ := g.tgt_closed r hr
    refine ⟨p, Finset.mem_erase.2 ⟨?_, hp⟩, hid⟩
    rintro rfl
    exact ht hid.symm

theorem eraseObj_objects_subset (g : KnowledgeGraph) (o : KnowledgeObject) :
    (g.eraseObj o).objects ⊆ g.objects := Finset.erase_subset _ _

theorem eraseObj_relations_subset (g : KnowledgeGraph) (o : KnowledgeObject) :
    (g.eraseObj o).relations ⊆ g.relations := Finset.filter_subset _ _

theorem eraseObj_not_mem (g : KnowledgeGraph) (o : KnowledgeObject) :
    o ∉ (g.eraseObj o).objects := Finset.notMem_erase _ _

/-- Erasure preserves normalization. -/
theorem eraseObj_normalized {g : KnowledgeGraph} (hg : g.Normalized) (o : KnowledgeObject) :
    (g.eraseObj o).Normalized := by
  intro a ha b hb hk hl
  exact hg a (g.eraseObj_objects_subset o ha) b (g.eraseObj_objects_subset o hb) hk hl

end KnowledgeGraph

/-- Confidence of a chain of steps: the weakest link (with `0` as the empty bound). -/
def chainConfidence : List ℤ → ℤ
  | [] => 0
  | c :: t => min c (chainConfidence t)

theorem chainConfidence_le {l : List ℤ} {x : ℤ} (hx : x ∈ l) : chainConfidence l ≤ x := by
  induction l with
  | nil => cases hx
  | cons c t ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih hx)

theorem chainConfidence_nonpos (l : List ℤ) : chainConfidence l ≤ 0 := by
  induction l with
  | nil => simp [chainConfidence]
  | cons c t ih => exact le_trans (min_le_right _ _) ih

theorem chainConfidence_append (l₁ l₂ : List ℤ) :
    chainConfidence (l₁ ++ l₂) = min (chainConfidence l₁) (chainConfidence l₂) := by
  induction l₁ with
  | nil => simp [chainConfidence, min_eq_right (chainConfidence_nonpos l₂)]
  | cons c t ih => simp [chainConfidence, ih, min_assoc]

end Polymath
