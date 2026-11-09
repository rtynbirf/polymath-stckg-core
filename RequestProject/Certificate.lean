import RequestProject.Verification

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Acyclicity certificates

A `Layering` of a knowledge graph (see `RequestProject.Dependency`) is a level
assignment that strictly decreases along every structural edge; it is the
standard certificate of acyclicity.  This module proves that the certificate is
*complete*: a finite acyclic graph always admits a layering, obtained by
counting how many objects an identifier depends on.

* `depCount` — the number of graph objects an identifier depends on;
* `depCount_lt_of_dependsDirect` — a direct dependency strictly decreases the
  count, so `depCount` is a layering;
* `exists_layering_of_acyclic` and `acyclic_iff_nonempty_layering` — acyclicity
  is *equivalent* to the existence of a certificate;
* `Certificate` — a layering bundled with a certified maturity level, with
  `Certificate.acyclic` and `Certificate.certified` extracting the two
  guarantees.
-/

namespace Polymath.Certificates

open Polymath Polymath.Dependency Polymath.Verification

/-- The number of objects of the graph that `a` depends on. -/
noncomputable def depCount (g : KnowledgeGraph) (a : ℕ) : ℕ :=
  open Classical in (g.ids.filter (fun b => Depends g a b)).card

/-- Everything `b` depends on is also something `a` depends on, when `a` depends
on `b`. -/
theorem depFilter_subset {g : KnowledgeGraph} {a b : ℕ} (hab : Depends g a b) :
    open Classical in
    (g.ids.filter (fun c => Depends g b c)) ⊆ (g.ids.filter (fun c => Depends g a c)) := by
  classical
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, depends_trans hab hc.2⟩

/-- In an acyclic graph a direct dependency strictly decreases the dependency
count. -/
theorem depCount_lt_of_dependsDirect {g : KnowledgeGraph} (hg : Acyclic g) {a b : ℕ}
    (h : DependsDirect g a b) : depCount g b < depCount g a := by
  classical
  have hab : Depends g a b := depends_of_direct h
  have hb : b ∈ g.ids := (mem_ids_of_dependsDirect h).2
  refine Finset.card_lt_card ?_
  refine ⟨depFilter_subset hab, ?_⟩
  intro hsub
  have hmem : b ∈ g.ids.filter (fun c => Depends g a c) := Finset.mem_filter.2 ⟨hb, hab⟩
  have : b ∈ g.ids.filter (fun c => Depends g b c) := hsub hmem
  exact hg b (Finset.mem_filter.1 this).2

/-- Counting dependencies produces a layering of any acyclic graph. -/
noncomputable def countLayering {g : KnowledgeGraph} (hg : Acyclic g) : Layering g where
  level := depCount g
  decreasing := fun _ _ h => depCount_lt_of_dependsDirect hg h

/-- Every finite acyclic knowledge graph admits an acyclicity certificate. -/
theorem exists_layering_of_acyclic {g : KnowledgeGraph} (hg : Acyclic g) :
    Nonempty (Layering g) := ⟨countLayering hg⟩

/-- Acyclicity and the existence of a layering certificate are equivalent. -/
theorem acyclic_iff_nonempty_layering (g : KnowledgeGraph) :
    Acyclic g ↔ Nonempty (Layering g) :=
  ⟨exists_layering_of_acyclic, fun ⟨L⟩ => acyclic_of_layering L⟩

/-- Along a whole dependency chain the dependency count strictly decreases. -/
theorem depCount_lt_of_depends {g : KnowledgeGraph} (hg : Acyclic g) {a b : ℕ}
    (h : Depends g a b) : depCount g b < depCount g a :=
  level_lt_of_depends (countLayering hg) h

/-! ## Bundled certificates -/

/-- A certificate of a knowledge graph: a layering witnessing acyclicity together
with a maturity level reached by every object. -/
structure Certificate (g : KnowledgeGraph) where
  /-- The acyclicity witness. -/
  layering : Layering g
  /-- The certified maturity level. -/
  level : Maturity
  /-- Every object of the graph has reached `level`. -/
  certified : Certified g level

/-- A certificate witnesses acyclicity. -/
theorem Certificate.acyclic {g : KnowledgeGraph} (c : Certificate g) : Acyclic g :=
  acyclic_of_layering c.layering

/-- A certificate can always be weakened to a lower maturity requirement. -/
def Certificate.weaken {g : KnowledgeGraph} (c : Certificate g) {m : Maturity}
    (hm : m ≤ c.level) : Certificate g where
  layering := c.layering
  level := m
  certified := c.certified.mono hm

/-- Every acyclic graph carries at least the trivial certificate. -/
theorem exists_certificate_of_acyclic {g : KnowledgeGraph} (hg : Acyclic g) :
    Nonempty (Certificate g) :=
  ⟨{ layering := countLayering hg
     level := Maturity.hypothesis
     certified := certified_hypothesis g }⟩

/-- A certified acyclic graph has a leaf, and everything the graph contains is
certified at the recorded level. -/
theorem Certificate.leaf_exists {g : KnowledgeGraph} (c : Certificate g) {a : ℕ}
    (ha : a ∈ g.ids) : ∃ b ∈ g.ids, (∀ d, ¬ DependsDirect g b d) ∧
      MaturityAtLeast g c.level b := by
  obtain ⟨b, hb, hleaf⟩ := exists_leaf c.acyclic ha
  exact ⟨b, hb, hleaf, c.certified b hb⟩

end Polymath.Certificates
