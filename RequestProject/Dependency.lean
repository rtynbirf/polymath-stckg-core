import RequestProject.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Dependency structure of a knowledge graph

The structural relations of a `KnowledgeGraph` induce a dependency relation on
object identifiers: `DependsDirect g a b` when some structural edge points from
`a` to `b`, and `Depends g` is its transitive closure.

Main results:

* `acyclic_of_layering` / `level_lt_of_depends` — a layering (a level assignment
  strictly decreasing along edges) certifies acyclicity, and the certificate
  propagates along whole dependency chains;
* `exists_root` and `exists_leaf` — a finite acyclic dependency graph always has
  an object that nothing depends on, and an object that depends on nothing.
-/

namespace Polymath.Dependency

open Polymath

/-- `a` directly depends on `b`: some structural relation of the graph points
from `a` to `b`. -/
def DependsDirect (g : KnowledgeGraph) (a b : ℕ) : Prop :=
  ∃ r ∈ g.relations, r.kind.isStructural = true ∧ r.source = a ∧ r.target = b

instance (g : KnowledgeGraph) (a b : ℕ) : Decidable (DependsDirect g a b) := by
  unfold DependsDirect; infer_instance

/-- The dependency relation: the transitive closure of direct dependency. -/
def Depends (g : KnowledgeGraph) : ℕ → ℕ → Prop := Relation.TransGen (DependsDirect g)

theorem depends_of_direct {g : KnowledgeGraph} {a b : ℕ} (h : DependsDirect g a b) :
    Depends g a b := Relation.TransGen.single h

theorem depends_trans {g : KnowledgeGraph} {a b c : ℕ} (h₁ : Depends g a b)
    (h₂ : Depends g b c) : Depends g a c := Relation.TransGen.trans h₁ h₂

/-- Both endpoints of a direct dependency are objects of the graph. -/
theorem mem_ids_of_dependsDirect {g : KnowledgeGraph} {a b : ℕ} (h : DependsDirect g a b) :
    a ∈ g.ids ∧ b ∈ g.ids := by
  obtain ⟨r, hr, _, hs, ht⟩ := h
  exact ⟨hs ▸ g.src_mem_ids hr, ht ▸ g.tgt_mem_ids hr⟩

theorem mem_ids_of_depends {g : KnowledgeGraph} {a b : ℕ} (h : Depends g a b) :
    a ∈ g.ids ∧ b ∈ g.ids := by
  induction h with
  | single hab => exact mem_ids_of_dependsDirect hab
  | tail _ hbc ih => exact ⟨ih.1, (mem_ids_of_dependsDirect hbc).2⟩

/-! ## Acyclicity and layerings -/

/-- A graph is acyclic when nothing depends on itself. -/
def Acyclic (g : KnowledgeGraph) : Prop := ∀ a : ℕ, ¬ Depends g a a

/-- A layering assigns a level to every identifier so that dependencies strictly
decrease the level. -/
structure Layering (g : KnowledgeGraph) where
  /-- The level of an identifier. -/
  level : ℕ → ℕ
  /-- Every direct dependency strictly decreases the level. -/
  decreasing : ∀ a b, DependsDirect g a b → level b < level a

/-- Levels strictly decrease along whole dependency chains. -/
theorem level_lt_of_depends {g : KnowledgeGraph} (L : Layering g) {a b : ℕ}
    (h : Depends g a b) : L.level b < L.level a := by
  induction h with
  | single hab => exact L.decreasing _ _ hab
  | tail _ hbc ih => exact lt_trans (L.decreasing _ _ hbc) ih

/-- A layering certifies acyclicity. -/
theorem acyclic_of_layering {g : KnowledgeGraph} (L : Layering g) : Acyclic g :=
  fun _ h => lt_irrefl _ (level_lt_of_depends L h)

/-! ## Roots and leaves of a finite acyclic graph -/

/-- The dependency relation restricted to the (finite) identifiers of the graph. -/
private def depSub (g : KnowledgeGraph) (x y : {n : ℕ // n ∈ g.ids}) : Prop :=
  Depends g x.1 y.1

private theorem depSub_wellFounded {g : KnowledgeGraph} (hg : Acyclic g) :
    WellFounded (depSub g) := by
  haveI : IsTrans {n : ℕ // n ∈ g.ids} (depSub g) := ⟨fun _ _ _ h₁ h₂ => depends_trans h₁ h₂⟩
  haveI : Std.Irrefl (depSub g) := ⟨fun x h => hg x.1 h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

private theorem depSubFlip_wellFounded {g : KnowledgeGraph} (hg : Acyclic g) :
    WellFounded (fun x y : {n : ℕ // n ∈ g.ids} => depSub g y x) := by
  haveI : IsTrans {n : ℕ // n ∈ g.ids} (fun x y : {n : ℕ // n ∈ g.ids} => depSub g y x) :=
    ⟨fun _ _ _ h₁ h₂ => depends_trans h₂ h₁⟩
  haveI : Std.Irrefl (fun x y : {n : ℕ // n ∈ g.ids} => depSub g y x) :=
    ⟨fun x h => hg x.1 h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- A nonempty finite acyclic graph has a *leaf*: an object that depends on
nothing. -/
theorem exists_leaf {g : KnowledgeGraph} (hg : Acyclic g) {a : ℕ} (ha : a ∈ g.ids) :
    ∃ b ∈ g.ids, ∀ c : ℕ, ¬ DependsDirect g b c := by
  obtain ⟨m, -, hm⟩ :=
    (depSubFlip_wellFounded hg).has_min Set.univ ⟨⟨a, ha⟩, Set.mem_univ _⟩
  refine ⟨m.1, m.2, fun c hc => ?_⟩
  have hcid : c ∈ g.ids := (mem_ids_of_dependsDirect hc).2
  exact hm ⟨c, hcid⟩ (Set.mem_univ _) (depends_of_direct hc)

/-- A nonempty finite acyclic graph has a *root*: an object that nothing depends
on. -/
theorem exists_root {g : KnowledgeGraph} (hg : Acyclic g) {a : ℕ} (ha : a ∈ g.ids) :
    ∃ b ∈ g.ids, ∀ c : ℕ, ¬ DependsDirect g c b := by
  obtain ⟨m, -, hm⟩ :=
    (depSub_wellFounded hg).has_min Set.univ ⟨⟨a, ha⟩, Set.mem_univ _⟩
  refine ⟨m.1, m.2, fun c hc => ?_⟩
  have hcid : c ∈ g.ids := (mem_ids_of_dependsDirect hc).1
  exact hm ⟨c, hcid⟩ (Set.mem_univ _) (depends_of_direct hc)

/-- Erasing an object can only remove dependencies. -/
theorem dependsDirect_eraseObj {g : KnowledgeGraph} {o : KnowledgeObject} {a b : ℕ}
    (h : DependsDirect (g.eraseObj o) a b) : DependsDirect g a b := by
  obtain ⟨r, hr, hk, hs, ht⟩ := h
  exact ⟨r, g.eraseObj_relations_subset o hr, hk, hs, ht⟩

theorem depends_eraseObj {g : KnowledgeGraph} {o : KnowledgeObject} {a b : ℕ}
    (h : Depends (g.eraseObj o) a b) : Depends g a b := by
  induction h with
  | single hab => exact depends_of_direct (dependsDirect_eraseObj hab)
  | tail _ hbc ih => exact depends_trans ih (depends_of_direct (dependsDirect_eraseObj hbc))

/-- Acyclicity is inherited by erasure. -/
theorem acyclic_eraseObj {g : KnowledgeGraph} (hg : Acyclic g) (o : KnowledgeObject) :
    Acyclic (g.eraseObj o) := fun a h => hg a (depends_eraseObj h)

end Polymath.Dependency
