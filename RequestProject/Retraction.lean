import RequestProject.Evolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Retraction: withdrawing a refuted object

Retracting an object removes it together with every relation incident to it.
The point of the operation is that nothing can still depend on what has been
withdrawn:

* `no_dependsDirect_retracted` — after a retraction no object depends on the
  retracted identifier;
* `retract_extends`, `retract_acyclic`, `retract_normalized`,
  `retract_certified` — retraction is a step down the growth preorder and
  preserves acyclicity, normalization and certification;
* `retractList` and `retractList_extends` — iterated retraction, with the same
  guarantees.
-/

namespace Polymath.Retraction

open Polymath Polymath.Dependency Polymath.Verification Polymath.Evolution

/-- Withdraw an object and every relation incident to it. -/
def retract (g : KnowledgeGraph) (o : KnowledgeObject) : KnowledgeGraph := g.eraseObj o

@[simp] theorem retract_objects (g : KnowledgeGraph) (o : KnowledgeObject) :
    (retract g o).objects = g.objects.erase o := rfl

theorem mem_retract_relations {g : KnowledgeGraph} {o : KnowledgeObject}
    {r : KnowledgeRelation} (hr : r ∈ (retract g o).relations) :
    r ∈ g.relations ∧ r.source ≠ o.id ∧ r.target ≠ o.id := by
  have := Finset.mem_filter.1 hr
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- The retracted object is gone. -/
theorem notMem_retract (g : KnowledgeGraph) (o : KnowledgeObject) :
    o ∉ (retract g o).objects := g.eraseObj_not_mem o

/-- Nothing depends on a retracted identifier any more. -/
theorem no_dependsDirect_retracted (g : KnowledgeGraph) (o : KnowledgeObject) (a : ℕ) :
    ¬ DependsDirect (retract g o) a o.id := by
  rintro ⟨r, hr, -, -, ht⟩
  exact (mem_retract_relations hr).2.2 ht

/-- Nothing reaches a retracted identifier through a chain either. -/
theorem no_depends_retracted (g : KnowledgeGraph) (o : KnowledgeObject) (a : ℕ) :
    ¬ Depends (retract g o) a o.id := by
  intro h
  cases h with
  | single hab => exact no_dependsDirect_retracted g o a hab
  | tail _ hbc => exact no_dependsDirect_retracted g o _ hbc

theorem retract_extends (g : KnowledgeGraph) (o : KnowledgeObject) :
    Extends (retract g o) g := extends_eraseObj g o

theorem retract_acyclic {g : KnowledgeGraph} (hg : Acyclic g) (o : KnowledgeObject) :
    Acyclic (retract g o) := acyclic_eraseObj hg o

theorem retract_normalized {g : KnowledgeGraph} (hg : g.Normalized) (o : KnowledgeObject) :
    (retract g o).Normalized := KnowledgeGraph.eraseObj_normalized hg o

theorem retract_certified {g : KnowledgeGraph} {m : Maturity} (hc : Certified g m)
    (o : KnowledgeObject) : Certified (retract g o) m := hc.eraseObj o

/-- Retraction never increases the number of objects. -/
theorem retract_card_le (g : KnowledgeGraph) (o : KnowledgeObject) :
    (retract g o).objects.card ≤ g.objects.card :=
  Finset.card_le_card (g.eraseObj_objects_subset o)

/-- Retracting an object that is present strictly shrinks the graph. -/
theorem retract_card_lt {g : KnowledgeGraph} {o : KnowledgeObject} (ho : o ∈ g.objects) :
    (retract g o).objects.card < g.objects.card :=
  Finset.card_erase_lt_of_mem ho

/-! ## Iterated retraction -/

/-- Retract a whole list of objects, in order. -/
def retractList (g : KnowledgeGraph) : List KnowledgeObject → KnowledgeGraph
  | [] => g
  | o :: t => retractList (retract g o) t

@[simp] theorem retractList_nil (g : KnowledgeGraph) : retractList g [] = g := rfl

@[simp] theorem retractList_cons (g : KnowledgeGraph) (o : KnowledgeObject)
    (t : List KnowledgeObject) : retractList g (o :: t) = retractList (retract g o) t := rfl

theorem retractList_extends (g : KnowledgeGraph) (l : List KnowledgeObject) :
    Extends (retractList g l) g := by
  induction l generalizing g with
  | nil => exact Extends.refl g
  | cons o t ih => exact (ih (retract g o)).trans (retract_extends g o)

theorem retractList_acyclic {g : KnowledgeGraph} (hg : Acyclic g)
    (l : List KnowledgeObject) : Acyclic (retractList g l) := by
  induction l generalizing g with
  | nil => exact hg
  | cons o t ih => exact ih (retract_acyclic hg o)

theorem retractList_certified {g : KnowledgeGraph} {m : Maturity} (hc : Certified g m)
    (l : List KnowledgeObject) : Certified (retractList g l) m := by
  induction l generalizing g with
  | nil => exact hc
  | cons o t ih => exact ih (retract_certified hc o)

/-- Every retracted object is really gone from the final graph. -/
theorem notMem_retractList {g : KnowledgeGraph} {o : KnowledgeObject}
    {l : List KnowledgeObject} (ho : o ∈ l) : o ∉ (retractList g l).objects := by
  induction l generalizing g with
  | nil => cases ho
  | cons p t ih =>
      rcases List.mem_cons.1 ho with rfl | ho'
      · intro hmem
        exact notMem_retract g o ((retractList_extends (retract g o) t).1 hmem)
      · exact ih ho'

end Polymath.Retraction
