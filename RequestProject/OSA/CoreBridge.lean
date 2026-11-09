import RequestProject.OSA.Theorems
import RequestProject.Certificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: plans as knowledge graphs

A plan of `n` steps becomes a knowledge graph with one `step` object per index
and a `dependsOn` edge from every step to its predecessor.

* `planGraph` — the construction, with referential integrity discharged;
* `planGraph_ids` — the identifiers are exactly `0, …, n-1`;
* `planGraph_acyclic` — the plan graph is acyclic, certified by the index
  layering;
* `planGraph_certified` — every step object is `validated`;
* `satisfies_gives_certified_acyclic_graph` — a conforming plan yields an
  acyclic, validated knowledge graph whose size is the length of the plan.
-/

namespace Polymath.OSA.CoreBridge

open Polymath Polymath.Dependency Polymath.Verification Polymath.OSA Polymath.OSA4

/-- The knowledge object recording step `i` of a plan. -/
def stepObject (chain : List Op) (i : ℕ) : KnowledgeObject :=
  { id := i
    kind := .step
    label := (chain[i]?).elim "" Op.name
    maturity := .validated
    confidence := 0 }

@[simp] theorem stepObject_id (chain : List Op) (i : ℕ) : (stepObject chain i).id = i := rfl

/-- The dependency edge from step `i` to step `i - 1`. -/
def stepEdge (i : ℕ) : KnowledgeRelation :=
  { source := i, target := i - 1, kind := .dependsOn, confidence := 0 }

/-- The knowledge graph of a plan. -/
def planGraph (chain : List Op) : KnowledgeGraph where
  objects := (Finset.range chain.length).image (stepObject chain)
  relations := (Finset.Ico 1 chain.length).image stepEdge
  unique_id := by
    intro a ha b hb hab
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
    simp only [stepObject_id] at hab
    subst hab
    rfl
  src_closed := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨hi1, hin⟩ := Finset.mem_Ico.1 hi
    exact ⟨stepObject chain i, Finset.mem_image_of_mem _ (Finset.mem_range.2 hin), rfl⟩
  tgt_closed := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨hi1, hin⟩ := Finset.mem_Ico.1 hi
    refine ⟨stepObject chain (i - 1),
      Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)), rfl⟩

theorem planGraph_ids (chain : List Op) :
    (planGraph chain).ids = Finset.range chain.length := by
  ext a
  simp only [KnowledgeGraph.mem_ids_iff, planGraph, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨o, ⟨i, hi, rfl⟩, rfl⟩
    simpa using hi
  · intro ha
    exact ⟨stepObject chain a, ⟨a, ha, rfl⟩, rfl⟩

/-- Every direct dependency of a plan graph goes from a step to its predecessor. -/
theorem dependsDirect_planGraph_iff (chain : List Op) (a b : ℕ) :
    DependsDirect (planGraph chain) a b ↔ 1 ≤ a ∧ a < chain.length ∧ b = a - 1 := by
  constructor
  · rintro ⟨r, hr, -, hs, ht⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨hi1, hin⟩ := Finset.mem_Ico.1 hi
    simp only [stepEdge] at hs ht
    subst hs
    exact ⟨hi1, hin, ht.symm⟩
  · rintro ⟨ha1, han, rfl⟩
    exact ⟨stepEdge a, Finset.mem_image_of_mem _ (Finset.mem_Ico.2 ⟨ha1, han⟩), rfl, rfl, rfl⟩

/-- Indexing the steps is a layering of the plan graph. -/
def indexLayering (chain : List Op) : Layering (planGraph chain) where
  level := fun a => a
  decreasing := by
    intro a b h
    obtain ⟨ha1, -, rfl⟩ := (dependsDirect_planGraph_iff chain a b).1 h
    omega

/-- A plan graph is acyclic. -/
theorem planGraph_acyclic (chain : List Op) : Acyclic (planGraph chain) :=
  acyclic_of_layering (indexLayering chain)

/-- Every step object of a plan graph is validated. -/
theorem planGraph_certified (chain : List Op) :
    Certified (planGraph chain) Maturity.validated := by
  intro a ha
  rw [planGraph_ids] at ha
  refine ⟨stepObject chain a, ⟨?_, rfl⟩, le_rfl⟩
  exact Finset.mem_image_of_mem _ ha

/-- The plan graph has one object per step. -/
theorem planGraph_card (chain : List Op) :
    (planGraph chain).objects.card = chain.length := by
  classical
  rw [planGraph]
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ hij
  simpa using congrArg KnowledgeObject.id hij

/-- Every plan graph carries a certificate. -/
theorem planGraph_certificate (chain : List Op) :
    Nonempty (Certificates.Certificate (planGraph chain)) :=
  ⟨{ layering := indexLayering chain
     level := Maturity.validated
     certified := planGraph_certified chain }⟩

/-- A conforming plan yields an acyclic, validated knowledge graph of the size
of the plan, recording only declared operators and reaching the goal. -/
theorem satisfies_gives_certified_acyclic_graph {sp : Spec} {init : KState} {chain : List Op}
    (h : sp.Satisfies init chain) :
    Acyclic (planGraph chain) ∧
      Certified (planGraph chain) Maturity.validated ∧
      (planGraph chain).objects.card = chain.length ∧
      ChainRegistered sp.registry chain ∧
      eval (execChain chain init) sp.goal = PT.TRUE_KNOWN :=
  ⟨planGraph_acyclic chain, planGraph_certified chain, planGraph_card chain,
    Spec.registered_of_satisfies h, h.2.1⟩

end Polymath.OSA.CoreBridge
