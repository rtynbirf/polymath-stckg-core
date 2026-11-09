import RequestProject.Collective

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Meta-learning: runs inside a bounded universe saturate

An agent only ever adds objects and relations, so a run is an increasing chain.
If the whole run stays inside a fixed finite universe, the chain must stop
growing:

* `exists_objects_stabilization` — the object sets of a bounded run are
  eventually constant;
* `exists_relations_stabilization` — likewise for relations;
* `exists_stabilization` — both at once, so the graph itself is eventually
  constant along the run.
-/

namespace Polymath.MetaLearning

open Polymath Polymath.Evolution Polymath.Agents Polymath.Collective

/-- A monotone `ℕ`-valued sequence bounded above is eventually constant. -/
theorem exists_const_of_monotone_bounded {f : ℕ → ℕ} (hmono : Monotone f) {B : ℕ}
    (hB : ∀ n, f n ≤ B) : ∃ N, ∀ m, N ≤ m → f m = f N := by
  have hne : (Set.range f).Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hbdd : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  obtain ⟨N, hN⟩ : sSup (Set.range f) ∈ Set.range f := Nat.sSup_mem hne hbdd
  refine ⟨N, fun m hm => ?_⟩
  have h₁ : f N ≤ f m := hmono hm
  have h₂ : f m ≤ sSup (Set.range f) := le_csSup hbdd ⟨m, rfl⟩
  rw [← hN] at h₂
  omega

/-- The object sets of a run inside a finite universe are eventually constant. -/
theorem exists_objects_stabilization (A : Agent) (g : KnowledgeGraph)
    (U : Finset KnowledgeObject) (hU : ∀ n, (A.run g n).objects ⊆ U) :
    ∃ N, ∀ m, N ≤ m → (A.run g m).objects = (A.run g N).objects := by
  have hmono : Monotone (fun n => (A.run g n).objects.card) := by
    intro m n hmn
    exact Finset.card_le_card (A.run_le_mono g hmn).1
  obtain ⟨N, hN⟩ := exists_const_of_monotone_bounded hmono
    (B := U.card) (fun n => Finset.card_le_card (hU n))
  refine ⟨N, fun m hm => ?_⟩
  have hsub : (A.run g N).objects ⊆ (A.run g m).objects := (A.run_le_mono g hm).1
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hN m hm))).symm

/-- The relation sets of a run inside a finite universe are eventually constant. -/
theorem exists_relations_stabilization (A : Agent) (g : KnowledgeGraph)
    (R : Finset KnowledgeRelation) (hR : ∀ n, (A.run g n).relations ⊆ R) :
    ∃ N, ∀ m, N ≤ m → (A.run g m).relations = (A.run g N).relations := by
  have hmono : Monotone (fun n => (A.run g n).relations.card) := by
    intro m n hmn
    exact Finset.card_le_card (A.run_le_mono g hmn).2
  obtain ⟨N, hN⟩ := exists_const_of_monotone_bounded hmono
    (B := R.card) (fun n => Finset.card_le_card (hR n))
  refine ⟨N, fun m hm => ?_⟩
  have hsub : (A.run g N).relations ⊆ (A.run g m).relations := (A.run_le_mono g hm).2
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hN m hm))).symm

/-- A run inside a finite universe eventually stops changing the graph. -/
theorem exists_stabilization (A : Agent) (g : KnowledgeGraph)
    (U : Finset KnowledgeObject) (R : Finset KnowledgeRelation)
    (hU : ∀ n, (A.run g n).objects ⊆ U) (hR : ∀ n, (A.run g n).relations ⊆ R) :
    ∃ N, ∀ m, N ≤ m → A.run g m = A.run g N := by
  obtain ⟨N₁, h₁⟩ := exists_objects_stabilization A g U hU
  obtain ⟨N₂, h₂⟩ := exists_relations_stabilization A g R hR
  refine ⟨max N₁ N₂, fun m hm => ?_⟩
  have hm₁ : N₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm₂ : N₂ ≤ m := le_trans (le_max_right _ _) hm
  have hM₁ : N₁ ≤ max N₁ N₂ := le_max_left _ _
  have hM₂ : N₂ ≤ max N₁ N₂ := le_max_right _ _
  refine graph_ext ?_ ?_
  · rw [h₁ m hm₁, h₁ (max N₁ N₂) hM₁]
  · rw [h₂ m hm₂, h₂ (max N₁ N₂) hM₂]

/-- Once a run has stabilised, the agent is at a fixed point. -/
theorem fixed_of_stabilization {A : Agent} {g : KnowledgeGraph} {N : ℕ}
    (h : ∀ m, N ≤ m → A.run g m = A.run g N) : A.Fixed (A.run g N) := by
  have := h (N + 1) (Nat.le_succ N)
  simpa [Agent.Fixed] using this

end Polymath.MetaLearning
