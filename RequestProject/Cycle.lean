import RequestProject.MetaLearning

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Cycles of an agent run

Because an agent only adds, a run can never cycle non-trivially: if a run
revisits an earlier graph, then it never moved at all in between, and the agent
has reached a fixed point.

* `eq_of_between` — every graph strictly inside a revisited window equals the
  endpoints;
* `fixed_of_revisit` — a revisit forces a fixed point;
* `cycle_length_one` — every cycle of an agent run has length one;
* `exists_fixed_of_bounded` — inside a finite universe a run always reaches a
  fixed point.
-/

namespace Polymath.Cycle

open Polymath Polymath.Evolution Polymath.Agents Polymath.Collective Polymath.MetaLearning

variable {A : Agent} {g : KnowledgeGraph}

/-- If the run returns to an earlier graph, nothing changed in between. -/
theorem eq_of_between {i j m : ℕ} (hij : A.run g i = A.run g j) (him : i ≤ m) (hmj : m ≤ j) :
    A.run g m = A.run g i := by
  have h₁ : Extends (A.run g i) (A.run g m) := A.run_le_mono g him
  have h₂ : Extends (A.run g m) (A.run g j) := A.run_le_mono g hmj
  rw [← hij] at h₂
  exact graph_ext (Finset.Subset.antisymm h₂.1 h₁.1) (Finset.Subset.antisymm h₂.2 h₁.2)

/-- A revisit forces the agent to be at a fixed point. -/
theorem fixed_of_revisit {i j : ℕ} (hlt : i < j) (hij : A.run g i = A.run g j) :
    A.Fixed (A.run g i) := by
  have h := eq_of_between hij (Nat.le_succ i) hlt
  simpa [Agent.Fixed] using h

/-- Every cycle of an agent run has length one: revisiting means standing still. -/
theorem cycle_length_one {i j : ℕ} (hlt : i < j) (hij : A.run g i = A.run g j) (m : ℕ)
    (him : i ≤ m) : A.run g m = A.run g i := by
  induction m with
  | zero =>
      obtain rfl : i = 0 := Nat.le_zero.1 him
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · have hi : A.run g m = A.run g i := ih (Nat.lt_succ_iff.1 h)
        have := fixed_of_revisit hlt hij
        rw [Agent.run_succ, hi]
        exact this
      · obtain rfl : i = m + 1 := le_antisymm him h
        rfl

/-- Inside a finite universe, an agent run always reaches a fixed point. -/
theorem exists_fixed_of_bounded (A : Agent) (g : KnowledgeGraph)
    (U : Finset KnowledgeObject) (R : Finset KnowledgeRelation)
    (hU : ∀ n, (A.run g n).objects ⊆ U) (hR : ∀ n, (A.run g n).relations ⊆ R) :
    ∃ N, A.Fixed (A.run g N) := by
  obtain ⟨N, hN⟩ := exists_stabilization A g U R hU hR
  exact ⟨N, fixed_of_stabilization hN⟩

/-- Once the run is fixed, it is constant for ever after. -/
theorem run_const_of_fixed {N : ℕ} (h : A.Fixed (A.run g N)) {m : ℕ} (hm : N ≤ m) :
    A.run g m = A.run g N := by
  induction m with
  | zero =>
      obtain rfl : N = 0 := Nat.le_zero.1 hm
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge N (m + 1) with hlt | hge
      · rw [Agent.run_succ, ih (Nat.lt_succ_iff.1 hlt)]
        exact h
      · obtain rfl : N = m + 1 := le_antisymm hm hge
        rfl

end Polymath.Cycle
