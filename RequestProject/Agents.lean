import RequestProject.Evolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Agents: monotone transformations of a knowledge graph

An `Agent` is a transformation of knowledge graphs that only ever adds: its
output extends its input.  Agents compose, contain an identity, and their
iterates form an increasing chain.

* `Agent.comp`, `Agent.id`, `comp_assoc`, `id_comp`, `comp_id` — the monoid
  structure of agents;
* `Agent.run` — iterated action, with `extends_run` and `run_le_mono`;
* `Agent.Fixed` and `run_eq_of_fixed` — an agent at a fixed point does nothing
  for ever after.
-/

namespace Polymath.Agents

open Polymath Polymath.Evolution

/-- An agent transforms a knowledge graph, only ever extending it. -/
structure Agent where
  /-- The action of the agent. -/
  act : KnowledgeGraph → KnowledgeGraph
  /-- Agents never delete: the output extends the input. -/
  monotone : ∀ g, Extends g (act g)

/-- The agent that does nothing. -/
def Agent.id : Agent where
  act := _root_.id
  monotone := fun g => Extends.refl g

/-- Run `A` after `B`. -/
def Agent.comp (A B : Agent) : Agent where
  act := fun g => A.act (B.act g)
  monotone := fun g => (B.monotone g).trans (A.monotone (B.act g))

theorem Agent.comp_act (A B : Agent) (g : KnowledgeGraph) :
    (A.comp B).act g = A.act (B.act g) := rfl

theorem Agent.comp_assoc (A B C : Agent) (g : KnowledgeGraph) :
    ((A.comp B).comp C).act g = (A.comp (B.comp C)).act g := rfl

theorem Agent.id_comp (A : Agent) (g : KnowledgeGraph) : (Agent.id.comp A).act g = A.act g := rfl

theorem Agent.comp_id (A : Agent) (g : KnowledgeGraph) : (A.comp Agent.id).act g = A.act g := rfl

/-! ## Iteration -/

/-- Run the agent `n` times. -/
def Agent.run (A : Agent) (g : KnowledgeGraph) : ℕ → KnowledgeGraph
  | 0 => g
  | n + 1 => A.act (A.run g n)

@[simp] theorem Agent.run_zero (A : Agent) (g : KnowledgeGraph) : A.run g 0 = g := rfl

@[simp] theorem Agent.run_succ (A : Agent) (g : KnowledgeGraph) (n : ℕ) :
    A.run g (n + 1) = A.act (A.run g n) := rfl

/-- Every stage of a run extends the initial graph. -/
theorem Agent.extends_run (A : Agent) (g : KnowledgeGraph) (n : ℕ) :
    Extends g (A.run g n) := by
  induction n with
  | zero => exact Extends.refl g
  | succ n ih => exact ih.trans (A.monotone (A.run g n))

/-- Runs increase along the growth preorder. -/
theorem Agent.run_le_mono (A : Agent) (g : KnowledgeGraph) {m n : ℕ} (h : m ≤ n) :
    Extends (A.run g m) (A.run g n) := by
  induction n with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.1 h
      exact Extends.refl _
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (A.monotone (A.run g n))
      · obtain rfl : m = n + 1 := le_antisymm h hge
        exact Extends.refl _

/-- Objects are never lost during a run. -/
theorem Agent.objects_subset_run (A : Agent) (g : KnowledgeGraph) (n : ℕ) :
    g.objects ⊆ (A.run g n).objects := (A.extends_run g n).1

/-- Identifiers are never lost during a run. -/
theorem Agent.ids_subset_run (A : Agent) (g : KnowledgeGraph) (n : ℕ) :
    g.ids ⊆ (A.run g n).ids := (A.extends_run g n).ids_subset

/-! ## Fixed points -/

/-- The agent has nothing left to do on `g`. -/
def Agent.Fixed (A : Agent) (g : KnowledgeGraph) : Prop := A.act g = g

/-- At a fixed point the run is constant. -/
theorem Agent.run_eq_of_fixed {A : Agent} {g : KnowledgeGraph} (h : A.Fixed g) (n : ℕ) :
    A.run g n = g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Agent.run_succ, ih, h]

/-- The identity agent is fixed everywhere. -/
theorem Agent.id_fixed (g : KnowledgeGraph) : Agent.id.Fixed g := rfl

/-- A fixed point of `A` is also a fixed point of any number of repetitions. -/
theorem Agent.fixed_comp {A B : Agent} {g : KnowledgeGraph} (hA : A.Fixed g) (hB : B.Fixed g) :
    (A.comp B).Fixed g := by
  show A.act (B.act g) = g
  rw [hB, hA]

end Polymath.Agents
