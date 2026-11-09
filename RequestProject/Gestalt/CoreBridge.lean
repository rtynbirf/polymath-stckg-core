import RequestProject.Gestalt.GenesisEngine
import RequestProject.Gestalt.UCC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: knowledge-graph agents as cognitive systems

An agent acting on knowledge graphs is a cognitive system whose environment is
the agent's own action and whose predictor is "nothing will change".  The
learning rate is then zero exactly at a fixed point, so the UCC theorems T3 and
T4 apply verbatim to agents.

* `agentSystem` and `agentErrorDriven` — the two constructions;
* `agentSystem_trajectory` — the cognitive trajectory is the agent run;
* `perfect_iff_forall_fixed` — perfection is universal fixedness;
* `learningRate_pos_iff_not_fixed`, `genesis_learningRate_pos` — the genesis
  engine always has something to learn.
-/

namespace PolymathAtlas.Gestalt.CoreBridge

open Polymath Polymath.Agents PolymathAtlas.Gestalt.UCC

/-- An agent, read as an error-driven cognitive system on knowledge graphs. -/
noncomputable def agentErrorDriven (A : Agent) : ErrorDriven KnowledgeGraph where
  env := A.act
  predict := _root_.id
  step := A.act
  learningRate := fun g => open Classical in if A.act g = g then 0 else 1
  learningRate_nonneg := by
    intro g
    classical
    by_cases h : A.act g = g <;> simp [h]
  learningRate_eq_zero_iff := by
    intro g
    classical
    show (if A.act g = g then (0 : ℝ) else 1) = 0 ↔ g = A.act g
    by_cases h : A.act g = g
    · simp [h]
    · have hne : ¬ (g = A.act g) := fun hc => h hc.symm
      simp [h, hne]
  step_eq_self_of_no_learning := by
    intro g hg
    classical
    by_cases h : A.act g = g
    · exact h
    · rw [if_neg h] at hg; norm_num at hg

/-- The underlying cognitive system of an agent. -/
noncomputable def agentSystem (A : Agent) : CognitiveSystem KnowledgeGraph :=
  (agentErrorDriven A).toCognitiveSystem

@[simp] theorem agentSystem_step (A : Agent) : (agentSystem A).step = A.act := rfl

@[simp] theorem agentSystem_env (A : Agent) : (agentSystem A).env = A.act := rfl

/-- The cognitive trajectory of an agent is its run. -/
theorem agentSystem_trajectory (A : Agent) (g : KnowledgeGraph) (n : ℕ) :
    (agentSystem A).trajectory g n = A.run g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [CognitiveSystem.trajectory_succ, ih, agentSystem_step, Agent.run_succ]

/-- Perfect prediction means the agent is fixed everywhere. -/
theorem perfect_iff_forall_fixed (A : Agent) :
    (agentSystem A).Perfect ↔ ∀ g, A.Fixed g := by
  constructor
  · intro h g; exact (h g).symm
  · intro h g; exact (h g).symm

/-- The learning rate is positive exactly where the agent still moves. -/
theorem learningRate_pos_iff_not_fixed (A : Agent) (g : KnowledgeGraph) :
    0 < (agentSystem A).learningRate g ↔ ¬ A.Fixed g := by
  classical
  by_cases h : A.act g = g
  · simp [agentSystem, agentErrorDriven, Agent.Fixed, h]
  · simp [agentSystem, agentErrorDriven, Agent.Fixed, h]

/-- The genesis engine never predicts its environment: it always has something
to learn. -/
theorem genesis_learningRate_pos (k : ObjectKind) (label : String) (g : KnowledgeGraph) :
    0 < (agentSystem (Genesis.genesisAgent k label)).learningRate g :=
  (learningRate_pos_iff_not_fixed _ g).2 (Genesis.genesisAgent_not_fixed k label g)

/-- The genesis engine is never a perfect predictor of itself. -/
theorem genesis_not_perfect (k : ObjectKind) (label : String) :
    ¬ (agentSystem (Genesis.genesisAgent k label)).Perfect := by
  intro h
  exact Genesis.genesisAgent_not_fixed k label
    { objects := ∅, relations := ∅,
      unique_id := by intro a ha; simp at ha,
      src_closed := by intro r hr; simp at hr,
      tgt_closed := by intro r hr; simp at hr }
    ((perfect_iff_forall_fixed _).1 h _)

/-- **T4 for agents.** An agent that is fixed everywhere is inert, and its runs
are constant. -/
theorem run_const_of_perfect {A : Agent} (h : ∀ g, A.Fixed g) (g : KnowledgeGraph) (n : ℕ) :
    A.run g n = g := by
  have := (agentErrorDriven A).t4_perfect_trajectory_const
    ((perfect_iff_forall_fixed A).2 h) g n
  rwa [show (agentErrorDriven A).toCognitiveSystem = agentSystem A from rfl,
    agentSystem_trajectory] at this

end PolymathAtlas.Gestalt.CoreBridge
