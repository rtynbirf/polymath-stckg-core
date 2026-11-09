import RequestProject.Gestalt.UCC
import RequestProject.AdaptiveAgent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: active-inference agents and cognitive systems

An active-inference agent enacting its own plan is a cognitive system whose
environment and step map are both "act on the plan"; conversely a cognitive
system, once equipped with a variational family, is an agent whose action space
is the state space and whose plan is the identity.  The two constructions are
inverse on the data that both structures carry (`roundTrip_step`,
`roundTrip_predict`, `roundTrip_env`, `agent_roundTrip_trajectory`).

The predicted environment `C.env` is *not* recovered by the round trip — the
agent construction forgets it and replaces it by the step map — so
`roundTrip_perfect_iff` carries the hypothesis `C.env = C.step`.

Finally the UCC theorems T3 and T5 are transported to reflexive adaptive
agents.
-/

namespace PolymathAtlas.Bridges

open PolymathAtlas.Gestalt.UCC
open PolymathAtlas.AdaptiveAgent

universe u v w

variable {S : Type u} {A : Type v} {Latent : Type w} [Fintype Latent]

/-! ## Agent → cognitive system -/

/-- The cognitive system of an agent enacting its own plan, with a supplied
predictor. -/
def uccOfAgent [DecidableEq S] (M : ActivePolicyAgent S A Latent) (predict : S → S) :
    CognitiveSystem S where
  env s := M.forward s (M.plan s)
  predict := predict
  step s := M.forward s (M.plan s)
  learningRate s := if predict s = M.forward s (M.plan s) then 0 else 1
  learningRate_nonneg s := by split_ifs <;> norm_num
  learningRate_eq_zero_iff s := by
    by_cases h : predict s = M.forward s (M.plan s)
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨fun hc => absurd hc (by norm_num), fun hc => absurd hc h⟩

@[simp] theorem uccOfAgent_step [DecidableEq S] (M : ActivePolicyAgent S A Latent)
    (predict : S → S) (s : S) :
    (uccOfAgent M predict).step s = M.forward s (M.plan s) := rfl

@[simp] theorem uccOfAgent_env [DecidableEq S] (M : ActivePolicyAgent S A Latent)
    (predict : S → S) (s : S) :
    (uccOfAgent M predict).env s = M.forward s (M.plan s) := rfl

@[simp] theorem uccOfAgent_predict [DecidableEq S] (M : ActivePolicyAgent S A Latent)
    (predict : S → S) :
    (uccOfAgent M predict).predict = predict := rfl

/-- The cognitive trajectory of the derived system is the agent's trajectory. -/
theorem uccOfAgent_trajectory [DecidableEq S] (M : ActivePolicyAgent S A Latent)
    (predict : S → S) (x : S) (n : ℕ) :
    (uccOfAgent M predict).trajectory x n = M.trajectory x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CognitiveSystem.trajectory_succ, ActivePolicyAgent.trajectory_succ, ih]
    rfl

/-! ## Cognitive system → agent -/

/-- The agent of a cognitive system: actions are states, the plan is the
identity, and every outcome is equally (un)preferred. -/
def agentOfCognitiveSystem (F : VariationalFamily Latent S) (C : CognitiveSystem S) :
    ActivePolicyAgent S S Latent where
  family := F
  forward _ a := C.step a
  preference _ := 0
  preference_nonpos _ := le_refl 0
  plan s := s

@[simp] theorem agentOfCognitiveSystem_forward (F : VariationalFamily Latent S)
    (C : CognitiveSystem S) (s a : S) :
    (agentOfCognitiveSystem F C).forward s a = C.step a := rfl

@[simp] theorem agentOfCognitiveSystem_plan (F : VariationalFamily Latent S)
    (C : CognitiveSystem S) (s : S) : (agentOfCognitiveSystem F C).plan s = s := rfl

/-! ## Round trip -/

variable (F : VariationalFamily Latent S) (C : CognitiveSystem S)

theorem roundTrip_step [DecidableEq S] :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).step = C.step := rfl

theorem roundTrip_env [DecidableEq S] :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).env = C.step := rfl

theorem roundTrip_predict [DecidableEq S] :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).predict = C.predict := rfl

/-- Perfection is preserved by the round trip for systems whose prediction
target is their own step map. -/
theorem roundTrip_perfect_iff [DecidableEq S] (hC : C.env = C.step) :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).Perfect ↔ C.Perfect := by
  constructor
  · intro h s
    rw [hC]
    exact h s
  · intro h s
    have := h s
    rw [hC] at this
    exact this

/-- Trajectories are preserved by the round trip. -/
theorem agent_roundTrip_trajectory (x : S) (n : ℕ) :
    (agentOfCognitiveSystem F C).trajectory x n = C.trajectory x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ActivePolicyAgent.trajectory_succ, CognitiveSystem.trajectory_succ, ih]
    rfl

/-- All the round-trip identities at once. -/
theorem bridge2_two_sided [DecidableEq S] (hC : C.env = C.step) :
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).step = C.step ∧
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).env = C.step ∧
    (uccOfAgent (agentOfCognitiveSystem F C) C.predict).predict = C.predict ∧
    ((uccOfAgent (agentOfCognitiveSystem F C) C.predict).Perfect ↔ C.Perfect) ∧
    ∀ x n, (agentOfCognitiveSystem F C).trajectory x n = C.trajectory x n :=
  ⟨roundTrip_step F C, roundTrip_env F C, roundTrip_predict F C,
    roundTrip_perfect_iff F C hC, agent_roundTrip_trajectory F C⟩

/-! ## Transfer of T3 and T5 to reflexive agents -/

/-- The channel by which an agent recognises its own latent. -/
def selfChannel (R : ReflexiveAdaptiveAgent S A Latent) : Channel Latent Prop :=
  fun z => z = R.selfLatent

/-- **T3 transfer.** A reflexive adaptive agent draws a distinction: it tells
its own latent apart from another one. -/
theorem uccOfReflexive_drawsDistinction (R : ReflexiveAdaptiveAgent S A Latent) :
    DrawsDistinction (selfChannel R) := by
  refine ⟨R.selfLatent, R.otherLatent, ?_⟩
  intro hEq
  exact R.self_ne (cast hEq rfl).symm

/-- **T5 transfer.** On a finite state space the trajectory of a reflexive
adaptive agent revisits a state within `card S` steps. -/
theorem uccOfReflexive_revisits [Fintype S] [DecidableEq S]
    (R : ReflexiveAdaptiveAgent S A Latent) (predict : S → S) (x : S) :
    ∃ i j, i < j ∧ j ≤ t5Bound S ∧ R.agent.trajectory x i = R.agent.trajectory x j := by
  obtain ⟨i, j, hij, hj, h⟩ := t5_trajectory_revisits (uccOfAgent R.agent predict) x
  exact ⟨i, j, hij, hj, by
    rw [← uccOfAgent_trajectory R.agent predict, ← uccOfAgent_trajectory R.agent predict]
    exact h⟩

/-- A reflexive adaptive agent has non-negative expected free energy and an
optimal plan, viewed through the bridge. -/
theorem uccOfReflexive_efe_optimal (R : ReflexiveAdaptiveAgent S A Latent) (a : A) :
    0 ≤ R.agent.efe R.state (R.agent.plan R.state) ∧
      R.agent.efe R.state (R.agent.plan R.state) ≤ R.agent.efe R.state a :=
  ⟨R.agent.efe_nonneg _ _, R.spec.minimizes a⟩

end PolymathAtlas.Bridges
