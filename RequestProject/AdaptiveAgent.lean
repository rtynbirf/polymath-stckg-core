import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Adaptive agents: variational free energy and reflexive self-models

This module builds the active-inference side of the project.

* `ObservationStream`s carry a liveness predicate (infinitely often active), and
  the stream transformers preserving liveness form a monoid.
* `klDiv` is the Kullback–Leibler divergence on a finite alphabet.  We prove
  `klDiv_self` and Gibbs' inequality `klDiv_nonneg` from `log x ≤ x - 1`.
* An `ActivePolicyAgent` carries a variational family, a forward model and a
  preference (a non-positive log-preference).  Its **expected free energy**
  decomposes as risk plus ambiguity, and is non-negative (`efe_nonneg`).
* A `ReflexiveAdaptiveAgent` is an agent equipped with a self-model that is a
  fixed point of its own meta-update, and whose plan genuinely minimises
  expected free energy.
-/

namespace PolymathAtlas.AdaptiveAgent

/-! ## Observation streams -/

/-- A single observation on a channel. -/
structure Observation where
  channel : ℕ
  value : ℝ

/-- An infinite stream of observations. -/
abbrev ObservationStream := ℕ → Observation

/-- An observation is active when it carries a nonzero value. -/
def Active (o : Observation) : Prop := o.value ≠ 0

/-- A stream is live at `n` when some observation from `n` onwards is active. -/
def LiveAt (s : ObservationStream) (n : ℕ) : Prop := ∃ m, n ≤ m ∧ Active (s m)

/-- A stream is live when it is active infinitely often. -/
def Live (s : ObservationStream) : Prop := ∀ n, LiveAt s n

theorem live_iff_forall_exists (s : ObservationStream) :
    Live s ↔ ∀ n, ∃ m, n ≤ m ∧ (s m).value ≠ 0 := Iff.rfl

/-- A liveness-preserving transformation of observation streams. -/
structure StreamTransformer where
  toFun : ObservationStream → ObservationStream
  live_apply : ∀ s, Live s → Live (toFun s)

namespace StreamTransformer

instance : CoeFun StreamTransformer (fun _ => ObservationStream → ObservationStream) :=
  ⟨StreamTransformer.toFun⟩

@[ext] theorem ext {f g : StreamTransformer} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact h

/-- The identity transformer. -/
protected def id : StreamTransformer := ⟨_root_.id, fun _ h => h⟩

/-- Composition of transformers. -/
protected def comp (f g : StreamTransformer) : StreamTransformer :=
  ⟨f.toFun ∘ g.toFun, fun s h => f.live_apply _ (g.live_apply s h)⟩

theorem comp_assoc (f g h : StreamTransformer) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext1
  rfl

@[simp] theorem id_comp (f : StreamTransformer) : StreamTransformer.id.comp f = f := by
  ext1; rfl

@[simp] theorem comp_id (f : StreamTransformer) : f.comp StreamTransformer.id = f := by
  ext1; rfl

/-- Liveness-preserving stream transformers form a monoid under composition. -/
instance : Monoid StreamTransformer where
  mul := StreamTransformer.comp
  one := StreamTransformer.id
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id

end StreamTransformer

/-! ## Kullback–Leibler divergence -/

section KL

variable {α : Type*} [Fintype α]

/-- Kullback–Leibler divergence on a finite alphabet. -/
noncomputable def klDiv (p q : α → ℝ) : ℝ := ∑ a, p a * Real.log (p a / q a)

@[simp] theorem klDiv_self (p : α → ℝ) : klDiv p p = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases h : p a = 0
  · simp [h]
  · simp [div_self h]

/-- **Gibbs' inequality.** The divergence between two strictly positive
probability vectors is non-negative. -/
theorem klDiv_nonneg {p q : α → ℝ} (hp : ∀ a, 0 < p a) (hq : ∀ a, 0 < q a)
    (hps : ∑ a, p a = 1) (hqs : ∑ a, q a = 1) : 0 ≤ klDiv p q := by
  have key : ∀ a : α, p a * Real.log (q a / p a) ≤ q a - p a := by
    intro a
    have h1 : Real.log (q a / p a) ≤ q a / p a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hq a) (hp a))
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (hp a))
    have hpa : p a ≠ 0 := ne_of_gt (hp a)
    have h3 : p a * (q a / p a - 1) = q a - p a := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hsum : ∑ a, p a * Real.log (q a / p a) ≤ ∑ a : α, (q a - p a) :=
    Finset.sum_le_sum fun a _ => key a
  have hzero : ∑ a : α, (q a - p a) = 0 := by
    rw [Finset.sum_sub_distrib, hps, hqs, sub_self]
  have hflip : klDiv p q = - ∑ a, p a * Real.log (q a / p a) := by
    rw [klDiv, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_neg, ← Real.log_inv, inv_div]
  rw [hflip, neg_nonneg]
  linarith [hsum, hzero.le, hzero.ge]

end KL

/-! ## Variational families -/

/-- A variational family: a strictly positive prior over latents and, for each
observation, a strictly positive posterior. -/
structure VariationalFamily (Latent Obs : Type*) [Fintype Latent] where
  prior : Latent → ℝ
  posterior : Obs → Latent → ℝ
  prior_pos : ∀ z, 0 < prior z
  posterior_pos : ∀ o z, 0 < posterior o z
  prior_sum : ∑ z, prior z = 1
  posterior_sum : ∀ o, ∑ z, posterior o z = 1

namespace VariationalFamily

variable {Latent Obs : Type*} [Fintype Latent] (F : VariationalFamily Latent Obs)

/-- Complexity: how far the posterior for an observation moves from the prior. -/
noncomputable def complexity (o : Obs) : ℝ := klDiv (F.posterior o) F.prior

/-- Divergence between the posteriors of two observations. -/
noncomputable def posteriorDiv (o o' : Obs) : ℝ := klDiv (F.posterior o) (F.posterior o')

theorem complexity_nonneg (o : Obs) : 0 ≤ F.complexity o :=
  klDiv_nonneg (F.posterior_pos o) F.prior_pos (F.posterior_sum o) F.prior_sum

theorem posteriorDiv_nonneg (o o' : Obs) : 0 ≤ F.posteriorDiv o o' :=
  klDiv_nonneg (F.posterior_pos o) (F.posterior_pos o') (F.posterior_sum o) (F.posterior_sum o')

@[simp] theorem posteriorDiv_self (o : Obs) : F.posteriorDiv o o = 0 := klDiv_self _

end VariationalFamily

/-! ## Active-inference agents -/

/-- An agent that plans by minimising expected free energy. -/
structure ActivePolicyAgent (S A Latent : Type*) [Fintype Latent] where
  family : VariationalFamily Latent S
  forward : S → A → S
  preference : S → ℝ
  preference_nonpos : ∀ s, preference s ≤ 0
  plan : S → A

namespace ActivePolicyAgent

variable {S A Latent : Type*} [Fintype Latent] (M : ActivePolicyAgent S A Latent)

/-- Risk: how far the predicted outcome is from the agent's preferences. -/
def risk (s : S) (a : A) : ℝ := -M.preference (M.forward s a)

/-- Ambiguity: the complexity of the belief update the outcome would force. -/
noncomputable def ambiguity (s : S) (a : A) : ℝ := M.family.complexity (M.forward s a)

/-- Expected free energy: risk plus ambiguity. -/
noncomputable def efe (s : S) (a : A) : ℝ := M.risk s a + M.ambiguity s a

theorem risk_nonneg (s : S) (a : A) : 0 ≤ M.risk s a := by
  simpa [risk] using M.preference_nonpos (M.forward s a)

theorem ambiguity_nonneg (s : S) (a : A) : 0 ≤ M.ambiguity s a :=
  M.family.complexity_nonneg _

/-- Expected free energy is non-negative. -/
theorem efe_nonneg (s : S) (a : A) : 0 ≤ M.efe s a :=
  add_nonneg (M.risk_nonneg s a) (M.ambiguity_nonneg s a)

/-- The state trajectory obtained by repeatedly enacting the plan. -/
def trajectory (x : S) : ℕ → S := fun n => (fun s => M.forward s (M.plan s))^[n] x

@[simp] theorem trajectory_zero (x : S) : M.trajectory x 0 = x := rfl

theorem trajectory_succ (x : S) (n : ℕ) :
    M.trajectory x (n + 1) = M.forward (M.trajectory x n) (M.plan (M.trajectory x n)) := by
  simp [trajectory, Function.iterate_succ_apply']

theorem trajectory_eq_of_fixed {x : S} (h : M.forward x (M.plan x) = x) (n : ℕ) :
    M.trajectory x n = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory_succ, ih, h]

end ActivePolicyAgent

/-! ## Self-models and fixed points -/

/-- A self-map of a type. -/
abbrev SelfMap (α : Type*) := α → α

/-- An idempotent self-map on a nonempty type has a fixed point. -/
theorem exists_fixed_point_of_idempotent {α : Type*} [Nonempty α] (f : SelfMap α)
    (h : f ∘ f = f) : ∃ x, f x = x :=
  ⟨f (Classical.arbitrary α), congrFun h (Classical.arbitrary α)⟩

/-- A self-map that fixes a designated point has a fixed point. -/
theorem exists_fixed_point_selfMap {α : Type*} (f : SelfMap α) {a : α} (h : f a = a) :
    ∃ x, f x = x := ⟨a, h⟩

/-- An agent together with a self-model latent and a meta-update on agents. -/
structure MetaOptimizer (S A Latent : Type*) [Fintype Latent] where
  agent : ActivePolicyAgent S A Latent
  selfLatent : Latent
  metaUpdate : SelfMap (ActivePolicyAgent S A Latent)

/-- The specification an adaptive agent is required to meet: it acts on a live
stream, and its plan really does minimise expected free energy. -/
structure AdaptiveAgentSpec {S A Latent : Type*} [Fintype Latent]
    (M : ActivePolicyAgent S A Latent) (stream : ObservationStream) (state : S) : Prop where
  live : Live stream
  minimizes : ∀ a : A, M.efe state (M.plan state) ≤ M.efe state a

/-- A reflexive adaptive agent: its meta-update has converged, it meets its
specification, and it distinguishes itself from at least one other latent. -/
structure ReflexiveAdaptiveAgent (S A Latent : Type*) [Fintype Latent]
    extends MetaOptimizer S A Latent where
  stream : ObservationStream
  state : S
  metaUpdate_fix : metaUpdate agent = agent
  spec : AdaptiveAgentSpec agent stream state
  otherLatent : Latent
  self_ne : selfLatent ≠ otherLatent

namespace ReflexiveAdaptiveAgent

variable {S A Latent : Type*} [Fintype Latent] (R : ReflexiveAdaptiveAgent S A Latent)

/-- The meta-update of a reflexive agent has a fixed point, namely the agent. -/
theorem exists_metaUpdate_fixed_point : ∃ M, R.metaUpdate M = M :=
  exists_fixed_point_selfMap R.metaUpdate R.metaUpdate_fix

/-- A reflexive agent's plan is optimal in its current state. -/
theorem plan_optimal (a : A) :
    R.agent.efe R.state (R.agent.plan R.state) ≤ R.agent.efe R.state a := R.spec.minimizes a

/-- A reflexive agent's expected free energy is a genuine non-negative budget. -/
theorem efe_nonneg (a : A) : 0 ≤ R.agent.efe R.state a := R.agent.efe_nonneg _ _

/-- A reflexive agent's observation stream never dies out. -/
theorem stream_live : Live R.stream := R.spec.live

/-- A reflexive agent draws a distinction: its self-latent differs from another
latent it models. -/
theorem draws_self_distinction : ∃ z : Latent, R.selfLatent ≠ z := ⟨R.otherLatent, R.self_ne⟩

end ReflexiveAdaptiveAgent

end PolymathAtlas.AdaptiveAgent
