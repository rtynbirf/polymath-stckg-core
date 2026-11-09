import RequestProject.OSA4.Compiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Effect accounting for operator chains

The effect level of a chain is the aggregate of the effect levels of its
operators.  This module develops the resulting budget calculus:

* `chainEffect`, `chainEffect_append` — aggregation is a monoid homomorphism
  from concatenation to the join of effect levels (LAW-008 lifted to chains);
* `chainEffect_le_iff` — a chain stays inside a budget exactly when each of its
  operators does, so `WithinBudget` is decidable and closed under sublists;
* `chainEffect_eq_E4_of_mem` — a single irreversible step makes the whole chain
  irreversible;
* `NonDestructive` and `factStatus_exec_of_nonDestructive` — an operator that
  destroys nothing never turns a known fact off.
-/

namespace Polymath.OSA4

/-- The aggregate effect level of a chain of operators. -/
def chainEffect (ops : List Op) : EffectLevel := aggregate (ops.map Op.effect)

@[simp] theorem chainEffect_nil : chainEffect [] = EffectLevel.E0 := rfl

@[simp] theorem chainEffect_cons (o : Op) (t : List Op) :
    chainEffect (o :: t) = EffectLevel.join o.effect (chainEffect t) := rfl

/-- Aggregation of effects is a homomorphism from concatenation to `join`. -/
theorem chainEffect_append (x y : List Op) :
    chainEffect (x ++ y) = EffectLevel.join (chainEffect x) (chainEffect y) := by
  simp [chainEffect, List.map_append, law008_aggregate_append]

/-- Every operator of a chain stays below the chain's effect level. -/
theorem op_effect_le_chainEffect {o : Op} {ops : List Op} (h : o ∈ ops) :
    o.effect ≤ chainEffect ops :=
  aggregate_le_of_mem (List.mem_map_of_mem h)

/-- A chain fits in a budget exactly when each of its operators does. -/
theorem chainEffect_le_iff (ops : List Op) (b : EffectLevel) :
    chainEffect ops ≤ b ↔ ∀ o ∈ ops, o.effect ≤ b := by
  induction ops with
  | nil => simp
  | cons o t ih =>
      simp only [chainEffect_cons, EffectLevel.join, max_le_iff, List.mem_cons,
        forall_eq_or_imp, ih]

/-- A chain of operators stays inside an effect budget. -/
def WithinBudget (b : EffectLevel) (ops : List Op) : Prop := chainEffect ops ≤ b

instance (b : EffectLevel) (ops : List Op) : Decidable (WithinBudget b ops) := by
  unfold WithinBudget; infer_instance

theorem withinBudget_iff (b : EffectLevel) (ops : List Op) :
    WithinBudget b ops ↔ ∀ o ∈ ops, o.effect ≤ b := chainEffect_le_iff ops b

theorem withinBudget_append_iff (b : EffectLevel) (x y : List Op) :
    WithinBudget b (x ++ y) ↔ WithinBudget b x ∧ WithinBudget b y := by
  simp only [withinBudget_iff, List.mem_append, or_imp, forall_and]

/-- Dropping steps never leaves an effect budget. -/
theorem WithinBudget.sublist {b : EffectLevel} {x y : List Op} (hsub : x.Sublist y)
    (h : WithinBudget b y) : WithinBudget b x :=
  (withinBudget_iff b x).2 fun o ho => (withinBudget_iff b y).1 h o (hsub.mem ho)

/-- Nothing exceeds the top effect level. -/
theorem withinBudget_E4 (ops : List Op) : WithinBudget EffectLevel.E4 ops :=
  (withinBudget_iff _ ops).2 fun o _ => by
    cases o.effect <;> simp [EffectLevel.le_iff_rank_le, EffectLevel.rank]

/-- One irreversible step makes the whole chain irreversible. -/
theorem chainEffect_eq_E4_of_mem {o : Op} {ops : List Op} (ho : o ∈ ops)
    (h4 : o.effect = EffectLevel.E4) : chainEffect ops = EffectLevel.E4 := by
  have hle : EffectLevel.E4 ≤ chainEffect ops := h4 ▸ op_effect_le_chainEffect ho
  have htop : chainEffect ops ≤ EffectLevel.E4 := withinBudget_E4 ops
  exact le_antisymm htop hle

/-- An inert chain is a chain of inert operators. -/
theorem chainEffect_eq_E0_iff (ops : List Op) :
    chainEffect ops = EffectLevel.E0 ↔ ∀ o ∈ ops, o.effect = EffectLevel.E0 := by
  constructor
  · intro h o ho
    have := op_effect_le_chainEffect ho
    rw [h] at this
    exact le_antisymm this (EffectLevel.E0_le _)
  · intro h
    refine le_antisymm ((chainEffect_le_iff ops _).2 fun o ho => le_of_eq (h o ho)) ?_
    exact EffectLevel.E0_le _

/-! ## Non-destructive operators -/

/-- An operator is non-destructive when it destroys no fact. -/
def NonDestructive (o : Op) : Prop := o.kill = []

/-- A non-destructive operator never turns a known fact off. -/
theorem factStatus_exec_of_nonDestructive {o : Op} (ho : NonDestructive o) (s : KState)
    {f : FactId} (hf : s.factStatus f = PT.TRUE_KNOWN) :
    (o.exec s).factStatus f = PT.TRUE_KNOWN := by
  by_cases hp : f ∈ o.produces
  · exact Op.factStatus_exec_produces o s hp
  · have hk : f ∉ o.kill := by rw [ho]; simp
    rw [Op.factStatus_exec_untouched o s hp hk]
    exact hf

/-- A chain of non-destructive operators never turns a known fact off. -/
theorem factStatus_execChain_of_nonDestructive {ops : List Op}
    (ho : ∀ o ∈ ops, NonDestructive o) (s : KState) {f : FactId}
    (hf : s.factStatus f = PT.TRUE_KNOWN) :
    (execChain ops s).factStatus f = PT.TRUE_KNOWN := by
  induction ops generalizing s with
  | nil => simpa using hf
  | cons o t ih =>
      rw [execChain_cons]
      exact ih (fun p hp => ho p (List.mem_cons_of_mem _ hp)) (o.exec s)
        (factStatus_exec_of_nonDestructive (ho o List.mem_cons_self) s hf)

end Polymath.OSA4
