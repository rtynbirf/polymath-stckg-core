import RequestProject.OSA4.Invariants
import RequestProject.OSA4.Effects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 state spaces

Two knowledge states that agree on every fact and every variable are
*observationally equal*: no predicate of the kernel language can tell them
apart, and no operator or chain of operators can drive them apart.  On top of
this we describe the reachability space of a registry.

* `Polymath.OSA4.Agree` — observational agreement of two states;
* `Polymath.OSA4.eval_congr` — agreeing states evaluate every predicate alike;
* `Polymath.OSA4.agree_exec` and `Polymath.OSA4.agree_execChain` — agreement is
  preserved by execution;
* `Polymath.OSA4.enabled_congr` — agreeing states enable the same operators;
* `Polymath.OSA4.Reachable` — the reachability relation of a registry, shown
  reflexive and transitive, with preserved facts and bounded effects.
-/

namespace Polymath.OSA4

/-! ## Observational agreement -/

/-- Two states agree when they assign the same status to every fact and the
same value to every variable. -/
def Agree (s t : KState) : Prop :=
  (∀ f : FactId, s.factStatus f = t.factStatus f) ∧ (∀ v : VarName, s.varValue v = t.varValue v)

theorem agree_refl (s : KState) : Agree s s := ⟨fun _ => rfl, fun _ => rfl⟩

theorem agree_symm {s t : KState} (h : Agree s t) : Agree t s :=
  ⟨fun f => (h.1 f).symm, fun v => (h.2 v).symm⟩

theorem agree_trans {s t u : KState} (h₁ : Agree s t) (h₂ : Agree t u) : Agree s u :=
  ⟨fun f => (h₁.1 f).trans (h₂.1 f), fun v => (h₁.2 v).trans (h₂.2 v)⟩

/-- Agreeing states evaluate every predicate to the same truth value. -/
theorem eval_congr {s t : KState} (h : Agree s t) (p : Pred) : eval s p = eval t p := by
  induction p with
  | factExists f => simp [eval, h.1 f]
  | pnot p ih => simp [eval, ih]
  | pand p q ihp ihq => simp [eval, ihp, ihq]
  | por p q ihp ihq => simp [eval, ihp, ihq]
  | pimp p q ihp ihq => simp [eval, ihp, ihq]
  | gte v n => simp [eval, h.2 v]
  | peq v n => simp [eval, h.2 v]
  | ctrue => rfl
  | cfalse => rfl
  | cunknown => rfl

/-- Agreeing states enable exactly the same operators. -/
theorem enabled_congr {s t : KState} (h : Agree s t) (o : Op) : o.enabled s ↔ o.enabled t := by
  constructor
  · intro hen p hp; rw [← eval_congr h p]; exact hen p hp
  · intro hen p hp; rw [eval_congr h p]; exact hen p hp

/-- Executing an operator in agreeing states yields agreeing states. -/
theorem agree_exec {s t : KState} (h : Agree s t) (o : Op) : Agree (o.exec s) (o.exec t) := by
  constructor
  · intro f
    by_cases hp : f ∈ o.produces
    · rw [Op.factStatus_exec_produces o s hp, Op.factStatus_exec_produces o t hp]
    · by_cases hk : f ∈ o.kill
      · rw [Op.factStatus_exec_kill o s hk, Op.factStatus_exec_kill o t hk]
      · rw [Op.factStatus_exec_untouched o s hp hk, Op.factStatus_exec_untouched o t hp hk]
        exact h.1 f
  · intro v
    by_cases hv : v ∈ o.modifies
    · rw [Op.varValue_exec_modifies o s hv, Op.varValue_exec_modifies o t hv]
    · rw [Op.varValue_exec_untouched o s hv, Op.varValue_exec_untouched o t hv]
      exact h.2 v

/-- Agreement is preserved along a whole chain. -/
theorem agree_execChain {s t : KState} (h : Agree s t) (ops : List Op) :
    Agree (execChain ops s) (execChain ops t) := by
  induction ops generalizing s t with
  | nil => exact h
  | cons o rest ih => exact ih (agree_exec h o)

/-- Agreeing states are indistinguishable by whole chains: they enable the same
chains and reach agreeing results. -/
theorem chainEnabled_congr {s t : KState} (h : Agree s t) (ops : List Op) :
    chainEnabled ops s ↔ chainEnabled ops t := by
  induction ops generalizing s t with
  | nil => simp
  | cons o rest ih =>
    rw [chainEnabled_cons, chainEnabled_cons, enabled_congr h o]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (ih (agree_exec h o)).1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (ih (agree_exec h o)).2 h2⟩

/-! ## Reachability -/

/-- A state is reachable from another when some enabled chain of registry
operators leads from one to the other. -/
def Reachable (reg : List Op) (s t : KState) : Prop :=
  ∃ ops : List Op, (∀ o ∈ ops, o ∈ reg) ∧ chainEnabled ops s ∧ execChain ops s = t

theorem reachable_refl (reg : List Op) (s : KState) : Reachable reg s s :=
  ⟨[], by simp, trivial, rfl⟩

theorem reachable_step {reg : List Op} {s : KState} {o : Op} (ho : o ∈ reg)
    (hen : o.enabled s) : Reachable reg s (o.exec s) :=
  ⟨[o], by simpa using ho, ⟨hen, trivial⟩, rfl⟩

theorem reachable_trans {reg : List Op} {s t u : KState}
    (h₁ : Reachable reg s t) (h₂ : Reachable reg t u) : Reachable reg s u := by
  obtain ⟨x, hx, hxen, rfl⟩ := h₁
  obtain ⟨y, hy, hyen, rfl⟩ := h₂
  refine ⟨x ++ y, ?_, chainEnabled_append hxen hyen, ?_⟩
  · intro o ho
    rcases List.mem_append.1 ho with h | h
    · exact hx o h
    · exact hy o h
  · rw [execChain_append]

/-- A fact that no operator of the registry destroys survives every reachable
transition. -/
theorem factStatus_reachable_preserved {reg : List Op} {s t : KState} {f : FactId}
    (hreg : ∀ o ∈ reg, f ∉ o.kill) (h : Reachable reg s t)
    (hs : s.factStatus f = PT.TRUE_KNOWN) : t.factStatus f = PT.TRUE_KNOWN := by
  obtain ⟨ops, hops, -, rfl⟩ := h
  exact factStatus_execChain_preserved ops s (fun o ho => hreg o (hops o ho)) hs

/-- Reachability through inert operators cannot exceed the inert effect level. -/
theorem chainEffect_reachable_E0 {reg : List Op} {s t : KState}
    (hreg : ∀ o ∈ reg, o.effect = EffectLevel.E0) (h : Reachable reg s t) :
    ∃ ops : List Op, chainEffect ops = EffectLevel.E0 ∧ execChain ops s = t := by
  obtain ⟨ops, hops, -, rfl⟩ := h
  exact ⟨ops, aggregate_eq_E0 (fun o ho => hreg o (hops o ho)), rfl⟩

/-- Reachability is invariant under observational agreement of the source. -/
theorem reachable_congr {reg : List Op} {s t : KState} (h : Agree s t) {u : KState}
    (hu : Reachable reg s u) : ∃ u' : KState, Reachable reg t u' ∧ Agree u u' := by
  obtain ⟨ops, hops, hen, rfl⟩ := hu
  exact ⟨execChain ops t, ⟨ops, hops, (chainEnabled_congr h ops).1 hen, rfl⟩,
    agree_execChain h ops⟩

end Polymath.OSA4
