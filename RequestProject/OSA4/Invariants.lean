import RequestProject.OSA4.Compiler

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 Invariants: frame properties along whole chains

The kernel proves the one-step frame laws (`Op.factStatus_exec_untouched`,
`Op.varValue_exec_untouched`).  This module lifts them to chains:

* `factStatus_execChain_untouched` / `varValue_execChain_untouched` — a fact or
  variable that no operator of the chain touches is preserved by the chain;
* `factStatus_execChain_preserved` — a known-true fact that no operator of the
  chain destroys stays known-true;
* `factStatus_execChain_established` — a fact produced somewhere in the chain
  and destroyed nowhere after that point is known-true at the end;
* `execChain_effect_le` — the effect level of a chain bounds the effect level of
  each of its operators.
-/

namespace Polymath.OSA4

/-! ## Frame properties -/

/-- A fact touched by no operator of the chain keeps its status. -/
theorem factStatus_execChain_untouched (ops : List Op) (s : KState) {f : FactId}
    (h : ∀ o ∈ ops, f ∉ o.produces ∧ f ∉ o.kill) :
    (execChain ops s).factStatus f = s.factStatus f := by
  induction ops generalizing s with
  | nil => rfl
  | cons o t ih =>
    have ho := h o (List.mem_cons_self ..)
    rw [execChain_cons, ih _ (fun p hp => h p (List.mem_cons_of_mem _ hp)),
      Op.factStatus_exec_untouched o s ho.1 ho.2]

/-- A variable modified by no operator of the chain keeps its value. -/
theorem varValue_execChain_untouched (ops : List Op) (s : KState) {v : VarName}
    (h : ∀ o ∈ ops, v ∉ o.modifies) :
    (execChain ops s).varValue v = s.varValue v := by
  induction ops generalizing s with
  | nil => rfl
  | cons o t ih =>
    rw [execChain_cons, ih _ (fun p hp => h p (List.mem_cons_of_mem _ hp)),
      Op.varValue_exec_untouched o s (h o (List.mem_cons_self ..))]

/-- A known-true fact that the chain never destroys is still known-true at the
end. -/
theorem factStatus_execChain_preserved (ops : List Op) (s : KState) {f : FactId}
    (hkill : ∀ o ∈ ops, f ∉ o.kill) (hs : s.factStatus f = PT.TRUE_KNOWN) :
    (execChain ops s).factStatus f = PT.TRUE_KNOWN := by
  induction ops generalizing s with
  | nil => exact hs
  | cons o t ih =>
    refine ih _ (fun p hp => hkill p (List.mem_cons_of_mem _ hp)) ?_
    by_cases hp : f ∈ o.produces
    · exact Op.factStatus_exec_produces o s hp
    · rw [Op.factStatus_exec_untouched o s hp (hkill o (List.mem_cons_self ..))]
      exact hs

/-- A fact produced by an operator of the chain and destroyed by none of the
later operators is known-true at the end of the chain. -/
theorem factStatus_execChain_established (pre post : List Op) (o : Op) (s : KState)
    {f : FactId} (hprod : f ∈ o.produces) (hkill : ∀ p ∈ post, f ∉ p.kill) :
    (execChain (pre ++ o :: post) s).factStatus f = PT.TRUE_KNOWN := by
  rw [execChain_append, execChain_cons]
  exact factStatus_execChain_preserved post _ hkill
    (Op.factStatus_exec_produces o _ hprod)

/-! ## Effects along a chain -/

/-- The aggregate effect level of a chain dominates the effect level of each of
its operators. -/
theorem execChain_effect_le {ops : List Op} {o : Op} (ho : o ∈ ops) :
    o.effect ≤ aggregate (ops.map (·.effect)) :=
  aggregate_le_of_mem (List.mem_map_of_mem ho)

/-- A chain of inert operators has inert aggregate effect. -/
theorem aggregate_eq_E0 {ops : List Op} (h : ∀ o ∈ ops, o.effect = EffectLevel.E0) :
    aggregate (ops.map (·.effect)) = EffectLevel.E0 := by
  induction ops with
  | nil => rfl
  | cons o t ih =>
    rw [List.map_cons, aggregate, ih (fun p hp => h p (List.mem_cons_of_mem _ hp)),
      h o (List.mem_cons_self ..)]
    rfl

/-! ## Invariants of a chain -/

/-- A predicate on states that every operator of the chain preserves. -/
def Invariant (P : KState → Prop) (ops : List Op) : Prop :=
  ∀ o ∈ ops, ∀ s : KState, P s → P (o.exec s)

/-- An invariant of every operator of the chain is an invariant of the chain. -/
theorem invariant_execChain {P : KState → Prop} {ops : List Op} (h : Invariant P ops)
    {s : KState} (hs : P s) : P (execChain ops s) := by
  induction ops generalizing s with
  | nil => exact hs
  | cons o t ih =>
    have h1 : P (o.exec s) := h o (List.mem_cons_self ..) s hs
    have h2 : Invariant P t := fun p hp => h p (List.mem_cons_of_mem _ hp)
    exact ih h2 h1

/-- "This fact is never destroyed" is an invariant in the above sense. -/
theorem invariant_factTrue {f : FactId} {ops : List Op} (h : ∀ o ∈ ops, f ∉ o.kill) :
    Invariant (fun s => s.factStatus f = PT.TRUE_KNOWN) ops := by
  intro o ho s hs
  by_cases hp : f ∈ o.produces
  · exact Op.factStatus_exec_produces o s hp
  · rw [Op.factStatus_exec_untouched o s hp (h o ho)]; exact hs

end Polymath.OSA4
