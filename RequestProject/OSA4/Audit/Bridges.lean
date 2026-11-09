import RequestProject.OSA4.Audit.Consistency
import RequestProject.OSA4.Criteria

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Audit: coherence of the layers

The OSA-4.0 stack has three layers — the kernel semantics, the static compiler
and the acceptance criteria — and each must agree with the one below it.

* `kernel_compiler_coherent` — the compiler passes exactly the chains the kernel
  says are well-formed and goal-establishing;
* `criteria_compiler_coherent` — the criteria layer agrees with the compiler;
* `wp_chain_coherent` — the syntactic chain transformer agrees with execution;
* `effect_chain_coherent` — effect accounting is compositional;
* `bridges_audit` — the four coherence statements, bundled.
-/

namespace Polymath.OSA4.Audit

open Polymath.OSA4

theorem kernel_compiler_coherent (sc : Scenario) :
    (compile sc).verdict = .PASS ↔
      ChainOk sc.registry sc.chain sc.init ∧
        eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN :=
  compile_verdict_pass_iff sc

theorem criteria_compiler_coherent (sc : Scenario) :
    (compile sc).verdict = .PASS ↔
      Criterion.wellFormed.holds sc ∧ Criterion.achievesGoal.holds sc :=
  pass_iff_criteria sc

theorem wp_chain_coherent (ops : List Op) (s : KState) (q : Pred) :
    eval s (wpChain ops q) = eval (execChain ops s) q :=
  eval_execChain_eq_eval_wpChain ops s q

theorem effect_chain_coherent (x y : List Op) :
    chainEffect (x ++ y) = EffectLevel.join (chainEffect x) (chainEffect y) :=
  chainEffect_append x y

/-- The four layers of the stack agree. -/
theorem bridges_audit :
    (∀ sc : Scenario, (compile sc).verdict = .PASS ↔
        ChainOk sc.registry sc.chain sc.init ∧
          eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN) ∧
    (∀ sc : Scenario, (compile sc).verdict = .PASS ↔
        Criterion.wellFormed.holds sc ∧ Criterion.achievesGoal.holds sc) ∧
    (∀ (ops : List Op) (s : KState) (q : Pred),
        eval s (wpChain ops q) = eval (execChain ops s) q) ∧
    (∀ x y : List Op,
        chainEffect (x ++ y) = EffectLevel.join (chainEffect x) (chainEffect y)) :=
  ⟨kernel_compiler_coherent, criteria_compiler_coherent, wp_chain_coherent,
   effect_chain_coherent⟩

end Polymath.OSA4.Audit
