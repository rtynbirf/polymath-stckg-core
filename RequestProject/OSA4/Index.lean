import RequestProject.OSA4.Audit
import RequestProject.OSA4.Registry
import RequestProject.OSA4.Invariants
import RequestProject.OSA4.BasisWitnesses
import RequestProject.OSA4.Spaces
import RequestProject.OSA4.Axes
import RequestProject.OSA4.MetaSchema

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 index

Aggregation module for the OSA-4.0 tower: the kernel, the compiler, the
identity and epistemic layers, one-step repair, the lawbook, the registry, the
chain invariants, the ninety-item basis with its witnesses, and the full audit.  `osa4_summary` collects the headline
guarantees in a single statement.
-/

namespace Polymath.OSA4

/-- The headline guarantees of OSA-4.0. -/
theorem osa4_summary :
    (∀ l : LawId, l.holds) ∧
    (∀ (o : Op) (s : KState) (q : Pred), eval s (o.wp q) = eval (o.exec s) q) ∧
    (∀ sc : Scenario, (compile sc).verdict = .PASS ↔
      ChainOk sc.registry sc.chain sc.init ∧
        eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN) ∧
    (∀ t : TortureId, t.claim) ∧
    (∀ t : TortureId20, t.claim) ∧
    (∀ t : IntegrationTest, t.claim) ∧
    (∀ b : BasisId, b.claim) ∧
    (∀ w : WitnessId, w.claim) :=
  ⟨lawbook_holds, Op.eval_wp, compile_verdict_pass_iff, torture_all_pass,
   torture20_all_pass, integration_all_pass, basis_all_covered, witness_all_hold⟩

end Polymath.OSA4
