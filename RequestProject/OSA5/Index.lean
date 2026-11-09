import RequestProject.OSA5.Torture25
import RequestProject.OSA4.Audit.Integration

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-5.0 audit report

A single statement bundling the outcome of the OSA-5.0 audit: the twenty-five
torture tests pass, the six integration tests hold, and the bounded repair
search is exactly characterised — it succeeds precisely when a correct repair
plan exists within the fuel budget.
-/

namespace Polymath.OSA5

open Polymath.OSA4

/-- The OSA-5.0 audit report. -/
theorem osa5_audit_report :
    (∀ t : TortureId25, t.passed) ∧
    (∀ t : IntegrationTest, t.claim) ∧
    (∀ (reg : List Op) (goal : Pred) (n : ℕ) (s : KState),
      (searchRepair reg goal n s).isSome ↔
        ∃ ops, RepairCorrect reg goal s ops ∧ ops.length ≤ n) :=
  ⟨torture25_all_pass, integration_all_pass, searchRepair_isSome_iff⟩

/-- The suite sizes recorded by the audit. -/
theorem osa5_audit_cardinalities :
    Fintype.card TortureId25 = 25 ∧ Fintype.card IntegrationTest = 6 ∧
      Fintype.card LawId = 18 :=
  ⟨torture25_card, integration_card, lawbook_card⟩

end Polymath.OSA5
