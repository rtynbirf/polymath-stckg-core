import RequestProject.OSA4.Audit.TypeSystem
import RequestProject.OSA4.Audit.Effects
import RequestProject.OSA4.Audit.Operators
import RequestProject.OSA4.Audit.Witness
import RequestProject.OSA4.Audit.Consistency
import RequestProject.OSA4.Audit.Bridges
import RequestProject.OSA4.Audit.Torture20
import RequestProject.OSA4.Audit.Integration

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 audit report

The audit is the conjunction of every check performed by the modules of
`RequestProject.OSA4.Audit`: the type lattice, the effect algebra, the operator
contracts, the reachability witnesses, cross-law consistency, layer coherence,
the extended torture suite, and the integration tests.
-/

namespace Polymath.OSA4.Audit

open Polymath.OSA4

/-- The full OSA-4.0 audit report. -/
theorem audit_report :
    -- the type lattice is a bounded partial order
    (∀ a b : Ty, IsSubtype a b → IsSubtype b a → a = b) ∧
    (∀ a : Ty, IsSubtype .Bot a ∧ IsSubtype a .Top) ∧
    -- the effect algebra aggregates as a supremum
    (∀ (l : List EffectLevel) (b : EffectLevel), aggregate l ≤ b ↔ ∀ e ∈ l, e ≤ b) ∧
    -- the registry is well-formed
    (registry.map (·.name)).Nodup ∧
    (∀ o ∈ registry, (o.requiresAuth = true ↔ o.name = "DEPLOY")) ∧
    -- every verdict and every error is reachable
    (∀ v : Verdict, ∃ sc : Scenario, (compile sc).verdict = v) ∧
    -- the eighteen laws hold
    (∀ l : LawId, l.holds) ∧
    -- the layers agree
    (∀ sc : Scenario, (compile sc).verdict = .PASS ↔
      Criterion.wellFormed.holds sc ∧ Criterion.achievesGoal.holds sc) ∧
    -- the torture suite and the integration tests pass
    (∀ t : TortureId20, t.claim) ∧
    (∀ t : IntegrationTest, t.claim) :=
  ⟨fun _ _ h₁ h₂ => isSubtype_antisymm h₁ h₂,
   fun a => ⟨bot_isSubtype a, isSubtype_top a⟩,
   aggregate_le_iff,
   registry_names_nodup,
   registry_auth_iff_deploy,
   every_verdict_reachable,
   lawbook_consistent,
   criteria_compiler_coherent,
   torture20_all_pass,
   integration_all_pass⟩

/-- The cardinalities the audit reports. -/
theorem audit_cardinalities :
    Fintype.card LawId = 18 ∧
    Fintype.card TortureId20 = 20 ∧
    Fintype.card IntegrationTest = 6 ∧
    Fintype.card EffectLevel = 5 ∧
    registry.length = 17 :=
  ⟨lawbook_card, torture20_card, integration_card, effectLevel_card, registry_card⟩

end Polymath.OSA4.Audit
