import RequestProject.OSA4.Audit.Integration
import RequestProject.OSA5.Torture25
import RequestProject.OSA5.Pipeline

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Canon: the self-description of the development

The development describes itself by a small record of counts, `atlasStats`.  The
point of the module is that the counts are not merely asserted: each of them is
tied back to a theorem of the development.

* `atlasStats_laws` — the recorded number of laws is the cardinality of `LawId`,
  every one of which is proved to hold (`lawbook_holds`);
* `atlasStats_torture` — the recorded number of torture tests is the cardinality
  of `TortureId25`, every one of which passes (`torture25_all_pass`);
* `atlasStats_integration` — likewise for the integration tests;
* `canon_selfConsistent` — the three statements bundled with the corresponding
  "all pass" theorems, so the self-description cannot drift away from the
  artifacts it describes.
-/

namespace PolymathAtlas.Gestalt.Canon

open Polymath.OSA4 Polymath.OSA5

/-- A record of the checkable counts of the development. -/
structure AtlasStats where
  /-- Number of laws in the OSA-4.0 lawbook. -/
  laws : ℕ
  /-- Number of torture tests in the OSA-5.0 suite. -/
  tortureTests : ℕ
  /-- Number of integration tests in the audit layer. -/
  integrationTests : ℕ
  deriving DecidableEq, Repr

/-- The recorded counts. -/
def atlasStats : AtlasStats where
  laws := 18
  tortureTests := 25
  integrationTests := 6

theorem atlasStats_laws : atlasStats.laws = Fintype.card LawId := lawbook_card.symm

theorem atlasStats_torture : atlasStats.tortureTests = Fintype.card TortureId25 :=
  torture25_card.symm

theorem atlasStats_integration :
    atlasStats.integrationTests = Fintype.card IntegrationTest := integration_card.symm

/-- The self-description agrees with the artifacts: the recorded counts are the
cardinalities of the corresponding index types, and every law holds and every
test passes. -/
theorem canon_selfConsistent :
    (atlasStats.laws = Fintype.card LawId ∧ ∀ l : LawId, l.holds) ∧
    (atlasStats.tortureTests = Fintype.card TortureId25 ∧ ∀ t : TortureId25, t.passed) ∧
    (atlasStats.integrationTests = Fintype.card IntegrationTest ∧
      ∀ t : IntegrationTest, t.claim) :=
  ⟨⟨atlasStats_laws, lawbook_holds⟩,
    ⟨atlasStats_torture, torture25_all_pass⟩,
    ⟨atlasStats_integration, integration_all_pass⟩⟩

/-- The repair pipeline is part of the canon: it is exact, and on the standard
failing scenario it produces a plan that compiles. -/
theorem canon_pipeline :
    (∀ sc : Scenario, ∀ fuel : ℕ, pipeline sc fuel = .irreparable ↔
        (compile sc).verdict ≠ Verdict.PASS ∧
        ¬ ∃ plan, RepairCorrect sc.registry (chainPred sc.chain sc.goal) sc.init plan ∧
          plan.length ≤ fuel) ∧
      pipeline modelScenario 2 = .repaired [opMEASURE, opCHECK_SUFFICIENCY] [opMODEL] :=
  ⟨pipeline_irreparable_iff, pipeline_modelScenario⟩

end PolymathAtlas.Gestalt.Canon
