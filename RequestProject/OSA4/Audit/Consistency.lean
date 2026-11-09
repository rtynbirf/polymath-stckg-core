import RequestProject.OSA4.Audit.Witness
import RequestProject.OSA4.Lawbook

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Audit: cross-law consistency

Laws 006 and 017 pull in opposite directions — a destroyed fact must not stay
known, but destroying it must not make its negation known either.  They are
consistent because destruction lands in `UNKNOWN`
(`kill_exec_status_unknown`), and they are not vacuous, since the registry
contains operators that really do destroy facts
(`destroying_operator_exists`).

* `belief_join_semilattice` — laws 013–015 make the belief join a semilattice;
* `lawbook_consistent` — the eighteen laws hold simultaneously;
* `pass_sound` — a `PASS` verdict really does imply enabled steps and an
  established goal.
-/

namespace Polymath.OSA4.Audit

open Polymath.OSA4

/-- Destroying a fact makes it unknown: neither the fact nor its negation
becomes known. -/
theorem kill_exec_status_unknown (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.kill) :
    (o.exec s).factStatus f = PT.UNKNOWN := Op.factStatus_exec_kill o s hf

/-- Laws 006 and 017 are jointly satisfiable: they are two readings of the same
`UNKNOWN` outcome. -/
theorem law006_law017_consistent (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.kill) :
    eval (o.exec s) (.factExists f) ≠ PT.TRUE_KNOWN ∧
    eval (o.exec s) (.pnot (.factExists f)) ≠ PT.TRUE_KNOWN :=
  ⟨Op.law006_kill_live_fact o s hf, Op.law017_invalidate_not_refute o s hf⟩

/-- The laws about destruction are not vacuous: the registry destroys facts. -/
theorem destroying_operator_exists : ∃ o ∈ registry, o.kill ≠ [] :=
  ⟨opDELETE_Y, by decide, by decide⟩

/-- Laws 013–015: the belief join is a commutative, associative, idempotent
operation. -/
theorem belief_join_semilattice :
    (∀ a b : Belief, PT.join a b = PT.join b a) ∧
    (∀ a b c : Belief, PT.join (PT.join a b) c = PT.join a (PT.join b c)) ∧
    (∀ a : Belief, PT.join a a = a) :=
  ⟨law013_join_comm, law014_join_assoc, law015_join_idem⟩

/-- All eighteen laws hold at once, so the lawbook is consistent. -/
theorem lawbook_consistent : ∀ l : LawId, l.holds := lawbook_holds

/-- A `PASS` verdict is sound: every step was enabled and the goal is
established. -/
theorem pass_sound (sc : Scenario) (h : (compile sc).verdict = .PASS) :
    chainEnabled sc.chain sc.init ∧
      eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN := by
  obtain ⟨hok, hgoal⟩ := (compile_verdict_pass_iff sc).1 h
  exact ⟨law007_pass_chainEnabled _ _ _ hok, hgoal⟩

/-- The compiler is not trivially permissive: some scenarios fail. -/
theorem pass_not_universal : ∃ sc : Scenario, (compile sc).verdict ≠ .PASS :=
  ⟨verdictWitness .REJECT, by rw [verdict_witness]; decide⟩

/-- ... and not trivially restrictive: some scenarios pass. -/
theorem pass_nonempty : ∃ sc : Scenario, (compile sc).verdict = .PASS :=
  ⟨verdictWitness .PASS, verdict_witness .PASS⟩

end Polymath.OSA4.Audit
