import RequestProject.OSA4.Repair
import RequestProject.OSA4.Identity
import RequestProject.OSA4.Epistemic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 Lawbook: the eighteen laws

`LawId` enumerates the eighteen laws of the OSA-4.0 discipline, `LawId.holds`
states each of them as a proposition, and `lawbook_holds` proves that every one
of them is a theorem of the kernel.
-/

namespace Polymath.OSA4

/-- The eighteen laws. -/
inductive LawId
  | LAW_001 | LAW_002 | LAW_003 | LAW_004 | LAW_005 | LAW_006 | LAW_007 | LAW_008 | LAW_009
  | LAW_010 | LAW_011 | LAW_012 | LAW_013 | LAW_014 | LAW_015 | LAW_016 | LAW_017 | LAW_018
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Human-readable title of each law. -/
def LawId.title : LawId → String
  | .LAW_001 => "Type reflexivity"
  | .LAW_002 => "Type transitivity"
  | .LAW_003 => "State conservation"
  | .LAW_004 => "No resurrection"
  | .LAW_005 => "Consume safety"
  | .LAW_006 => "Destroy/predicate liveness"
  | .LAW_007 => "Liveness soundness"
  | .LAW_008 => "Effect monotonicity"
  | .LAW_009 => "Epistemic non-overclaim"
  | .LAW_010 => "Composition soundness"
  | .LAW_011 => "Effect authorization"
  | .LAW_012 => "Weakest-precondition soundness and completeness"
  | .LAW_013 => "Join commutativity"
  | .LAW_014 => "Join associativity"
  | .LAW_015 => "Join idempotence"
  | .LAW_016 => "Recreation identity"
  | .LAW_017 => "Invalidation is not refutation"
  | .LAW_018 => "Repair soundness"

/-- The formal content of each law. -/
def LawId.holds : LawId → Prop
  | .LAW_001 => ∀ a : Ty, IsSubtype a a
  | .LAW_002 => ∀ a b c : Ty, IsSubtype a b → IsSubtype b c → IsSubtype a c
  | .LAW_003 => (∀ (o : Op) (s : KState) (f : FactId), f ∉ o.produces → f ∉ o.kill →
        (o.exec s).factStatus f = s.factStatus f) ∧
      (∀ (o : Op) (s : KState) (v : VarName), v ∉ o.modifies →
        (o.exec s).varValue v = s.varValue v)
  | .LAW_004 => ∀ (w : World) (i : ObjId), phaseOf w i = .Destroyed →
      ¬ legal w (.create i) ∧ ∀ old : ObjId, ¬ legal w (.recreate old i)
  | .LAW_005 => ∀ (w : World) (i : ObjId), legal w (.consume i) ↔ phaseOf w i = .Available
  | .LAW_006 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill →
      eval (o.exec s) (.factExists f) ≠ .TRUE_KNOWN
  | .LAW_007 => ∀ (reg ops : List Op) (s : KState), ChainOk reg ops s → chainEnabled ops s
  | .LAW_008 => ∀ l₁ l₂ : List EffectLevel,
      aggregate (l₁ ++ l₂) = EffectLevel.join (aggregate l₁) (aggregate l₂)
  | .LAW_009 => ∀ (ds : List Uncertainty) (u : Uncertainty), u ≤ propagate ds u
  | .LAW_010 => ∀ (a b : Op) (s : KState) (q : Pred),
      eval s (a.liveBefore (b.liveBefore q)) = .TRUE_KNOWN ↔
        a.enabled s ∧ b.enabled (a.exec s) ∧ eval (b.exec (a.exec s)) q = .TRUE_KNOWN
  | .LAW_011 => ∀ (o : Op) (s : KState), o.execAllowed s → o.requiresAuth = true →
      s.factStatus o.authFact = .TRUE_KNOWN
  | .LAW_012 => ∀ (o : Op) (s : KState) (q : Pred), eval s (o.wp q) = eval (o.exec s) q
  | .LAW_013 => ∀ a b : Belief, PT.join a b = PT.join b a
  | .LAW_014 => ∀ a b c : Belief, PT.join (PT.join a b) c = PT.join a (PT.join b c)
  | .LAW_015 => ∀ a : Belief, PT.join a a = a
  | .LAW_016 => ∀ (w : World) (old new : ObjId), legal w (.recreate old new) → new ≠ old
  | .LAW_017 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill →
      eval (o.exec s) (.pnot (.factExists f)) ≠ .TRUE_KNOWN
  | .LAW_018 => ∀ (sc : Scenario) (p : RepairPlan), bestRepair sc = some p →
      (compile (p.apply sc)).verdict = .PASS ∧ p ∈ oneStepRepairs sc ∧
      (∀ q ∈ oneStepRepairs sc, RVec.le p.cost q.cost)

/-- Every law of the OSA-4.0 lawbook is a theorem. -/
theorem lawbook_holds : ∀ l : LawId, l.holds := by
  intro l
  cases l with
  | LAW_001 => exact law001_subtype_refl
  | LAW_002 => exact fun _ _ _ h₁ h₂ => law002_subtype_trans h₁ h₂
  | LAW_003 =>
      exact ⟨fun o s _ hp hk => Op.factStatus_exec_untouched o s hp hk,
             fun o s _ hv => Op.varValue_exec_untouched o s hv⟩
  | LAW_004 => exact fun _ _ h => law004_no_resurrection h
  | LAW_005 => exact law005_consume_legal_iff
  | LAW_006 => exact fun o s _ hf => Op.law006_kill_live_fact o s hf
  | LAW_007 => exact fun reg ops s h => law007_pass_chainEnabled reg ops s h
  | LAW_008 => exact law008_aggregate_append
  | LAW_009 => exact law009_no_overclaim
  | LAW_010 => exact Op.law010_composition_sound
  | LAW_011 => exact fun _ _ h hr => Op.law011_exec_allowed_auth h hr
  | LAW_012 => exact Op.eval_wp
  | LAW_013 => exact law013_join_comm
  | LAW_014 => exact law014_join_assoc
  | LAW_015 => exact law015_join_idem
  | LAW_016 => exact fun _ _ _ h => law016_recreate_new_ne_old h
  | LAW_017 => exact fun o s _ hf => Op.law017_invalidate_not_refute o s hf
  | LAW_018 => exact fun _ _ h => law018_repair_sound h

theorem lawbook_card : Fintype.card LawId = 18 := by decide

end Polymath.OSA4
