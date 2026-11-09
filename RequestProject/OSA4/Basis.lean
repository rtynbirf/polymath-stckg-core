import RequestProject.OSA4.Lawbook
import RequestProject.OSA4.Criteria
import RequestProject.OSA4.Invariants
import RequestProject.OSA4.Registry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# OSA-4.0 basis: ninety kernel facts, all covered

The *basis* is an explicit enumeration of the ninety elementary facts on which
the OSA-4.0 semantics rests: the four-valued truth algebra, the effect lattice,
the state operations, the execution and weakest-precondition calculus, the
chain laws, the compiler characterisation, the identity and epistemic layers,
one-step repair, and the concrete operator registry.

Each item of `BasisId` carries a formal `claim`, and `basis_all_covered` proves
every one of them; `basis_card` records that there are exactly ninety.
-/

namespace Polymath.OSA4

/-- Identifiers of the ninety basis facts. -/
inductive BasisId
  | B01 | B02 | B03 | B04 | B05 | B06 | B07 | B08 | B09 | B10
  | B11 | B12 | B13 | B14 | B15 | B16 | B17 | B18 | B19 | B20
  | B21 | B22 | B23 | B24 | B25 | B26 | B27 | B28 | B29 | B30
  | B31 | B32 | B33 | B34 | B35 | B36 | B37 | B38 | B39 | B40
  | B41 | B42 | B43 | B44 | B45 | B46 | B47 | B48 | B49 | B50
  | B51 | B52 | B53 | B54 | B55 | B56 | B57 | B58 | B59 | B60
  | B61 | B62 | B63 | B64 | B65 | B66 | B67 | B68 | B69 | B70
  | B71 | B72 | B73 | B74 | B75 | B76 | B77 | B78 | B79 | B80
  | B81 | B82 | B83 | B84 | B85 | B86 | B87 | B88 | B89 | B90
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The formal content of each basis fact. -/
def BasisId.claim : BasisId → Prop
  -- The four-valued truth algebra.
  | .B01 => ∀ a : PT, PT.neg (PT.neg a) = a
  | .B02 => ∀ a b : PT, PT.neg (PT.and a b) = PT.or (PT.neg a) (PT.neg b)
  | .B03 => ∀ a b : PT, PT.neg (PT.or a b) = PT.and (PT.neg a) (PT.neg b)
  | .B04 => ∀ a b : PT, PT.and a b = PT.and b a
  | .B05 => ∀ a b : PT, PT.or a b = PT.or b a
  | .B06 => ∀ a b c : PT, PT.and (PT.and a b) c = PT.and a (PT.and b c)
  | .B07 => ∀ a b c : PT, PT.or (PT.or a b) c = PT.or a (PT.or b c)
  | .B08 => ∀ a : PT, PT.and a a = a
  | .B09 => ∀ a : PT, PT.or a a = a
  | .B10 => ∀ a : PT, PT.and PT.TRUE_KNOWN a = a
  | .B11 => ∀ a : PT, PT.and a PT.TRUE_KNOWN = a
  | .B12 => ∀ a b : PT, PT.and a b = PT.TRUE_KNOWN ↔ a = PT.TRUE_KNOWN ∧ b = PT.TRUE_KNOWN
  | .B13 => ∀ a b : PT, PT.imp a b = PT.or (PT.neg a) b
  | .B14 => ∀ a b : PT, PT.join a b = PT.join b a
  | .B15 => ∀ a b c : PT, PT.join (PT.join a b) c = PT.join a (PT.join b c)
  | .B16 => ∀ a : PT, PT.join a a = a
  | .B17 => ∀ a : PT, PT.join PT.UNKNOWN a = a
  | .B18 => PT.join PT.TRUE_KNOWN PT.FALSE_KNOWN = PT.CONFLICT
  | .B19 => ∀ a : PT, PT.join PT.CONFLICT a = PT.CONFLICT
  | .B20 => Fintype.card PT = 4
  -- The effect lattice.
  | .B21 => Function.Injective EffectLevel.rank
  | .B22 => ∀ a : EffectLevel, EffectLevel.E0 ≤ a
  | .B23 => ∀ a : EffectLevel, EffectLevel.join a EffectLevel.E0 = a
  | .B24 => ∀ a b c : EffectLevel,
      EffectLevel.join (EffectLevel.join a b) c = EffectLevel.join a (EffectLevel.join b c)
  | .B25 => ∀ l₁ l₂ : List EffectLevel,
      aggregate (l₁ ++ l₂) = EffectLevel.join (aggregate l₁) (aggregate l₂)
  | .B26 => ∀ (l : List EffectLevel) (e : EffectLevel), e ∈ l → e ≤ aggregate l
  | .B27 => Fintype.card EffectLevel = 5
  | .B28 => ∀ ops : List Op, WithinBudget EffectLevel.E4 ops
  | .B29 => ∀ (b : EffectLevel) (x y : List Op),
      WithinBudget b (x ++ y) ↔ WithinBudget b x ∧ WithinBudget b y
  | .B30 => ∀ x y : List Op,
      chainEffect (x ++ y) = EffectLevel.join (chainEffect x) (chainEffect y)
  -- Knowledge states.
  | .B31 => ∀ (s : KState) (f : FactId) (v : PT), (s.setFact f v).factStatus f = v
  | .B32 => ∀ (s : KState) (f g : FactId) (v : PT), g ≠ f →
      (s.setFact f v).factStatus g = s.factStatus g
  | .B33 => ∀ (s : KState) (f : FactId) (v : PT) (w : VarName),
      (s.setFact f v).varValue w = s.varValue w
  | .B34 => ∀ (s : KState) (v : VarName), (s.clearVar v).varValue v = none
  | .B35 => ∀ (s : KState) (v w : VarName), w ≠ v →
      (s.clearVar v).varValue w = s.varValue w
  | .B36 => ∀ (s : KState) (v : VarName) (f : FactId),
      (s.clearVar v).factStatus f = s.factStatus f
  | .B37 => ∀ (fs : List FactId) (f : FactId), f ∉ fs → ∀ (v : PT) (s : KState),
      (setFacts fs v s).factStatus f = s.factStatus f
  | .B38 => ∀ (fs : List FactId) (f : FactId), f ∈ fs → ∀ (v : PT) (s : KState),
      (setFacts fs v s).factStatus f = v
  | .B39 => ∀ (vs : List VarName) (w : VarName), w ∉ vs → ∀ s : KState,
      (clearVars vs s).varValue w = s.varValue w
  | .B40 => ∀ (vs : List VarName) (w : VarName), w ∈ vs → ∀ s : KState,
      (clearVars vs s).varValue w = none
  -- Operators and execution.
  | .B41 => ∀ (o : Op) (f : FactId),
      f ∈ o.kill ↔ (f ∈ o.consumes ∨ f ∈ o.invalidates) ∧ f ∉ o.produces
  | .B42 => ∀ (o : Op) (f : FactId), f ∈ o.kill → f ∉ o.produces
  | .B43 => ∀ (o : Op) (f : FactId), f ∈ o.produces → f ∉ o.kill
  | .B44 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.produces →
      (o.exec s).factStatus f = PT.TRUE_KNOWN
  | .B45 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill →
      (o.exec s).factStatus f = PT.UNKNOWN
  | .B46 => ∀ (o : Op) (s : KState) (f : FactId), f ∉ o.produces → f ∉ o.kill →
      (o.exec s).factStatus f = s.factStatus f
  | .B47 => ∀ (o : Op) (s : KState) (v : VarName), v ∉ o.modifies →
      (o.exec s).varValue v = s.varValue v
  | .B48 => ∀ (o : Op) (s : KState) (v : VarName), v ∈ o.modifies →
      (o.exec s).varValue v = none
  | .B49 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill →
      eval (o.exec s) (.factExists f) ≠ PT.TRUE_KNOWN
  | .B50 => ∀ (o : Op) (s : KState) (f : FactId), f ∈ o.kill →
      eval (o.exec s) (.pnot (.factExists f)) ≠ PT.TRUE_KNOWN
  -- Weakest preconditions.
  | .B51 => ∀ (o : Op) (s : KState) (q : Pred), eval s (o.wp q) = eval (o.exec s) q
  | .B52 => ∀ (o : Op) (s : KState) (q : Pred), eval s (o.wp q) = PT.TRUE_KNOWN →
      eval (o.exec s) q = PT.TRUE_KNOWN
  | .B53 => ∀ (o : Op) (s : KState) (q : Pred), eval (o.exec s) q = PT.TRUE_KNOWN →
      eval s (o.wp q) = PT.TRUE_KNOWN
  | .B54 => ∀ (a b : Op) (s : KState) (q : Pred),
      eval s (a.wp (b.wp q)) = eval (b.exec (a.exec s)) q
  | .B55 => ∀ (o : Op) (s : KState) (q : Pred),
      eval s (o.liveBefore q) = PT.TRUE_KNOWN ↔
        o.enabled s ∧ eval (o.exec s) q = PT.TRUE_KNOWN
  | .B56 => ∀ (a b : Op) (s : KState) (q : Pred),
      eval s (a.liveBefore (b.liveBefore q)) = PT.TRUE_KNOWN ↔
        a.enabled s ∧ b.enabled (a.exec s) ∧ eval (b.exec (a.exec s)) q = PT.TRUE_KNOWN
  | .B57 => ∀ (o : Op) (s : KState), o.execAllowed s → o.requiresAuth = true →
      s.factStatus o.authFact = PT.TRUE_KNOWN
  | .B58 => ∀ (s : KState) (ps : List Pred),
      eval s (conj ps) = PT.TRUE_KNOWN ↔ ∀ p ∈ ps, eval s p = PT.TRUE_KNOWN
  -- Chains.
  | .B59 => ∀ s : KState, execChain [] s = s
  | .B60 => ∀ (o : Op) (t : List Op) (s : KState), execChain (o :: t) s = execChain t (o.exec s)
  | .B61 => ∀ (x y : List Op) (s : KState),
      execChain (x ++ y) s = execChain y (execChain x s)
  | .B62 => ∀ (ops : List Op) (s : KState) (q : Pred),
      eval s (wpChain ops q) = eval (execChain ops s) q
  | .B63 => ∀ (x y : List Op) (s : KState), chainEnabled x s →
      chainEnabled y (execChain x s) → chainEnabled (x ++ y) s
  | .B64 => ∀ (x y : List Op) (s : KState), chainEnabled (x ++ y) s →
      chainEnabled x s ∧ chainEnabled y (execChain x s)
  | .B65 => ∀ (ops : List Op) (s : KState) (f : FactId),
      (∀ o ∈ ops, f ∉ o.produces ∧ f ∉ o.kill) →
      (execChain ops s).factStatus f = s.factStatus f
  | .B66 => ∀ (ops : List Op) (s : KState) (v : VarName), (∀ o ∈ ops, v ∉ o.modifies) →
      (execChain ops s).varValue v = s.varValue v
  | .B67 => ∀ (ops : List Op) (s : KState) (f : FactId), (∀ o ∈ ops, f ∉ o.kill) →
      s.factStatus f = PT.TRUE_KNOWN → (execChain ops s).factStatus f = PT.TRUE_KNOWN
  | .B68 => ∀ (pre post : List Op) (o : Op) (s : KState) (f : FactId), f ∈ o.produces →
      (∀ p ∈ post, f ∉ p.kill) →
      (execChain (pre ++ o :: post) s).factStatus f = PT.TRUE_KNOWN
  | .B69 => ∀ (P : KState → Prop) (ops : List Op), Invariant P ops →
      ∀ s : KState, P s → P (execChain ops s)
  | .B70 => ∀ (f : FactId) (ops : List Op), (∀ o ∈ ops, f ∉ o.kill) →
      Invariant (fun s => s.factStatus f = PT.TRUE_KNOWN) ops
  -- The compiler.
  | .B71 => ∀ (o : Op) (s : KState),
      missingConsume o s = none ↔ ∀ f ∈ o.consumes, s.factStatus f = PT.TRUE_KNOWN
  | .B72 => ∀ (reg : List Op) (o : Op) (s : KState), checkStep reg o s = none ↔ StepOk reg o s
  | .B73 => ∀ (reg ops : List Op) (s : KState), compileGo reg ops s = none ↔ ChainOk reg ops s
  | .B74 => ∀ sc : Scenario, (compile sc).verdict = Verdict.PASS ↔
      ChainOk sc.registry sc.chain sc.init ∧
        eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN
  | .B75 => ∀ (reg ops : List Op) (s : KState), ChainOk reg ops s → chainEnabled ops s
  | .B76 => ∀ (reg : List Op) (o : Op) (t : List Op) (s : KState), ChainOk reg (o :: t) s →
      ∀ f ∈ o.consumes, s.factStatus f = PT.TRUE_KNOWN
  | .B77 => ∀ (reg ops : List Op) (s : KState), ChainOk reg ops s → ChainRegistered reg ops
  | .B78 => ∀ (reg ops : List Op) (s : KState), ChainOk reg ops s → ChainAuthorized ops s
  | .B79 => ∀ sc : Scenario, (compile sc).verdict = Verdict.PASS →
      Criterion.registered.holds sc ∧ Criterion.authorized.holds sc
  -- Identity and epistemics.
  | .B80 => ∀ a : Ty, IsSubtype a a
  | .B81 => ∀ a b c : Ty, IsSubtype a b → IsSubtype b c → IsSubtype a c
  | .B82 => ∀ (w : World) (i : ObjId), legal w (.consume i) ↔ phaseOf w i = Phase.Available
  | .B83 => ∀ (w : World) (i : ObjId), phaseOf w i = Phase.Destroyed →
      ¬ legal w (.create i) ∧ ∀ old : ObjId, ¬ legal w (.recreate old i)
  | .B84 => ∀ (w : World) (old new : ObjId), legal w (.recreate old new) → new ≠ old
  | .B85 => ∀ l₁ l₂ : List Belief,
      mergeBeliefs (l₁ ++ l₂) = PT.join (mergeBeliefs l₁) (mergeBeliefs l₂)
  | .B86 => ∀ (ds : List Uncertainty) (u : Uncertainty), u ≤ propagate ds u
  -- Repair and the concrete registry.
  | .B87 => ∀ (sc : Scenario) (p : RepairPlan), bestRepair sc = some p →
      (compile (p.apply sc)).verdict = Verdict.PASS ∧ p ∈ oneStepRepairs sc ∧
        (∀ q ∈ oneStepRepairs sc, RVec.le p.cost q.cost)
  | .B88 => ∀ a b : ℕ × ℕ, RVec.le a b ∨ RVec.le b a
  | .B89 => registry.length = 17 ∧ stdRegistry.lookup "MEASURE" = some opMEASURE ∧
      stdRegistry.lookup "TELEPORT" = none
  | .B90 => (∀ l : LawId, l.holds) ∧ Fintype.card LawId = 18

/-- Every basis fact is a theorem of the kernel. -/
theorem basis_all_covered : ∀ b : BasisId, b.claim := by
  intro b
  cases b with
  | B01 => exact PT.neg_neg
  | B02 => exact PT.de_morgan_and
  | B03 => exact PT.de_morgan_or
  | B04 => exact PT.and_comm
  | B05 => exact PT.or_comm
  | B06 => exact PT.and_assoc
  | B07 => exact PT.or_assoc
  | B08 => exact PT.and_self
  | B09 => exact PT.or_self
  | B10 => exact PT.and_true_left
  | B11 => exact PT.and_true_right
  | B12 => exact PT.and_eq_true_iff
  | B13 => intro a b; rfl
  | B14 => exact PT.join_comm
  | B15 => exact PT.join_assoc
  | B16 => exact PT.join_self
  | B17 => exact PT.join_unknown_left
  | B18 => rfl
  | B19 => exact (by intro a; cases a <;> rfl : ∀ a : PT, PT.join PT.CONFLICT a = PT.CONFLICT)
  | B20 => exact (by decide : Fintype.card PT = 4)
  | B21 => exact EffectLevel.rank_injective
  | B22 => exact EffectLevel.E0_le
  | B23 => exact EffectLevel.join_E0
  | B24 => exact EffectLevel.join_assoc
  | B25 => exact law008_aggregate_append
  | B26 => exact fun _ _ he => aggregate_le_of_mem he
  | B27 => exact (by decide : Fintype.card EffectLevel = 5)
  | B28 => exact withinBudget_E4
  | B29 => exact withinBudget_append_iff
  | B30 => exact chainEffect_append
  | B31 => exact KState.factStatus_setFact_self
  | B32 => exact fun s _ _ v hne => KState.factStatus_setFact_other s hne v
  | B33 => exact KState.varValue_setFact
  | B34 => exact KState.varValue_clearVar_self
  | B35 => exact fun s _ _ hne => KState.varValue_clearVar_other s hne
  | B36 => exact KState.factStatus_clearVar
  | B37 => exact fun _ _ hf v s => setFacts_notMem hf v s
  | B38 => exact fun _ _ hf v s => setFacts_mem hf v s
  | B39 => exact fun _ _ hw s => clearVars_notMem hw s
  | B40 => exact fun _ _ hw s => clearVars_mem hw s
  | B41 => exact Op.mem_kill_iff
  | B42 => exact fun _ _ h => Op.notMem_produces_of_mem_kill h
  | B43 => exact fun _ _ h => Op.notMem_kill_of_mem_produces h
  | B44 => exact fun o s _ hf => Op.factStatus_exec_produces o s hf
  | B45 => exact fun o s _ hf => Op.factStatus_exec_kill o s hf
  | B46 => exact fun o s _ hp hk => Op.factStatus_exec_untouched o s hp hk
  | B47 => exact fun o s _ hv => Op.varValue_exec_untouched o s hv
  | B48 => exact fun o s _ hv => Op.varValue_exec_modifies o s hv
  | B49 => exact fun o s _ hf => Op.law006_kill_live_fact o s hf
  | B50 => exact fun o s _ hf => Op.law017_invalidate_not_refute o s hf
  | B51 => exact Op.eval_wp
  | B52 => exact Op.law012_wp_sound
  | B53 => exact Op.law012_wp_complete
  | B54 => exact Op.wp_comp
  | B55 => exact Op.eval_liveBefore_eq_true_iff
  | B56 => exact Op.law010_composition_sound
  | B57 => exact fun _ _ h hr => Op.law011_exec_allowed_auth h hr
  | B58 => exact eval_conj_eq_true_iff
  | B59 => exact execChain_nil
  | B60 => exact execChain_cons
  | B61 => exact execChain_append
  | B62 => exact eval_execChain_eq_eval_wpChain
  | B63 => exact fun _ _ _ hx hy => chainEnabled_append hx hy
  | B64 => exact fun _ _ _ h => chainEnabled_of_append h
  | B65 => exact fun ops s _ h => factStatus_execChain_untouched ops s h
  | B66 => exact fun ops s _ h => varValue_execChain_untouched ops s h
  | B67 => exact fun ops s _ hk hs => factStatus_execChain_preserved ops s hk hs
  | B68 => exact fun pre post o s _ hp hk => factStatus_execChain_established pre post o s hp hk
  | B69 => exact fun _ _ h _ hs => invariant_execChain h hs
  | B70 => exact fun _ _ h => invariant_factTrue h
  | B71 => exact missingConsume_eq_none_iff
  | B72 => exact checkStep_eq_none_iff
  | B73 => exact compileGo_eq_none_iff
  | B74 => exact compile_verdict_pass_iff
  | B75 => exact law007_pass_chainEnabled
  | B76 => exact fun reg o t s h _ hf => law005_consume_safety reg o t s h hf
  | B77 => exact fun _ _ _ h => chainRegistered_of_chainOk h
  | B78 => exact fun _ _ _ h => chainAuthorized_of_chainOk h
  | B79 => exact pass_implies_registered_authorized
  | B80 => exact law001_subtype_refl
  | B81 => exact fun _ _ _ h₁ h₂ => law002_subtype_trans h₁ h₂
  | B82 => exact law005_consume_legal_iff
  | B83 => exact fun _ _ h => law004_no_resurrection h
  | B84 => exact fun _ _ _ h => law016_recreate_new_ne_old h
  | B85 => exact mergeBeliefs_append
  | B86 => exact law009_no_overclaim
  | B87 => exact fun _ _ h => law018_repair_sound h
  | B88 => exact RVec.le_total
  | B89 => exact ⟨registry_card, stdRegistry_lookup_measure, stdRegistry_lookup_teleport⟩
  | B90 => exact ⟨lawbook_holds, lawbook_card⟩

/-- The basis has exactly ninety items. -/
theorem basis_card : Fintype.card BasisId = 90 := by decide

end Polymath.OSA4
