import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

/-!
# OSA-4.0 Kernel: four-valued operational semantics

This module defines the operational core of the OSA stack:

* `PT`, a four-valued truth algebra (Belnap style) with negation, conjunction,
  disjunction and implication;
* `KState`, a knowledge state consisting of a fact table and a variable table;
* `Pred`, a small predicate language, and its evaluator `eval`;
* `Op`, an operator with a precondition list and produce / consume / invalidate /
  modify effects, together with its execution function `Op.exec`;
* `Op.wp`, a syntactic weakest-precondition transformer, proved sound **and**
  complete: `eval s (o.wp q) = eval (o.exec s) q`.

The frame theorems (`factStatus_exec_untouched`, `varValue_exec_untouched`), the
liveness theorem (`law006_kill_live_fact`) and the composition theorem
(`law010_composition_sound`) are the semantic facts the rest of the project
depends on.
-/

namespace Polymath.OSA4

/-- Identifier of a fact. -/
abbrev FactId := String
/-- Identifier of a state variable. -/
abbrev VarName := String

/-! ## Four-valued truth -/

/-- Four-valued truth: known-true, known-false, unknown, and conflicting. -/
inductive PT
  | TRUE_KNOWN | FALSE_KNOWN | UNKNOWN | CONFLICT
  deriving DecidableEq, Repr, Fintype, Inhabited

namespace PT

/-- Negation: swaps the two known values and fixes `UNKNOWN` and `CONFLICT`. -/
def neg : PT → PT
  | TRUE_KNOWN => FALSE_KNOWN
  | FALSE_KNOWN => TRUE_KNOWN
  | UNKNOWN => UNKNOWN
  | CONFLICT => CONFLICT

/-- Conjunction: the meet in the truth order `FALSE ≤ {UNKNOWN, CONFLICT} ≤ TRUE`. -/
def and : PT → PT → PT
  | FALSE_KNOWN, _ => FALSE_KNOWN
  | _, FALSE_KNOWN => FALSE_KNOWN
  | TRUE_KNOWN, b => b
  | a, TRUE_KNOWN => a
  | UNKNOWN, UNKNOWN => UNKNOWN
  | CONFLICT, CONFLICT => CONFLICT
  | UNKNOWN, CONFLICT => FALSE_KNOWN
  | CONFLICT, UNKNOWN => FALSE_KNOWN

/-- Disjunction: the join in the truth order. -/
def or : PT → PT → PT
  | TRUE_KNOWN, _ => TRUE_KNOWN
  | _, TRUE_KNOWN => TRUE_KNOWN
  | FALSE_KNOWN, b => b
  | a, FALSE_KNOWN => a
  | UNKNOWN, UNKNOWN => UNKNOWN
  | CONFLICT, CONFLICT => CONFLICT
  | UNKNOWN, CONFLICT => TRUE_KNOWN
  | CONFLICT, UNKNOWN => TRUE_KNOWN

/-- Material implication. -/
def imp (a b : PT) : PT := or (neg a) b

@[simp] theorem neg_neg (a : PT) : neg (neg a) = a := by cases a <;> rfl

theorem de_morgan_and (a b : PT) : neg (and a b) = or (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem de_morgan_or (a b : PT) : neg (or a b) = and (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem and_comm (a b : PT) : and a b = and b a := by cases a <;> cases b <;> rfl
theorem or_comm (a b : PT) : or a b = or b a := by cases a <;> cases b <;> rfl
theorem and_assoc (a b c : PT) : and (and a b) c = and a (and b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem or_assoc (a b c : PT) : or (or a b) c = or a (or b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] theorem and_self (a : PT) : and a a = a := by cases a <;> rfl
@[simp] theorem or_self (a : PT) : or a a = a := by cases a <;> rfl
@[simp] theorem and_true_left (a : PT) : and TRUE_KNOWN a = a := by cases a <;> rfl
@[simp] theorem and_true_right (a : PT) : and a TRUE_KNOWN = a := by cases a <;> rfl

/-- Conjunction is known-true exactly when both conjuncts are. -/
theorem and_eq_true_iff (a b : PT) :
    and a b = TRUE_KNOWN ↔ a = TRUE_KNOWN ∧ b = TRUE_KNOWN := by
  cases a <;> cases b <;> simp [and]

theorem or_eq_true_of_left {a : PT} (b : PT) (h : a = TRUE_KNOWN) : or a b = TRUE_KNOWN := by
  subst h; rfl

/-- The *information* join: the least upper bound in the knowledge order
`UNKNOWN ≤ {TRUE, FALSE} ≤ CONFLICT`.  This is how belief states merge. -/
def join : PT → PT → PT
  | UNKNOWN, b => b
  | a, UNKNOWN => a
  | CONFLICT, _ => CONFLICT
  | _, CONFLICT => CONFLICT
  | TRUE_KNOWN, TRUE_KNOWN => TRUE_KNOWN
  | FALSE_KNOWN, FALSE_KNOWN => FALSE_KNOWN
  | TRUE_KNOWN, FALSE_KNOWN => CONFLICT
  | FALSE_KNOWN, TRUE_KNOWN => CONFLICT

theorem join_comm (a b : PT) : join a b = join b a := by cases a <;> cases b <;> rfl
theorem join_assoc (a b c : PT) : join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] theorem join_self (a : PT) : join a a = a := by cases a <;> rfl
@[simp] theorem join_unknown_left (a : PT) : join UNKNOWN a = a := by cases a <;> rfl
@[simp] theorem join_unknown_right (a : PT) : join a UNKNOWN = a := by cases a <;> rfl

end PT

/-- A belief value is a four-valued truth value; merging beliefs is `PT.join`. -/
abbrev Belief := PT

/-! ## States -/

/-- A knowledge state: a fact table and a variable table. -/
structure KState where
  facts : List (FactId × PT)
  vars : List (VarName × Option ℕ)
  deriving Repr, Inhabited

namespace KState

/-- Status of a fact; facts absent from the table are `UNKNOWN`. -/
def factStatus (s : KState) (f : FactId) : PT :=
  match s.facts.find? (fun p => p.1 = f) with
  | some p => p.2
  | none => .UNKNOWN

/-- Value of a variable; variables absent from the table are unset. -/
def varValue (s : KState) (v : VarName) : Option ℕ :=
  match s.vars.find? (fun p => p.1 = v) with
  | some p => p.2
  | none => none

/-- Record a new status for a fact. -/
def setFact (s : KState) (f : FactId) (v : PT) : KState := ⟨(f, v) :: s.facts, s.vars⟩

/-- Record a new value for a variable. -/
def setVar (s : KState) (v : VarName) (n : ℕ) : KState := ⟨s.facts, (v, some n) :: s.vars⟩

/-- Unset a variable. -/
def clearVar (s : KState) (v : VarName) : KState := ⟨s.facts, (v, none) :: s.vars⟩

@[simp] theorem factStatus_setFact_self (s : KState) (f : FactId) (v : PT) :
    (s.setFact f v).factStatus f = v := by
  simp [factStatus, setFact]

theorem factStatus_setFact_other (s : KState) {f g : FactId} (hne : g ≠ f) (v : PT) :
    (s.setFact f v).factStatus g = s.factStatus g := by
  simp [factStatus, setFact, Ne.symm hne]

@[simp] theorem varValue_setFact (s : KState) (f : FactId) (v : PT) (w : VarName) :
    (s.setFact f v).varValue w = s.varValue w := rfl

@[simp] theorem varValue_clearVar_self (s : KState) (v : VarName) :
    (s.clearVar v).varValue v = none := by
  simp [varValue, clearVar]

theorem varValue_clearVar_other (s : KState) {v w : VarName} (hne : w ≠ v) :
    (s.clearVar v).varValue w = s.varValue w := by
  simp [varValue, clearVar, Ne.symm hne]

@[simp] theorem factStatus_clearVar (s : KState) (v : VarName) (f : FactId) :
    (s.clearVar v).factStatus f = s.factStatus f := rfl

end KState

/-- Set every fact in `fs` to the value `v`. -/
def setFacts (fs : List FactId) (v : PT) (s : KState) : KState :=
  fs.foldl (fun st f => st.setFact f v) s

/-- Unset every variable in `vs`. -/
def clearVars (vs : List VarName) (s : KState) : KState :=
  vs.foldl (fun st w => st.clearVar w) s

theorem setFacts_notMem {fs : List FactId} {f : FactId} (hf : f ∉ fs) (v : PT) (s : KState) :
    (setFacts fs v s).factStatus f = s.factStatus f := by
  induction fs generalizing s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at hf
    rw [setFacts, List.foldl_cons, ← setFacts, ih hf.2, KState.factStatus_setFact_other _ hf.1]

theorem setFacts_mem {fs : List FactId} {f : FactId} (hf : f ∈ fs) (v : PT) (s : KState) :
    (setFacts fs v s).factStatus f = v := by
  induction fs generalizing s with
  | nil => cases hf
  | cons a t ih =>
    rw [setFacts, List.foldl_cons, ← setFacts]
    by_cases ht : f ∈ t
    · exact ih ht _
    · rcases List.mem_cons.1 hf with rfl | h
      · rw [setFacts_notMem ht, KState.factStatus_setFact_self]
      · exact absurd h ht

@[simp] theorem setFacts_varValue (fs : List FactId) (v : PT) (s : KState) (w : VarName) :
    (setFacts fs v s).varValue w = s.varValue w := by
  induction fs generalizing s with
  | nil => rfl
  | cons a t ih => rw [setFacts, List.foldl_cons, ← setFacts, ih]; rfl

@[simp] theorem clearVars_factStatus (vs : List VarName) (s : KState) (f : FactId) :
    (clearVars vs s).factStatus f = s.factStatus f := by
  induction vs generalizing s with
  | nil => rfl
  | cons a t ih => rw [clearVars, List.foldl_cons, ← clearVars, ih]; rfl

theorem clearVars_notMem {vs : List VarName} {w : VarName} (hw : w ∉ vs) (s : KState) :
    (clearVars vs s).varValue w = s.varValue w := by
  induction vs generalizing s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at hw
    rw [clearVars, List.foldl_cons, ← clearVars, ih hw.2, KState.varValue_clearVar_other _ hw.1]

theorem clearVars_mem {vs : List VarName} {w : VarName} (hw : w ∈ vs) (s : KState) :
    (clearVars vs s).varValue w = none := by
  induction vs generalizing s with
  | nil => cases hw
  | cons a t ih =>
    rw [clearVars, List.foldl_cons, ← clearVars]
    by_cases ht : w ∈ t
    · exact ih ht _
    · rcases List.mem_cons.1 hw with rfl | h
      · rw [clearVars_notMem ht, KState.varValue_clearVar_self]
      · exact absurd h ht

/-! ## The predicate language -/

/-- The predicate language interpreted over `KState`. -/
inductive Pred
  | factExists (f : FactId)
  | pnot (p : Pred)
  | pand (p q : Pred)
  | por (p q : Pred)
  | pimp (p q : Pred)
  | gte (v : VarName) (n : ℕ)
  | peq (v : VarName) (n : ℕ)
  | ctrue
  | cfalse
  | cunknown
  deriving DecidableEq, Repr, Inhabited

/-- Four-valued evaluation of a predicate in a state. -/
def eval (s : KState) : Pred → PT
  | .factExists f => s.factStatus f
  | .pnot p => (eval s p).neg
  | .pand p q => PT.and (eval s p) (eval s q)
  | .por p q => PT.or (eval s p) (eval s q)
  | .pimp p q => PT.imp (eval s p) (eval s q)
  | .gte v n =>
      match s.varValue v with
      | none => .UNKNOWN
      | some m => if n ≤ m then .TRUE_KNOWN else .FALSE_KNOWN
  | .peq v n =>
      match s.varValue v with
      | none => .UNKNOWN
      | some m => if m = n then .TRUE_KNOWN else .FALSE_KNOWN
  | .ctrue => .TRUE_KNOWN
  | .cfalse => .FALSE_KNOWN
  | .cunknown => .UNKNOWN

/-- Conjunction of a list of predicates. -/
def conj : List Pred → Pred
  | [] => .ctrue
  | p :: t => .pand p (conj t)

theorem eval_conj_eq_true_iff (s : KState) (ps : List Pred) :
    eval s (conj ps) = .TRUE_KNOWN ↔ ∀ p ∈ ps, eval s p = .TRUE_KNOWN := by
  induction ps with
  | nil => simp [conj, eval]
  | cons p t ih =>
    simp only [conj, eval, PT.and_eq_true_iff, List.mem_cons, forall_eq_or_imp, ih]

/-! ## Effect levels -/

/-- Five levels of side effect, from inert (`E0`) to irreversible (`E4`). -/
inductive EffectLevel
  | E0 | E1 | E2 | E3 | E4
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Numerical rank of an effect level. -/
def EffectLevel.rank : EffectLevel → ℕ
  | E0 => 0 | E1 => 1 | E2 => 2 | E3 => 3 | E4 => 4

theorem EffectLevel.rank_injective : Function.Injective EffectLevel.rank := by
  intro a b h; cases a <;> cases b <;> simp [EffectLevel.rank] at h ⊢

instance : LinearOrder EffectLevel :=
  LinearOrder.lift' EffectLevel.rank EffectLevel.rank_injective

/-- The effect level of a composite is the maximum of its parts. -/
def EffectLevel.join (a b : EffectLevel) : EffectLevel := max a b

/-- Aggregate effect level of a list of effects. -/
def aggregate : List EffectLevel → EffectLevel
  | [] => .E0
  | e :: t => EffectLevel.join e (aggregate t)

theorem EffectLevel.le_iff_rank_le (a b : EffectLevel) : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

@[simp] theorem EffectLevel.E0_le (a : EffectLevel) : EffectLevel.E0 ≤ a := by
  cases a <;> simp [EffectLevel.le_iff_rank_le, EffectLevel.rank]

@[simp] theorem EffectLevel.join_E0 (a : EffectLevel) : EffectLevel.join a EffectLevel.E0 = a :=
  max_eq_left (EffectLevel.E0_le a)

theorem EffectLevel.join_assoc (a b c : EffectLevel) :
    EffectLevel.join (EffectLevel.join a b) c = EffectLevel.join a (EffectLevel.join b c) :=
  max_assoc a b c

/-- LAW-008 (effect monotonicity): aggregation carries concatenation of effect
lists to the join of effect levels. -/
theorem law008_aggregate_append (l₁ l₂ : List EffectLevel) :
    aggregate (l₁ ++ l₂) = EffectLevel.join (aggregate l₁) (aggregate l₂) := by
  induction l₁ with
  | nil =>
    show aggregate l₂ = EffectLevel.join EffectLevel.E0 (aggregate l₂)
    exact (max_eq_right (EffectLevel.E0_le _)).symm
  | cons e t ih => simp [aggregate, ih, EffectLevel.join_assoc]

theorem aggregate_le_of_mem {l : List EffectLevel} {e : EffectLevel} (he : e ∈ l) :
    e ≤ aggregate l := by
  induction l with
  | nil => cases he
  | cons a t ih =>
    rcases List.mem_cons.1 he with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-! ## Operators -/

/-- An operator: preconditions plus produce / consume / invalidate / modify effects. -/
structure Op where
  name : String
  requires : List Pred
  produces : List FactId
  consumes : List FactId
  invalidates : List FactId
  modifies : List VarName
  effect : EffectLevel
  requiresAuth : Bool
  deriving Repr, Inhabited, DecidableEq

namespace Op

/-- The facts an operator destroys: everything consumed or invalidated and not
re-produced. -/
def kill (o : Op) : List FactId :=
  (o.consumes ++ o.invalidates).filter (fun f => !o.produces.contains f)

theorem mem_kill_iff (o : Op) (f : FactId) :
    f ∈ o.kill ↔ (f ∈ o.consumes ∨ f ∈ o.invalidates) ∧ f ∉ o.produces := by
  simp only [kill, List.mem_filter, List.mem_append, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]

theorem notMem_produces_of_mem_kill {o : Op} {f : FactId} (h : f ∈ o.kill) :
    f ∉ o.produces := ((o.mem_kill_iff f).1 h).2

theorem notMem_kill_of_mem_produces {o : Op} {f : FactId} (h : f ∈ o.produces) :
    f ∉ o.kill := fun hk => notMem_produces_of_mem_kill hk h

/-- Executing an operator: assert everything produced, unset the modified
variables, then reset the destroyed facts to `UNKNOWN`. -/
def exec (o : Op) (s : KState) : KState :=
  setFacts o.kill .UNKNOWN (clearVars o.modifies (setFacts o.produces .TRUE_KNOWN s))

/-- An operator is enabled when all of its preconditions evaluate to known-true. -/
def enabled (o : Op) (s : KState) : Prop := ∀ p ∈ o.requires, eval s p = .TRUE_KNOWN

instance (o : Op) (s : KState) : Decidable (o.enabled s) := by
  unfold enabled; infer_instance

theorem factStatus_exec_produces (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.produces) :
    (o.exec s).factStatus f = .TRUE_KNOWN := by
  rw [exec, setFacts_notMem (notMem_kill_of_mem_produces hf), clearVars_factStatus,
    setFacts_mem hf]

theorem factStatus_exec_kill (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.kill) :
    (o.exec s).factStatus f = .UNKNOWN := by
  rw [exec, setFacts_mem hf]

/-- LAW-003 (state conservation, facts): facts neither produced nor destroyed are
preserved by execution. -/
theorem factStatus_exec_untouched (o : Op) (s : KState) {f : FactId}
    (hp : f ∉ o.produces) (hk : f ∉ o.kill) :
    (o.exec s).factStatus f = s.factStatus f := by
  rw [exec, setFacts_notMem hk, clearVars_factStatus, setFacts_notMem hp]

/-- LAW-003 (state conservation, variables): variables not modified are preserved. -/
theorem varValue_exec_untouched (o : Op) (s : KState) {v : VarName} (hv : v ∉ o.modifies) :
    (o.exec s).varValue v = s.varValue v := by
  rw [exec, setFacts_varValue, clearVars_notMem hv, setFacts_varValue]

theorem varValue_exec_modifies (o : Op) (s : KState) {v : VarName} (hv : v ∈ o.modifies) :
    (o.exec s).varValue v = none := by
  rw [exec, setFacts_varValue, clearVars_mem hv]

/-- LAW-006 (destroy/predicate liveness): after an operator destroys a fact, that
fact is no longer known-true. -/
theorem law006_kill_live_fact (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.kill) :
    eval (o.exec s) (.factExists f) ≠ .TRUE_KNOWN := by
  rw [eval, factStatus_exec_kill o s hf]; decide

/-- LAW-017 (invalidation is not refutation): destroying a fact does not make its
negation known-true either. -/
theorem law017_invalidate_not_refute (o : Op) (s : KState) {f : FactId} (hf : f ∈ o.kill) :
    eval (o.exec s) (.pnot (.factExists f)) ≠ .TRUE_KNOWN := by
  rw [eval, eval, factStatus_exec_kill o s hf]; decide

/-! ### Weakest preconditions -/

/-- Syntactic weakest-precondition transformer. -/
def wp (o : Op) : Pred → Pred
  | .factExists f =>
      if f ∈ o.produces then .ctrue else if f ∈ o.kill then .cunknown else .factExists f
  | .pnot p => .pnot (o.wp p)
  | .pand p q => .pand (o.wp p) (o.wp q)
  | .por p q => .por (o.wp p) (o.wp q)
  | .pimp p q => .pimp (o.wp p) (o.wp q)
  | .gte v n => if v ∈ o.modifies then .cunknown else .gte v n
  | .peq v n => if v ∈ o.modifies then .cunknown else .peq v n
  | .ctrue => .ctrue
  | .cfalse => .cfalse
  | .cunknown => .cunknown

/-- The transformer computes exactly the post-state evaluation: `wp` is both sound
and complete for the four-valued semantics. -/
theorem eval_wp (o : Op) (s : KState) (q : Pred) : eval s (o.wp q) = eval (o.exec s) q := by
  induction q with
  | factExists f =>
    by_cases hp : f ∈ o.produces
    · simp [wp, hp, eval, factStatus_exec_produces o s hp]
    · by_cases hk : f ∈ o.kill
      · simp [wp, hp, hk, eval, factStatus_exec_kill o s hk]
      · simp [wp, hp, hk, eval, factStatus_exec_untouched o s hp hk]
  | pnot p ih => simp [wp, eval, ih]
  | pand p q ihp ihq => simp [wp, eval, ihp, ihq]
  | por p q ihp ihq => simp [wp, eval, ihp, ihq]
  | pimp p q ihp ihq => simp [wp, eval, ihp, ihq]
  | gte v n =>
    by_cases hv : v ∈ o.modifies
    · simp [wp, hv, eval, varValue_exec_modifies o s hv]
    · simp [wp, hv, eval, varValue_exec_untouched o s hv]
  | peq v n =>
    by_cases hv : v ∈ o.modifies
    · simp [wp, hv, eval, varValue_exec_modifies o s hv]
    · simp [wp, hv, eval, varValue_exec_untouched o s hv]
  | ctrue => rfl
  | cfalse => rfl
  | cunknown => rfl

/-- LAW-012 (soundness half). -/
theorem law012_wp_sound (o : Op) (s : KState) (q : Pred)
    (h : eval s (o.wp q) = .TRUE_KNOWN) : eval (o.exec s) q = .TRUE_KNOWN := by
  rwa [eval_wp] at h

/-- LAW-012 (completeness half). -/
theorem law012_wp_complete (o : Op) (s : KState) (q : Pred)
    (h : eval (o.exec s) q = .TRUE_KNOWN) : eval s (o.wp q) = .TRUE_KNOWN := by
  rwa [eval_wp]

theorem wp_comp (a b : Op) (s : KState) (q : Pred) :
    eval s (a.wp (b.wp q)) = eval (b.exec (a.exec s)) q := by
  rw [eval_wp, eval_wp]

/-- The precondition that must hold before `o` for `q` to hold afterwards. -/
def liveBefore (o : Op) (q : Pred) : Pred := .pand (conj o.requires) (o.wp q)

theorem eval_liveBefore_eq_true_iff (o : Op) (s : KState) (q : Pred) :
    eval s (o.liveBefore q) = .TRUE_KNOWN ↔
      o.enabled s ∧ eval (o.exec s) q = .TRUE_KNOWN := by
  simp only [liveBefore, eval, PT.and_eq_true_iff, eval_conj_eq_true_iff, eval_wp, enabled]

/-- LAW-010 (composition soundness): the two-step live precondition decomposes
exactly into "first enabled, then enabled, then goal". -/
theorem law010_composition_sound (a b : Op) (s : KState) (q : Pred) :
    eval s (a.liveBefore (b.liveBefore q)) = .TRUE_KNOWN ↔
      a.enabled s ∧ b.enabled (a.exec s) ∧ eval (b.exec (a.exec s)) q = .TRUE_KNOWN := by
  rw [eval_liveBefore_eq_true_iff, eval_liveBefore_eq_true_iff]

/-! ### Authorization -/

/-- The fact recording that an operator has been authorized. -/
def authFact (o : Op) : FactId := "AUTH:" ++ o.name

/-- Execution is allowed when the operator is enabled and, if it needs
authorization, that authorization is known to have been granted. -/
def execAllowed (o : Op) (s : KState) : Prop :=
  o.enabled s ∧ (o.requiresAuth = true → s.factStatus o.authFact = .TRUE_KNOWN)

/-- LAW-011 (effect authorization): an allowed operator that requires
authorization has that authorization known-true. -/
theorem law011_exec_allowed_auth {o : Op} {s : KState} (h : o.execAllowed s)
    (hr : o.requiresAuth = true) : s.factStatus o.authFact = .TRUE_KNOWN := h.2 hr

end Op

/-! ## Chains -/

/-- Execute a list of operators left to right. -/
def execChain : List Op → KState → KState
  | [], s => s
  | o :: t, s => execChain t (o.exec s)

@[simp] theorem execChain_nil (s : KState) : execChain [] s = s := rfl
@[simp] theorem execChain_cons (o : Op) (t : List Op) (s : KState) :
    execChain (o :: t) s = execChain t (o.exec s) := rfl

theorem execChain_append (x y : List Op) (s : KState) :
    execChain (x ++ y) s = execChain y (execChain x s) := by
  induction x generalizing s with
  | nil => rfl
  | cons o t ih => simp [ih]

/-- Weakest precondition of a chain. -/
def wpChain : List Op → Pred → Pred
  | [], q => q
  | o :: t, q => o.wp (wpChain t q)

@[simp] theorem wpChain_nil (q : Pred) : wpChain [] q = q := rfl
@[simp] theorem wpChain_cons (o : Op) (t : List Op) (q : Pred) :
    wpChain (o :: t) q = o.wp (wpChain t q) := rfl

/-- The chain-level weakest precondition is exact. -/
theorem eval_execChain_eq_eval_wpChain (ops : List Op) (s : KState) (q : Pred) :
    eval s (wpChain ops q) = eval (execChain ops s) q := by
  induction ops generalizing s with
  | nil => rfl
  | cons o t ih => rw [wpChain_cons, Op.eval_wp, execChain_cons, ih]

/-- Every operator of the chain is enabled when it is reached. -/
def chainEnabled : List Op → KState → Prop
  | [], _ => True
  | o :: t, s => o.enabled s ∧ chainEnabled t (o.exec s)

instance decidableChainEnabled : ∀ (ops : List Op) (s : KState), Decidable (chainEnabled ops s)
  | [], _ => by unfold chainEnabled; infer_instance
  | o :: t, s => by
      have := decidableChainEnabled t (o.exec s)
      unfold chainEnabled
      infer_instance

@[simp] theorem chainEnabled_nil (s : KState) : chainEnabled [] s := trivial

@[simp] theorem chainEnabled_cons (o : Op) (t : List Op) (s : KState) :
    chainEnabled (o :: t) s ↔ o.enabled s ∧ chainEnabled t (o.exec s) := Iff.rfl

theorem chainEnabled_append {x y : List Op} {s : KState}
    (hx : chainEnabled x s) (hy : chainEnabled y (execChain x s)) :
    chainEnabled (x ++ y) s := by
  induction x generalizing s with
  | nil => simpa using hy
  | cons o t ih =>
    obtain ⟨h1, h2⟩ := hx
    exact ⟨h1, ih h2 (by simpa using hy)⟩

theorem chainEnabled_of_append {x y : List Op} {s : KState}
    (h : chainEnabled (x ++ y) s) : chainEnabled x s ∧ chainEnabled y (execChain x s) := by
  induction x generalizing s with
  | nil => exact ⟨trivial, by simpa using h⟩
  | cons o t ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ha, hb⟩ := ih h2
    exact ⟨⟨h1, ha⟩, by simpa using hb⟩

end Polymath.OSA4
