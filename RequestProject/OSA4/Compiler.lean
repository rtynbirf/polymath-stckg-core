import RequestProject.OSA4.Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

/-!
# OSA-4.0 Compiler: static checking of operator chains

A `Scenario` bundles a registry of known operators, an initial state, a chain to
execute and a goal predicate.  `compile` walks the chain, checking at each step:

1. the operator is in the registry (`E_UNKNOWN_OPERATOR`);
2. every consumed fact is currently available (`E_INVARIANT_VIOLATION`, this is
   what catches double consumption);
3. the operator's preconditions hold (`E_LIVENESS_VIOLATION`, this is what
   catches "destroy then use");
4. authorization is present when required (`E_AUTH_DENIED` if explicitly refused,
   `E_AUTH_MISSING` — a repairable situation — if merely unknown).

If the walk succeeds, the verdict is read off the goal in the final state:
known-true gives `PASS`, known-false gives `REJECT`, and the two non-classical
values give `UNDECIDABLE`.

The main result is `compile_verdict_pass_iff`: the compiler answers `PASS`
exactly when the chain is well-formed *and* actually establishes the goal.
-/

namespace Polymath.OSA4

/-- The four possible outcomes of compilation. -/
inductive Verdict
  | PASS | REJECT | REPAIR | UNDECIDABLE
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Static errors the compiler can report. -/
inductive CompileError
  | E_UNKNOWN_OPERATOR (op : String)
  | E_INVARIANT_VIOLATION (op : String) (fact : FactId)
  | E_LIVENESS_VIOLATION (op : String)
  | E_AUTH_DENIED (op : String)
  | E_AUTH_MISSING (op : String)
  deriving DecidableEq, Repr, Inhabited

/-- A missing authorization is repairable; every other error is fatal. -/
def CompileError.verdict : CompileError → Verdict
  | .E_AUTH_MISSING _ => .REPAIR
  | _ => .REJECT

/-- A compilation problem. -/
structure Scenario where
  registry : List Op
  init : KState
  chain : List Op
  goal : Pred

/-- The result of compiling a scenario. -/
structure CompileResult where
  verdict : Verdict
  errors : List CompileError
  deriving Repr, DecidableEq

/-- The first consumed fact that is not currently available, if any. -/
def missingConsume (o : Op) (s : KState) : Option FactId :=
  o.consumes.find? (fun f => decide (s.factStatus f ≠ PT.TRUE_KNOWN))

theorem missingConsume_eq_none_iff (o : Op) (s : KState) :
    missingConsume o s = none ↔ ∀ f ∈ o.consumes, s.factStatus f = PT.TRUE_KNOWN := by
  simp [missingConsume, List.find?_eq_none]

/-- One step of the static check: `none` means the step is admissible. -/
def checkStep (reg : List Op) (o : Op) (s : KState) : Option CompileError :=
  if o.name ∉ reg.map (·.name) then
    some (.E_UNKNOWN_OPERATOR o.name)
  else if (missingConsume o s).isSome then
    some (.E_INVARIANT_VIOLATION o.name ((missingConsume o s).getD ""))
  else if ¬ o.enabled s then
    some (.E_LIVENESS_VIOLATION o.name)
  else if o.requiresAuth = true ∧ s.factStatus o.authFact = PT.FALSE_KNOWN then
    some (.E_AUTH_DENIED o.name)
  else if o.requiresAuth = true ∧ s.factStatus o.authFact ≠ PT.TRUE_KNOWN then
    some (.E_AUTH_MISSING o.name)
  else
    none

/-- Walk the whole chain, reporting the first error. -/
def compileGo (reg : List Op) : List Op → KState → Option CompileError
  | [], _ => none
  | o :: t, s =>
      match checkStep reg o s with
      | some e => some e
      | none => compileGo reg t (o.exec s)

/-- Compile a scenario to a verdict. -/
def compile (sc : Scenario) : CompileResult :=
  match compileGo sc.registry sc.chain sc.init with
  | some e => ⟨e.verdict, [e]⟩
  | none =>
      match eval (execChain sc.chain sc.init) sc.goal with
      | .TRUE_KNOWN => ⟨.PASS, []⟩
      | .FALSE_KNOWN => ⟨.REJECT, []⟩
      | _ => ⟨.UNDECIDABLE, []⟩

/-! ## Well-formedness -/

/-- The declarative counterpart of the compiler's per-step checks. -/
def StepOk (reg : List Op) (o : Op) (s : KState) : Prop :=
  o.name ∈ reg.map (·.name) ∧
  (∀ f ∈ o.consumes, s.factStatus f = PT.TRUE_KNOWN) ∧
  o.enabled s ∧
  (o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN)

/-- A chain is well-formed when every step passes its checks in the state it is
reached in. -/
def ChainOk (reg : List Op) : List Op → KState → Prop
  | [], _ => True
  | o :: t, s => StepOk reg o s ∧ ChainOk reg t (o.exec s)

@[simp] theorem ChainOk_nil (reg : List Op) (s : KState) : ChainOk reg [] s := trivial

@[simp] theorem ChainOk_cons (reg : List Op) (o : Op) (t : List Op) (s : KState) :
    ChainOk reg (o :: t) s ↔ StepOk reg o s ∧ ChainOk reg t (o.exec s) := Iff.rfl

theorem checkStep_eq_none_iff (reg : List Op) (o : Op) (s : KState) :
    checkStep reg o s = none ↔ StepOk reg o s := by
  constructor
  · intro h
    rw [checkStep] at h
    have h1 : o.name ∈ List.map (fun x : Op => x.name) reg := by
      by_contra hx; rw [if_pos hx] at h; cases h
    rw [if_neg (not_not_intro h1)] at h
    have h2 : missingConsume o s = none := by
      cases hm : missingConsume o s with
      | none => rfl
      | some f => rw [hm] at h; simp at h
    rw [if_neg (by rw [h2]; simp)] at h
    have h3 : o.enabled s := by
      by_contra hx; rw [if_pos hx] at h; cases h
    rw [if_neg (not_not_intro h3)] at h
    have h4 : o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN := by
      intro ha
      by_contra hT
      by_cases hF : s.factStatus o.authFact = PT.FALSE_KNOWN
      · rw [if_pos (And.intro ha hF)] at h; cases h
      · rw [if_neg (by tauto), if_pos (And.intro ha hT)] at h; cases h
    exact ⟨h1, (missingConsume_eq_none_iff o s).1 h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hmc : missingConsume o s = none := (missingConsume_eq_none_iff o s).2 h2
    have hF : ¬ (o.requiresAuth = true ∧ s.factStatus o.authFact = PT.FALSE_KNOWN) := by
      rintro ⟨ha, hf⟩; rw [h4 ha] at hf; exact absurd hf (by decide)
    have hT : ¬ (o.requiresAuth = true ∧ s.factStatus o.authFact ≠ PT.TRUE_KNOWN) := by
      rintro ⟨ha, hf⟩; exact hf (h4 ha)
    rw [checkStep, if_neg (not_not_intro h1), if_neg (by rw [hmc]; simp),
      if_neg (not_not_intro h3), if_neg hF, if_neg hT]

/-- The compiler accepts a chain exactly when the chain is well-formed. -/
theorem compileGo_eq_none_iff (reg : List Op) (ops : List Op) (s : KState) :
    compileGo reg ops s = none ↔ ChainOk reg ops s := by
  induction ops generalizing s with
  | nil => simp [compileGo]
  | cons o t ih =>
    rw [ChainOk_cons, compileGo]
    cases hstep : checkStep reg o s with
    | some e =>
      have : ¬ StepOk reg o s := fun h =>
        by rw [(checkStep_eq_none_iff reg o s).2 h] at hstep; cases hstep
      simp [this]
    | none =>
      have : StepOk reg o s := (checkStep_eq_none_iff reg o s).1 hstep
      simp [this, ih]

/-- `PASS` is exactly "well-formed chain that establishes the goal". -/
theorem compile_verdict_pass_iff (sc : Scenario) :
    (compile sc).verdict = .PASS ↔
      ChainOk sc.registry sc.chain sc.init ∧
      eval (execChain sc.chain sc.init) sc.goal = PT.TRUE_KNOWN := by
  rw [compile]
  cases hgo : compileGo sc.registry sc.chain sc.init with
  | some e =>
    have hne : ¬ ChainOk sc.registry sc.chain sc.init := fun h => by
      rw [(compileGo_eq_none_iff sc.registry sc.chain sc.init).2 h] at hgo; cases hgo
    cases e <;> simp [CompileError.verdict, hne]
  | none =>
    have hok : ChainOk sc.registry sc.chain sc.init :=
      (compileGo_eq_none_iff sc.registry sc.chain sc.init).1 hgo
    cases hc : eval (execChain sc.chain sc.init) sc.goal <;> simp [hok]

/-- LAW-007 (liveness soundness): if the compiler passes a chain, then every
operator of the chain is enabled at the moment it runs. -/
theorem law007_pass_chainEnabled (reg : List Op) (ops : List Op) (s : KState)
    (h : ChainOk reg ops s) : chainEnabled ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons o t ih => exact ⟨h.1.2.2.1, ih _ h.2⟩

/-- A well-formed chain never consumes an unavailable fact (LAW-005, consume
safety). -/
theorem law005_consume_safety (reg : List Op) (o : Op) (t : List Op) (s : KState)
    (h : ChainOk reg (o :: t) s) {f : FactId} (hf : f ∈ o.consumes) :
    s.factStatus f = PT.TRUE_KNOWN := h.1.2.1 f hf

end Polymath.OSA4
