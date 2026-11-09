import RequestProject.OSA4.Lawbook

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

/-!
# OSA-5.0 Repair: bounded multistep repair search

OSA-4.0 can only repair a failing chain by inserting a single operator.  OSA-5.0
searches for a *sequence* of operators.

The search is a bounded depth-first exploration of the registry, total by
construction (it recurses on a fuel argument).  The two central theorems are

* `searchRepair_sound` — anything the search returns is a genuine repair: every
  operator comes from the registry, each step is admissible in the state it is
  reached in, the goal holds afterwards, and the plan is no longer than the fuel;
* `searchRepair_complete` — if any such repair exists within the fuel bound, the
  search finds one.

Together (`searchRepair_isSome_iff`) they characterise the search exactly.
`minRepair` then performs iterative deepening and returns a *shortest* repair
(`minRepair_length_le`), and `repair_compiles_pass` closes the loop by feeding a
discovered repair back through the OSA-4.0 compiler.

The predicate `chainPred` gives the same information symbolically: it is a single
`Pred` whose truth in a state is equivalent to "this chain runs and achieves the
goal" (`chainPred_eq_true_iff`).
-/

namespace Polymath.OSA5

open Polymath.OSA4

/-! ## Admissibility -/

/-- A step is admissible when its preconditions hold, its consumed facts are
available, and its authorization (if any) has been granted. -/
def StepAdmissible (o : Op) (s : KState) : Prop :=
  o.enabled s ∧
  (∀ f ∈ o.consumes, s.factStatus f = PT.TRUE_KNOWN) ∧
  (o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN)

instance (o : Op) (s : KState) : Decidable (StepAdmissible o s) := by
  unfold StepAdmissible; infer_instance

/-- Every step of the chain is admissible when it is reached. -/
def ChainAdmissible : List Op → KState → Prop
  | [], _ => True
  | o :: t, s => StepAdmissible o s ∧ ChainAdmissible t (o.exec s)

@[simp] theorem ChainAdmissible_nil (s : KState) : ChainAdmissible [] s := trivial

@[simp] theorem ChainAdmissible_cons (o : Op) (t : List Op) (s : KState) :
    ChainAdmissible (o :: t) s ↔ StepAdmissible o s ∧ ChainAdmissible t (o.exec s) := Iff.rfl

theorem chainAdmissible_append {x y : List Op} {s : KState}
    (hx : ChainAdmissible x s) (hy : ChainAdmissible y (execChain x s)) :
    ChainAdmissible (x ++ y) s := by
  induction x generalizing s with
  | nil => simpa using hy
  | cons a t ih => exact ⟨hx.1, ih hx.2 (by simpa using hy)⟩

/-- Admissibility is exactly OSA-4.0 well-formedness minus the registry check. -/
theorem chainOk_of_chainAdmissible {reg : List Op} {ops : List Op} {s : KState}
    (hreg : ∀ o ∈ ops, o ∈ reg) (h : ChainAdmissible ops s) : ChainOk reg ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons o t ih =>
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    refine ⟨⟨List.mem_map_of_mem (hreg o (by simp)), h2, h1, h3⟩, ?_⟩
    exact ih (fun x hx => hreg x (by simp [hx])) h4

/-- Conversely, a well-formed chain is admissible: well-formedness adds only the
registry check. -/
theorem chainAdmissible_of_chainOk {reg : List Op} {ops : List Op} {s : KState}
    (h : ChainOk reg ops s) : ChainAdmissible ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons o t ih =>
    obtain ⟨⟨-, h2, h1, h3⟩, h4⟩ := h
    exact ⟨⟨h1, h2, h3⟩, ih h4⟩

/-! ## Symbolic chain preconditions -/

/-- The facts an operator consumes, as a predicate. -/
def consumePred (o : Op) : Pred := conj (o.consumes.map Pred.factExists)

/-- The authorization requirement of an operator, as a predicate. -/
def authPred (o : Op) : Pred := if o.requiresAuth = true then .factExists o.authFact else .ctrue

/-- Everything that must hold in a state for an operator to be admissible. -/
def stepPred (o : Op) : Pred := .pand (conj o.requires) (.pand (consumePred o) (authPred o))

theorem eval_consumePred_iff (o : Op) (s : KState) :
    eval s (consumePred o) = PT.TRUE_KNOWN ↔ ∀ f ∈ o.consumes, s.factStatus f = PT.TRUE_KNOWN := by
  rw [consumePred, eval_conj_eq_true_iff]
  constructor
  · intro h f hf; exact h (.factExists f) (List.mem_map_of_mem hf)
  · rintro h p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hp
    exact h f hf

theorem eval_authPred_iff (o : Op) (s : KState) :
    eval s (authPred o) = PT.TRUE_KNOWN ↔
      (o.requiresAuth = true → s.factStatus o.authFact = PT.TRUE_KNOWN) := by
  unfold authPred
  by_cases h : o.requiresAuth = true
  · simp [h, eval]
  · simp [h, eval]

theorem eval_stepPred_iff (o : Op) (s : KState) :
    eval s (stepPred o) = PT.TRUE_KNOWN ↔ StepAdmissible o s := by
  rw [stepPred, StepAdmissible, eval, PT.and_eq_true_iff, eval, PT.and_eq_true_iff,
    eval_conj_eq_true_iff, eval_consumePred_iff, eval_authPred_iff]
  rfl

/-- Symbolic precondition of a whole chain plus a goal. -/
def chainPred : List Op → Pred → Pred
  | [], goal => goal
  | o :: t, goal => .pand (stepPred o) (o.wp (chainPred t goal))

/-- The symbolic chain precondition is exactly "the chain runs and achieves the
goal". -/
theorem chainPred_eq_true_iff (ops : List Op) (goal : Pred) (s : KState) :
    eval s (chainPred ops goal) = PT.TRUE_KNOWN ↔
      ChainAdmissible ops s ∧ eval (execChain ops s) goal = PT.TRUE_KNOWN := by
  induction ops generalizing s with
  | nil => simp [chainPred]
  | cons o t ih =>
    rw [chainPred, eval, PT.and_eq_true_iff, eval_stepPred_iff, Op.eval_wp, ih,
      ChainAdmissible_cons, execChain_cons, and_assoc]

/-! ## Bounded search -/

/-- A correct repair from state `s`: registry operators only, admissible at every
step, and achieving the goal. -/
def RepairCorrect (reg : List Op) (goal : Pred) (s : KState) (ops : List Op) : Prop :=
  (∀ o ∈ ops, o ∈ reg) ∧ ChainAdmissible ops s ∧ eval (execChain ops s) goal = PT.TRUE_KNOWN

/-- Bounded depth-first search for a repair.  `n` is the fuel, i.e. the maximum
length of the plan returned. -/
def searchRepair (reg : List Op) (goal : Pred) : ℕ → KState → Option (List Op)
  | 0, s => if eval s goal = PT.TRUE_KNOWN then some [] else none
  | n + 1, s =>
      if eval s goal = PT.TRUE_KNOWN then some []
      else
        reg.findSome? (fun o =>
          if StepAdmissible o s then (searchRepair reg goal n (o.exec s)).map (o :: ·) else none)

/-- Soundness: anything the search returns really is a repair, of length at most
the fuel. -/
theorem searchRepair_sound (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState) (ops : List Op), searchRepair reg goal n s = some ops →
      RepairCorrect reg goal s ops ∧ ops.length ≤ n := by
  intro n
  induction n with
  | zero =>
    intro s ops h
    rw [searchRepair] at h
    split_ifs at h with hg
    cases h
    exact ⟨⟨by simp, trivial, by simpa using hg⟩, le_rfl⟩
  | succ n ih =>
    intro s ops h
    rw [searchRepair] at h
    split_ifs at h with hg
    · cases h
      exact ⟨⟨by simp, trivial, by simpa using hg⟩, Nat.zero_le _⟩
    · obtain ⟨l₁, o, l₂, hreg, hfo, -⟩ := List.findSome?_eq_some_iff.1 h
      have hoMem : o ∈ reg := by rw [hreg]; simp
      by_cases hadm : StepAdmissible o s
      · rw [if_pos hadm] at hfo
        obtain ⟨t, ht, hops⟩ := Option.map_eq_some_iff.1 hfo
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ih (o.exec s) t ht
        subst hops
        refine ⟨⟨?_, ⟨hadm, h2⟩, by simpa using h3⟩, ?_⟩
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hoMem
          · exact h1 x hx
        · simpa using Nat.succ_le_succ h4
      · rw [if_neg hadm] at hfo; cases hfo

/-- Completeness: if a repair of length at most the fuel exists, the search finds
one. -/
theorem searchRepair_complete (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState) (ops : List Op), RepairCorrect reg goal s ops → ops.length ≤ n →
      (searchRepair reg goal n s).isSome := by
  intro n
  induction n with
  | zero =>
    intro s ops hc hlen
    have : ops = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
    subst this
    rw [searchRepair, if_pos (by simpa using hc.2.2)]
    rfl
  | succ n ih =>
    intro s ops hc hlen
    rw [searchRepair]
    by_cases hg : eval s goal = PT.TRUE_KNOWN
    · rw [if_pos hg]; rfl
    · rw [if_neg hg]
      obtain ⟨hreg, hadm, hgoal⟩ := hc
      cases ops with
      | nil => exact absurd (by simpa using hgoal) hg
      | cons o t =>
        obtain ⟨hao, hat⟩ := hadm
        have hrest : (searchRepair reg goal n (o.exec s)).isSome := by
          refine ih (o.exec s) t ⟨fun x hx => hreg x (by simp [hx]), hat, by simpa using hgoal⟩ ?_
          simpa using Nat.le_of_succ_le_succ (by simpa using hlen)
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hrest
        have hne : ¬ (List.findSome? (fun o => if StepAdmissible o s then
            (searchRepair reg goal n (o.exec s)).map (o :: ·) else none) reg = none) := by
          rw [List.findSome?_eq_none_iff]
          push_neg
          exact ⟨o, hreg o (by simp), by rw [if_pos hao, hl]; simp⟩
        cases hf : List.findSome? (fun o => if StepAdmissible o s then
            (searchRepair reg goal n (o.exec s)).map (o :: ·) else none) reg with
        | none => exact absurd hf hne
        | some r => rfl

/-- The exact characterisation of the bounded search. -/
theorem searchRepair_isSome_iff (reg : List Op) (goal : Pred) (n : ℕ) (s : KState) :
    (searchRepair reg goal n s).isSome ↔
      ∃ ops, RepairCorrect reg goal s ops ∧ ops.length ≤ n := by
  constructor
  · intro h
    obtain ⟨ops, hops⟩ := Option.isSome_iff_exists.1 h
    exact ⟨ops, searchRepair_sound reg goal n s ops hops⟩
  · rintro ⟨ops, hc, hlen⟩
    exact searchRepair_complete reg goal n s ops hc hlen

/-- More fuel never loses a solution. -/
theorem searchRepair_mono (reg : List Op) (goal : Pred) (s : KState) {n m : ℕ} (hnm : n ≤ m)
    (h : (searchRepair reg goal n s).isSome) : (searchRepair reg goal m s).isSome := by
  obtain ⟨ops, hc, hlen⟩ := (searchRepair_isSome_iff reg goal n s).1 h
  exact (searchRepair_isSome_iff reg goal m s).2 ⟨ops, hc, le_trans hlen hnm⟩

/-! ## Iterative deepening -/

/-- Iterative deepening: the first repair found by increasing the fuel from `0`. -/
def minRepair (reg : List Op) (goal : Pred) : ℕ → KState → Option (List Op)
  | 0, s => searchRepair reg goal 0 s
  | n + 1, s =>
      match minRepair reg goal n s with
      | some ops => some ops
      | none => searchRepair reg goal (n + 1) s

theorem minRepair_sound (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState) (ops : List Op), minRepair reg goal n s = some ops →
      RepairCorrect reg goal s ops ∧ ops.length ≤ n := by
  intro n
  induction n with
  | zero => intro s ops h; exact searchRepair_sound reg goal 0 s ops h
  | succ n ih =>
    intro s ops h
    rw [minRepair] at h
    cases hm : minRepair reg goal n s with
    | some r =>
      rw [hm] at h
      simp only [Option.some.injEq] at h
      obtain ⟨hc, hlen⟩ := ih s r hm
      subst h
      exact ⟨hc, le_trans hlen (Nat.le_succ n)⟩
    | none =>
      rw [hm] at h
      exact searchRepair_sound reg goal (n + 1) s ops h

theorem minRepair_eq_none_iff (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState), minRepair reg goal n s = none ↔ searchRepair reg goal n s = none := by
  intro n
  induction n with
  | zero => intro s; rw [minRepair]
  | succ n ih =>
    intro s
    rw [minRepair]
    cases hm : minRepair reg goal n s with
    | some r =>
      have hns : ¬ searchRepair reg goal n s = none := by
        rw [← ih s, hm]; simp
      have : (searchRepair reg goal n s).isSome := by
        cases h : searchRepair reg goal n s with
        | none => exact absurd h hns
        | some _ => rfl
      have hsucc := searchRepair_mono reg goal s (Nat.le_succ n) this
      constructor
      · intro h; cases h
      · intro h
        rw [h] at hsucc
        cases hsucc
    | none => simp

theorem minRepair_isSome_iff (reg : List Op) (goal : Pred) (n : ℕ) (s : KState) :
    (minRepair reg goal n s).isSome ↔ (searchRepair reg goal n s).isSome := by
  constructor <;> intro h
  · cases hs : searchRepair reg goal n s with
    | none =>
      rw [← minRepair_eq_none_iff] at hs
      rw [hs] at h; cases h
    | some _ => rfl
  · cases hm : minRepair reg goal n s with
    | none =>
      rw [minRepair_eq_none_iff] at hm
      rw [hm] at h; cases h
    | some _ => rfl

/-- Minimality: iterative deepening returns a shortest repair within the bound. -/
theorem minRepair_length_le (reg : List Op) (goal : Pred) :
    ∀ (n : ℕ) (s : KState) (ops : List Op), minRepair reg goal n s = some ops →
      ∀ ops', RepairCorrect reg goal s ops' → ops'.length ≤ n → ops.length ≤ ops'.length := by
  intro n
  induction n with
  | zero =>
    intro s ops h ops' _ hlen'
    obtain ⟨-, hlen⟩ := minRepair_sound reg goal 0 s ops h
    omega
  | succ n ih =>
    intro s ops h ops' hc' hlen'
    rw [minRepair] at h
    cases hm : minRepair reg goal n s with
    | some r =>
      rw [hm] at h
      simp only [Option.some.injEq] at h
      subst h
      by_cases hle : ops'.length ≤ n
      · exact ih s r hm ops' hc' hle
      · obtain ⟨-, hlen⟩ := minRepair_sound reg goal n s r hm
        omega
    | none =>
      rw [hm] at h
      obtain ⟨-, hlen⟩ := searchRepair_sound reg goal (n + 1) s ops h
      by_cases hle : ops'.length ≤ n
      · exfalso
        have : (searchRepair reg goal n s).isSome :=
          searchRepair_complete reg goal n s ops' hc' hle
        rw [← minRepair_isSome_iff, hm] at this
        cases this
      · omega

/-! ## Feeding a repair back to the compiler -/

/-- A discovered repair, run as a chain in its own right, compiles to `PASS`. -/
theorem repair_compiles_pass (reg : List Op) (goal : Pred) (n : ℕ) (s : KState)
    (ops : List Op) (h : searchRepair reg goal n s = some ops) :
    (compile ⟨reg, s, ops, goal⟩).verdict = .PASS := by
  obtain ⟨⟨hreg, hadm, hgoal⟩, -⟩ := searchRepair_sound reg goal n s ops h
  exact (compile_verdict_pass_iff _).2 ⟨chainOk_of_chainAdmissible hreg hadm, hgoal⟩

/-- Prefixing a failing chain with a repair for its symbolic precondition makes
the whole thing compile to `PASS`. -/
theorem repaired_chain_compiles_pass (reg : List Op) (chain : List Op) (goal : Pred)
    (n : ℕ) (s : KState) (ops : List Op)
    (hchain : ∀ o ∈ chain, o ∈ reg)
    (h : searchRepair reg (chainPred chain goal) n s = some ops) :
    (compile ⟨reg, s, ops ++ chain, goal⟩).verdict = .PASS := by
  obtain ⟨⟨hreg, hadm, hgoal⟩, -⟩ := searchRepair_sound reg (chainPred chain goal) n s ops h
  obtain ⟨hadm2, hgoal2⟩ := (chainPred_eq_true_iff chain goal (execChain ops s)).1 hgoal
  refine (compile_verdict_pass_iff _).2 ⟨?_, ?_⟩
  · refine chainOk_of_chainAdmissible (fun o ho => ?_) ?_
    · rcases List.mem_append.1 ho with h' | h'
      · exact hreg o h'
      · exact hchain o h'
    · exact chainAdmissible_append hadm hadm2
  · rw [execChain_append]; exact hgoal2

end Polymath.OSA5
