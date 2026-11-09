import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# OSA-4.0 Repair: one-step repair with lexicographic selection

When a chain fails to compile, a *repair* is a short prefix of operators that
makes it compile.  Plans are ranked lexicographically by

1. the aggregate effect level of the inserted operators (prefer the least
   invasive repair), then
2. the number of inserted operators (prefer the shortest repair).

`bestRepair` returns the lexicographic minimum among the viable one-step
repairs, and LAW-018 says that this plan really is viable and really does
dominate every alternative.
-/

namespace Polymath.OSA4

/-! ## Lexicographic ranking vectors -/

/-- Lexicographic order on ranking vectors: first component dominates. -/
def RVec.le (a b : ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel RVec.le := fun a b => by unfold RVec.le; infer_instance

theorem RVec.le_refl (a : ℕ × ℕ) : RVec.le a a := Or.inr ⟨rfl, le_rfl⟩

theorem RVec.le_trans {a b c : ℕ × ℕ} (h₁ : RVec.le a b) (h₂ : RVec.le b c) : RVec.le a c := by
  unfold RVec.le at *; omega

theorem RVec.le_total (a b : ℕ × ℕ) : RVec.le a b ∨ RVec.le b a := by
  unfold RVec.le; omega

theorem RVec.le_of_not_le {a b : ℕ × ℕ} (h : ¬ RVec.le a b) : RVec.le b a :=
  (RVec.le_total a b).resolve_left h

/-! ## Repair plans -/

/-- A repair plan is a list of operators to insert before the failing chain. -/
structure RepairPlan where
  ops : List Op
  deriving Repr, DecidableEq

/-- Ranking vector of a plan: aggregate effect level, then length. -/
def RepairPlan.cost (p : RepairPlan) : ℕ × ℕ :=
  ((aggregate (p.ops.map (·.effect))).rank, p.ops.length)

/-- Binary lexicographic minimum of two plans. -/
def minPlan (p q : RepairPlan) : RepairPlan := if RVec.le p.cost q.cost then p else q

theorem minPlan_eq_or (p q : RepairPlan) : minPlan p q = p ∨ minPlan p q = q := by
  unfold minPlan; split <;> simp

theorem minPlan_le_left (p q : RepairPlan) : RVec.le (minPlan p q).cost p.cost := by
  unfold minPlan
  split_ifs with h
  · exact RVec.le_refl _
  · exact RVec.le_of_not_le h

theorem minPlan_le_right (p q : RepairPlan) : RVec.le (minPlan p q).cost q.cost := by
  unfold minPlan
  split_ifs with h
  · exact h
  · exact RVec.le_refl _

/-- Lexicographic minimum of a nonempty list, given as head plus tail. -/
def bestOf (p : RepairPlan) : List RepairPlan → RepairPlan
  | [] => p
  | q :: t => bestOf (minPlan p q) t

theorem bestOf_mem (p : RepairPlan) (t : List RepairPlan) : bestOf p t ∈ p :: t := by
  induction t generalizing p with
  | nil => simp [bestOf]
  | cons q t ih =>
    rw [bestOf]
    have := ih (minPlan p q)
    rcases List.mem_cons.1 this with h | h
    · rcases minPlan_eq_or p q with hm | hm <;> rw [h, hm] <;> simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem bestOf_le (p : RepairPlan) (t : List RepairPlan) :
    ∀ q ∈ p :: t, RVec.le (bestOf p t).cost q.cost := by
  induction t generalizing p with
  | nil =>
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact RVec.le_refl _
  | cons a t ih =>
    intro q hq
    have hIH := ih (minPlan p a)
    rw [bestOf]
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact RVec.le_trans (hIH _ (List.mem_cons_self)) (minPlan_le_left q a)
    · rcases List.mem_cons.1 hq' with rfl | hq''
      · exact RVec.le_trans (hIH _ (List.mem_cons_self)) (minPlan_le_right p q)
      · exact hIH q (List.mem_cons_of_mem _ hq'')

/-- Lexicographic minimum of a list of plans. -/
def bestPlan : List RepairPlan → Option RepairPlan
  | [] => none
  | p :: t => some (bestOf p t)

theorem bestPlan_eq_none_iff (ps : List RepairPlan) : bestPlan ps = none ↔ ps = [] := by
  cases ps <;> simp [bestPlan]

theorem bestPlan_mem {ps : List RepairPlan} {p : RepairPlan} (h : bestPlan ps = some p) :
    p ∈ ps := by
  cases ps with
  | nil => simp [bestPlan] at h
  | cons a t =>
    rw [bestPlan] at h
    simp only [Option.some.injEq] at h
    subst h
    exact bestOf_mem a t

theorem bestPlan_le {ps : List RepairPlan} {p : RepairPlan} (h : bestPlan ps = some p) :
    ∀ q ∈ ps, RVec.le p.cost q.cost := by
  cases ps with
  | nil => simp [bestPlan] at h
  | cons a t =>
    rw [bestPlan] at h
    simp only [Option.some.injEq] at h
    subst h
    exact bestOf_le a t

/-! ## Repairing a scenario -/

/-- The scenario obtained by inserting a plan in front of the failing chain. -/
def RepairPlan.apply (p : RepairPlan) (sc : Scenario) : Scenario :=
  ⟨sc.registry, sc.init, p.ops ++ sc.chain, sc.goal⟩

/-- A plan is viable when the repaired scenario compiles to `PASS`. -/
def viable (sc : Scenario) (p : RepairPlan) : Bool :=
  decide ((compile (p.apply sc)).verdict = .PASS)

/-- The one-step repair candidates: insert a single registry operator. -/
def oneStepRepairs (sc : Scenario) : List RepairPlan :=
  (sc.registry.map (fun o => (⟨[o]⟩ : RepairPlan))).filter (viable sc)

/-- The lexicographically best one-step repair, if any exists. -/
def bestRepair (sc : Scenario) : Option RepairPlan := bestPlan (oneStepRepairs sc)

/-- LAW-018 (repair soundness): the selected repair is viable, is a genuine
one-step repair, and dominates every other viable one-step repair. -/
theorem law018_repair_sound {sc : Scenario} {p : RepairPlan} (h : bestRepair sc = some p) :
    (compile (p.apply sc)).verdict = .PASS ∧
    p ∈ oneStepRepairs sc ∧
    (∀ q ∈ oneStepRepairs sc, RVec.le p.cost q.cost) := by
  have hmem : p ∈ oneStepRepairs sc := bestPlan_mem h
  refine ⟨?_, hmem, bestPlan_le h⟩
  have := (List.mem_filter.1 hmem).2
  simpa [viable] using this

/-- If some one-step repair works, `bestRepair` finds one. -/
theorem bestRepair_isSome_of_viable {sc : Scenario} {p : RepairPlan}
    (hp : p ∈ oneStepRepairs sc) : (bestRepair sc).isSome := by
  unfold bestRepair
  cases hb : bestPlan (oneStepRepairs sc) with
  | none =>
    rw [(bestPlan_eq_none_iff _).1 hb] at hp
    cases hp
  | some q => rfl

/-! ## Worked example: repairing the unauthorized deployment -/

/-- The unauthorized deployment scenario of T13. -/
def deployScenario : Scenario := scen [opDEPLOY] (.factExists "Deployed")

theorem deploy_needs_repair : (compile deployScenario).verdict = .REPAIR := by decide

/-- The best repair for the unauthorized deployment is to obtain authorization. -/
theorem deploy_bestRepair :
    bestRepair deployScenario = some ⟨[opGRANT_AUTH_DEPLOY]⟩ := by decide

theorem deploy_repaired_passes :
    (compile ((⟨[opGRANT_AUTH_DEPLOY]⟩ : RepairPlan).apply deployScenario)).verdict = .PASS := by
  decide

end Polymath.OSA4
