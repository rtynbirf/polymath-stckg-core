import RequestProject.Dependency

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proof graphs and forward chaining

A `Proofs` record is a set of assumptions together with a list of inference
steps, each step deriving a conclusion from finitely many premises.  `Derivable`
is the inductively generated set of derivable statements, and `saturate` is the
forward-chaining algorithm that computes it round by round.

Main results:

* `mem_saturate_derivable` (soundness) — everything the algorithm produces is
  derivable;
* `exists_mem_saturate_of_derivable` (completeness) — everything derivable is
  produced after finitely many rounds;
* `derivable_iff_mem_of_fixpoint` — once a round adds nothing new, the computed
  set is exactly the set of derivable statements, so derivability is decided by
  running `saturate` until it stabilises.
-/

namespace Polymath.ProofGraph

/-- One inference step: a conclusion justified by a list of premises. -/
structure Step where
  /-- The statement established by the step. -/
  conclusion : ℕ
  /-- The statements the step consumes. -/
  premises : List ℕ
  deriving DecidableEq, Repr, Inhabited

/-- A proof graph: assumptions taken for granted, plus inference steps. -/
structure Proofs where
  /-- Statements accepted without justification. -/
  assumptions : Finset ℕ
  /-- The available inference steps. -/
  steps : List Step

/-- The statements derivable from the assumptions using the steps. -/
inductive Derivable (P : Proofs) : ℕ → Prop
  | assumption {n : ℕ} : n ∈ P.assumptions → Derivable P n
  | infer {s : Step} : s ∈ P.steps → (∀ p ∈ s.premises, Derivable P p) →
      Derivable P s.conclusion

/-! ## Forward chaining -/

/-- One round of forward chaining: add the conclusion of every step all of whose
premises are already known. -/
def stepOnce (P : Proofs) (k : Finset ℕ) : Finset ℕ :=
  k ∪ ((P.steps.filter (fun s => s.premises.all (fun p => decide (p ∈ k)))).map
    (·.conclusion)).toFinset

/-- `n` rounds of forward chaining starting from the assumptions. -/
def saturate (P : Proofs) : ℕ → Finset ℕ
  | 0 => P.assumptions
  | n + 1 => stepOnce P (saturate P n)

theorem subset_stepOnce (P : Proofs) (k : Finset ℕ) : k ⊆ stepOnce P k :=
  Finset.subset_union_left

theorem mem_stepOnce_iff (P : Proofs) (k : Finset ℕ) (x : ℕ) :
    x ∈ stepOnce P k ↔ x ∈ k ∨ ∃ s ∈ P.steps, (∀ p ∈ s.premises, p ∈ k) ∧ s.conclusion = x := by
  simp [stepOnce, List.mem_filter, and_assoc]

theorem saturate_succ_subset (P : Proofs) (n : ℕ) : saturate P n ⊆ saturate P (n + 1) :=
  subset_stepOnce P _

theorem saturate_mono (P : Proofs) {m n : ℕ} (h : m ≤ n) : saturate P m ⊆ saturate P n := by
  induction n with
  | zero => simp [Nat.le_zero.1 h]
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact fun x hx => saturate_succ_subset P n (ih (Nat.lt_succ_iff.1 hlt) hx)
    · have : m = n + 1 := le_antisymm h hge
      subst this
      exact Finset.Subset.refl _

/-! ## Soundness -/

/-- Everything forward chaining produces is derivable. -/
theorem mem_saturate_derivable (P : Proofs) (n : ℕ) {x : ℕ} (hx : x ∈ saturate P n) :
    Derivable P x := by
  induction n generalizing x with
  | zero => exact Derivable.assumption hx
  | succ n ih =>
    rcases (mem_stepOnce_iff P (saturate P n) x).1 hx with h | ⟨s, hs, hprem, hconc⟩
    · exact ih h
    · exact hconc ▸ Derivable.infer hs (fun p hp => ih (hprem p hp))

/-! ## Completeness -/

private theorem exists_common_bound (P : Proofs) (l : List ℕ)
    (h : ∀ p ∈ l, ∃ n, p ∈ saturate P n) : ∃ N, ∀ p ∈ l, p ∈ saturate P N := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    obtain ⟨na, hna⟩ := h a (List.mem_cons_self ..)
    obtain ⟨N, hN⟩ := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    refine ⟨max na N, ?_⟩
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hpt
    · exact saturate_mono P (le_max_left _ _) hna
    · exact saturate_mono P (le_max_right _ _) (hN p hpt)

/-- Everything derivable is produced after finitely many rounds. -/
theorem exists_mem_saturate_of_derivable {P : Proofs} {x : ℕ} (h : Derivable P x) :
    ∃ n, x ∈ saturate P n := by
  induction h with
  | assumption hn => exact ⟨0, hn⟩
  | @infer s hs _ ih =>
    obtain ⟨N, hN⟩ := exists_common_bound P s.premises ih
    exact ⟨N + 1, (mem_stepOnce_iff P (saturate P N) s.conclusion).2
      (Or.inr ⟨s, hs, hN, rfl⟩)⟩

/-! ## Closed sets and the fixpoint criterion -/

/-- A set of statements is closed when it contains the assumptions and is stable
under the inference steps. -/
def Closed (P : Proofs) (k : Finset ℕ) : Prop :=
  P.assumptions ⊆ k ∧ ∀ s ∈ P.steps, (∀ p ∈ s.premises, p ∈ k) → s.conclusion ∈ k

/-- Derivability is the least closed set. -/
theorem derivable_subset_of_closed {P : Proofs} {k : Finset ℕ} (hk : Closed P k) {x : ℕ}
    (hx : Derivable P x) : x ∈ k := by
  induction hx with
  | assumption hn => exact hk.1 hn
  | @infer s hs _ ih => exact hk.2 s hs ih

theorem closed_of_stepOnce_eq {P : Proofs} {k : Finset ℕ} (hassum : P.assumptions ⊆ k)
    (h : stepOnce P k = k) : Closed P k := by
  refine ⟨hassum, fun s hs hprem => ?_⟩
  have : s.conclusion ∈ stepOnce P k :=
    (mem_stepOnce_iff P k s.conclusion).2 (Or.inr ⟨s, hs, hprem, rfl⟩)
  rwa [h] at this

/-- **Fixpoint criterion.**  If a round of forward chaining adds nothing, the
computed set is exactly the set of derivable statements. -/
theorem derivable_iff_mem_of_fixpoint (P : Proofs) {n : ℕ}
    (h : saturate P (n + 1) = saturate P n) (x : ℕ) :
    Derivable P x ↔ x ∈ saturate P n := by
  constructor
  · intro hx
    refine derivable_subset_of_closed (closed_of_stepOnce_eq ?_ h) hx
    exact saturate_mono P (Nat.zero_le n)
  · exact mem_saturate_derivable P n

/-- Once forward chaining stabilises it stays stable. -/
theorem saturate_eq_of_fixpoint (P : Proofs) {n : ℕ} (h : saturate P (n + 1) = saturate P n) :
    ∀ m, n ≤ m → saturate P m = saturate P n := by
  intro m hm
  induction m with
  | zero => simp [Nat.le_zero.1 hm]
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := Nat.lt_succ_iff.1 hlt
      rw [saturate, ih hnm, ← saturate, h]
    · have : n = m + 1 := le_antisymm hm hge
      rw [this]

end Polymath.ProofGraph
