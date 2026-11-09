import RequestProject.OSA4.Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OSA-4.0 Epistemics: belief merging and uncertainty accounting

Two epistemic guarantees:

* **Belief merging** is a bounded join-semilattice operation (`PT.join`), so
  merging branches is commutative, associative and idempotent — LAW-013,
  LAW-014, LAW-015.  Crucially, merging a known-true with a known-false belief
  produces `CONFLICT` rather than silently choosing a side.
* **Non-overclaim** (LAW-009): along a chain of honest inference steps the
  uncertainty attached to a claim never decreases.
-/

namespace Polymath.OSA4

/-! ## Belief merging -/

/-- LAW-013 (join commutativity). -/
theorem law013_join_comm (a b : Belief) : PT.join a b = PT.join b a := PT.join_comm a b

/-- LAW-014 (join associativity). -/
theorem law014_join_assoc (a b c : Belief) :
    PT.join (PT.join a b) c = PT.join a (PT.join b c) := PT.join_assoc a b c

/-- LAW-015 (join idempotence). -/
theorem law015_join_idem (a : Belief) : PT.join a a = a := PT.join_self a

/-- Merging incompatible beliefs is flagged, never silently resolved. -/
theorem join_conflict_of_disagree :
    PT.join PT.TRUE_KNOWN PT.FALSE_KNOWN = PT.CONFLICT := rfl

/-- Merge a whole list of beliefs. -/
def mergeBeliefs : List Belief → Belief
  | [] => .UNKNOWN
  | b :: t => PT.join b (mergeBeliefs t)

theorem mergeBeliefs_append (l₁ l₂ : List Belief) :
    mergeBeliefs (l₁ ++ l₂) = PT.join (mergeBeliefs l₁) (mergeBeliefs l₂) := by
  induction l₁ with
  | nil => simp [mergeBeliefs]
  | cons b t ih => simp [mergeBeliefs, ih, PT.join_assoc]

/-- A merge of beliefs that all agree on `TRUE` is `TRUE`. -/
theorem mergeBeliefs_all_true {l : List Belief} (h : ∀ b ∈ l, b = PT.TRUE_KNOWN) (hne : l ≠ []) :
    mergeBeliefs l = PT.TRUE_KNOWN := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b t ih =>
    rcases eq_or_ne t [] with rfl | ht
    · simp [mergeBeliefs, h b (by simp)]
    · rw [mergeBeliefs, h b (by simp), ih (fun x hx => h x (by simp [hx])) ht]
      rfl

/-- If two branches disagree, the merge records a conflict. -/
theorem mergeBeliefs_conflict :
    mergeBeliefs [PT.TRUE_KNOWN, PT.FALSE_KNOWN] = PT.CONFLICT := rfl

/-! ## Uncertainty accounting -/

/-- An uncertainty budget carried by a claim. -/
abbrev Uncertainty := ℕ

/-- Propagate an uncertainty budget through a chain of honest steps, each of
which adds its own (non-negative) uncertainty. -/
def propagate : List Uncertainty → Uncertainty → Uncertainty
  | [], u => u
  | d :: t, u => propagate t (u + d)

/-- LAW-009 (epistemic non-overclaim): the uncertainty out of an honest chain is
never smaller than the uncertainty going in. -/
theorem law009_no_overclaim (ds : List Uncertainty) (u : Uncertainty) :
    u ≤ propagate ds u := by
  induction ds generalizing u with
  | nil => exact le_rfl
  | cons d t ih => exact le_trans (Nat.le_add_right u d) (ih (u + d))

theorem propagate_append (l₁ l₂ : List Uncertainty) (u : Uncertainty) :
    propagate (l₁ ++ l₂) u = propagate l₂ (propagate l₁ u) := by
  induction l₁ generalizing u with
  | nil => rfl
  | cons d t ih => simp [propagate, ih]

/-- Uncertainty is monotone in the starting budget. -/
theorem propagate_mono (ds : List Uncertainty) {u v : Uncertainty} (h : u ≤ v) :
    propagate ds u ≤ propagate ds v := by
  induction ds generalizing u v with
  | nil => exact h
  | cons d t ih => exact ih (Nat.add_le_add_right h d)

end Polymath.OSA4
