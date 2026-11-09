import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Reachable states and trimming an automaton

A state of a deterministic automaton is *reachable* when some word drives the
automaton into it from the start state.  Unreachable states can be deleted
without changing the accepted language:

* `UAM.Reachability.trim` — the automaton restricted to its reachable states;
* `UAM.Reachability.trim_accepts` — trimming preserves the language;
* `UAM.Reachability.trim_all_reachable` — every state of the trimmed automaton
  is reachable in it;
* `UAM.Reachability.card_trim_le` — trimming never increases the number of
  states.
-/

namespace UAM.Reachability

universe u v

variable {α : Type u} {σ : Type v}

/-- A state is reachable when some word leads to it from the start state. -/
def Reachable (M : DFA α σ) (q : σ) : Prop := ∃ w : List α, M.eval w = q

theorem reachable_start (M : DFA α σ) : Reachable M M.start := ⟨[], rfl⟩

theorem reachable_step {M : DFA α σ} {q : σ} (h : Reachable M q) (a : α) :
    Reachable M (M.step q a) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w ++ [a], by simp [DFA.eval, DFA.evalFrom]⟩

theorem reachable_evalFrom {M : DFA α σ} {q : σ} (h : Reachable M q) (w : List α) :
    Reachable M (M.evalFrom q w) := by
  induction w generalizing q with
  | nil => simpa using h
  | cons a t ih =>
    rw [DFA.evalFrom_cons]
    exact ih (reachable_step h a)

/-- The subtype of reachable states. -/
def ReachableState (M : DFA α σ) : Type v := {q : σ // Reachable M q}

instance instFiniteReachableState (M : DFA α σ) [Finite σ] : Finite (ReachableState M) :=
  Subtype.finite

/-- The automaton obtained by deleting the unreachable states. -/
def trim (M : DFA α σ) : DFA α (ReachableState M) where
  step q a := ⟨M.step q.1 a, reachable_step q.2 a⟩
  start := ⟨M.start, reachable_start M⟩
  accept := {q | q.1 ∈ M.accept}

@[simp] theorem trim_step_val (M : DFA α σ) (q : ReachableState M) (a : α) :
    ((trim M).step q a).1 = M.step q.1 a := rfl

theorem evalFrom_trim (M : DFA α σ) (q : ReachableState M) (w : List α) :
    ((trim M).evalFrom q w).1 = M.evalFrom q.1 w := by
  induction w generalizing q with
  | nil => rfl
  | cons a t ih =>
    rw [DFA.evalFrom_cons, DFA.evalFrom_cons, ih]
    rfl

/-- **Trimming preserves the language.** -/
theorem trim_accepts (M : DFA α σ) : (trim M).accepts = M.accepts := by
  ext w
  rw [DFA.mem_accepts, DFA.mem_accepts, DFA.eval, DFA.eval]
  show ((trim M).evalFrom (trim M).start w) ∈ (trim M).accept ↔ _
  rw [show (trim M).accept = {q : ReachableState M | q.1 ∈ M.accept} from rfl]
  simp only [Set.mem_setOf_eq]
  rw [evalFrom_trim]
  rfl

/-- Every state of the trimmed automaton is reachable in it. -/
theorem trim_all_reachable (M : DFA α σ) (q : ReachableState M) : Reachable (trim M) q := by
  obtain ⟨w, hw⟩ := q.2
  refine ⟨w, ?_⟩
  apply Subtype.ext
  rw [DFA.eval, evalFrom_trim]
  exact hw

/-- Trimming never increases the number of states. -/
theorem card_trim_le (M : DFA α σ) [Fintype σ] [Fintype (ReachableState M)] :
    Fintype.card (ReachableState M) ≤ Fintype.card σ :=
  Fintype.card_le_of_injective (fun q => q.1) Subtype.val_injective

/-- The trimmed automaton of a finite automaton is finite, so the trimmed
automaton witnesses regularity just as well. -/
theorem isRegular_trim {L : Language α} {σ' : Type} [Fintype σ'] (M : DFA α σ')
    (hM : M.accepts = L) : L.IsRegular := by
  classical
  exact ⟨ReachableState M, Fintype.ofFinite _, trim M, by rw [trim_accepts, hM]⟩

end UAM.Reachability
