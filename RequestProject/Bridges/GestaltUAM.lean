import RequestProject.Gestalt.UCC
import RequestProject.Bridges.RegularContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: automata as cognitive systems

A deterministic automaton reading a fixed letter is a cognitive system whose
environment is the transition map and whose predictor is the identity: it
"learns" exactly at the states the letter moves.  Under this reading the UCC
theorems become automata theorems:

* `trajectory_eq_evalFrom` identifies the cognitive trajectory with the run of
  the automaton on a constant word;
* `dfa_revisits` is T5 (pigeonhole recurrence) for automata;
* `no_distinction_language_trivial` is T1: an acceptance channel that draws no
  distinction has a trivial language;
* `returnLanguage_contextFree` shows the "ouroboros" language of words
  returning a state to itself is context-free.
-/

namespace PolymathAtlas.Bridges

open PolymathAtlas.Gestalt.UCC
open UAM.ContextFree

universe u

variable {α σ : Type u}

/-! ## An automaton as a cognitive system -/

/-- The cognitive system of an automaton driven by a fixed input letter. -/
def dfaSystem [DecidableEq σ] (M : DFA α σ) (a : α) : CognitiveSystem σ where
  env q := M.step q a
  predict q := q
  step q := M.step q a
  learningRate q := if M.step q a = q then 0 else 1
  learningRate_nonneg q := by split_ifs <;> norm_num
  learningRate_eq_zero_iff q := by
    by_cases h : M.step q a = q
    · rw [if_pos h]
      exact ⟨fun _ => h.symm, fun _ => rfl⟩
    · rw [if_neg h]
      exact ⟨fun hc => absurd hc (by norm_num), fun hc => absurd hc.symm h⟩

@[simp] theorem dfaSystem_step [DecidableEq σ] (M : DFA α σ) (a : α) (q : σ) :
    (dfaSystem M a).step q = M.step q a := rfl

@[simp] theorem dfaSystem_predict [DecidableEq σ] (M : DFA α σ) (a : α) (q : σ) :
    (dfaSystem M a).predict q = q := rfl

/-- The cognitive trajectory of `dfaSystem M a` is the run of `M` on a constant
word. -/
theorem trajectory_eq_evalFrom [DecidableEq σ] (M : DFA α σ) (a : α) (q : σ) (n : ℕ) :
    (dfaSystem M a).trajectory q n = M.evalFrom q (List.replicate n a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CognitiveSystem.trajectory_succ, ih, List.replicate_succ', DFA.evalFrom_of_append]
    simp [DFA.evalFrom]

/-- **T5 for automata.** Reading one letter repeatedly, an automaton on a finite
state space revisits a state within `card σ` steps. -/
theorem dfa_revisits [Fintype σ] [DecidableEq σ] (M : DFA α σ) (a : α) (q : σ) :
    ∃ i j, i < j ∧ j ≤ t5Bound σ ∧
      M.evalFrom q (List.replicate i a) = M.evalFrom q (List.replicate j a) := by
  obtain ⟨i, j, hij, hj, h⟩ := t5_trajectory_revisits (dfaSystem M a) q
  exact ⟨i, j, hij, hj, by
    rw [← trajectory_eq_evalFrom, ← trajectory_eq_evalFrom]; exact h⟩

/-! ## T1 for automata -/

/-- The acceptance channel of an automaton. -/
def acceptChannel (M : DFA α σ) : Channel σ Prop := fun q => q ∈ M.accept

/-- **T1 for automata.** If the acceptance channel draws no distinction, the
language of the automaton is trivial. -/
theorem no_distinction_language_trivial (M : DFA α σ)
    (h : ¬ DrawsDistinction (acceptChannel M)) :
    (∀ w : List α, w ∉ M.accepts) ∨ (∀ w : List α, w ∈ M.accepts) := by
  have hconst : ∀ q r : σ, (q ∈ M.accept) = (r ∈ M.accept) := by
    intro q r
    by_contra hc
    exact h ⟨q, r, hc⟩
  by_cases hstart : M.start ∈ M.accept
  · right
    intro w
    rw [DFA.mem_accepts, hconst (M.eval w) M.start]
    exact hstart
  · left
    intro w
    rw [DFA.mem_accepts, hconst (M.eval w) M.start]
    exact hstart

/-! ## Return languages -/

/-- The automaton that accepts exactly the words returning `q` to itself. -/
def returnDFA (M : DFA α σ) (q : σ) : DFA α σ where
  step := M.step
  start := q
  accept := {q}

/-- The language of `returnDFA M q` is the set of words that return `q` to
itself. -/
theorem returnDFA_accepts (M : DFA α σ) (q : σ) :
    (returnDFA M q).accepts = {w : List α | M.evalFrom q w = q} := by
  rfl

/-- The return ("ouroboros") language of a state is context-free. -/
theorem returnLanguage_contextFree (M : DFA α σ) (q : σ) :
    ∃ (N : Type u) (g : Grammar N α), g.language = {w : List α | M.evalFrom q w = q} := by
  obtain ⟨N, g, hg⟩ := regular_subset_contextFree (returnDFA M q)
  exact ⟨N, g, by rw [hg, returnDFA_accepts]⟩

/-- Every language accepted by a finite automaton is context-free. -/
theorem dfa_language_contextFree (M : DFA α σ) :
    ∃ (N : Type u) (g : Grammar N α), g.language = M.accepts :=
  regular_subset_contextFree M

end PolymathAtlas.Bridges
