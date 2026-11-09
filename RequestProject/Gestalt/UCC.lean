import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Gestalt UCC: five theorems about distinction, information and feedback

This module formalises the five core claims of the "universal cognitive cycle":

* **T1** a channel fails to draw a distinction exactly when it is constant;
* **T2** refining a context never loses information, and gains none exactly when
  the refinement is trivial;
* **T3** a perfect predictor has zero learning rate, and any prediction error
  forces a strictly positive one;
* **T4** a perfect error-driven system is inert: its step map is the identity and
  its trajectories are constant;
* **T5** on a finite state space every trajectory revisits a state within
  `card S` steps.
-/

namespace PolymathAtlas.Gestalt.UCC

variable {S Ω : Type*}

/-! ## T1 — distinction -/

/-- An observation channel. -/
abbrev Channel (S Ω : Type*) := S → Ω

/-- A channel draws a distinction when it separates at least two states. -/
def DrawsDistinction (o : Channel S Ω) : Prop := ∃ s t, o s ≠ o t

/-- **T1.** A channel draws no distinction exactly when it is constant. -/
theorem t1_no_distinction_iff_constant (o : Channel S Ω) :
    ¬ DrawsDistinction o ↔ ∀ s t, o s = o t := by
  unfold DrawsDistinction
  push_neg
  rfl

/-- On a nonempty state space, a channel drawing no distinction has a single
value. -/
theorem t1_no_distinction_iff_single_value [Nonempty S] (o : Channel S Ω) :
    ¬ DrawsDistinction o ↔ ∃ c, ∀ s, o s = c := by
  rw [t1_no_distinction_iff_constant]
  constructor
  · intro h
    exact ⟨o (Classical.arbitrary S), fun s => h s _⟩
  · rintro ⟨c, hc⟩ s t
    rw [hc s, hc t]

/-! ## T2 — information gain -/

/-- Uncertainty of a context, measured as the logarithm of its size. -/
noncomputable def uncertainty (C : Set S) : ℝ := Real.log C.ncard

/-- Information gained by moving from a prior context to a posterior one. -/
noncomputable def informationGain (prior post : Set S) : ℝ :=
  uncertainty prior - uncertainty post

/-- Refining a context by a distinction: keep the states that agree with `s`. -/
def refineBy (C : Set S) (d : S → Prop) (s : S) : Set S := {x | x ∈ C ∧ (d x ↔ d s)}

theorem refineBy_subset (C : Set S) (d : S → Prop) (s : S) : refineBy C d s ⊆ C :=
  fun _ hx => hx.1

theorem mem_refineBy_self {C : Set S} {d : S → Prop} {s : S} (hs : s ∈ C) :
    s ∈ refineBy C d s := ⟨hs, Iff.rfl⟩

/-- **T2 (first half).** Refinement never loses information. -/
theorem t2_informationGain_nonneg {A B : Set S} (hBA : B ⊆ A) (hA : A.Finite)
    (hB : B.Nonempty) : 0 ≤ informationGain A B := by
  have hBfin : B.Finite := hA.subset hBA
  have hcard : B.ncard ≤ A.ncard := Set.ncard_le_ncard hBA hA
  have hBpos : 0 < B.ncard := Set.ncard_pos hBfin |>.2 hB
  have : Real.log (B.ncard : ℝ) ≤ Real.log (A.ncard : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hBpos)
    exact_mod_cast hcard
  simpa [informationGain, uncertainty, sub_nonneg] using this

/-- **T2 (second half).** No information is gained exactly when the refinement
was trivial in size. -/
theorem t2_informationGain_eq_zero_iff {A B : Set S} (hBA : B ⊆ A) (hA : A.Finite)
    (hB : B.Nonempty) : informationGain A B = 0 ↔ A.ncard = B.ncard := by
  have hBfin : B.Finite := hA.subset hBA
  have hBpos : 0 < B.ncard := Set.ncard_pos hBfin |>.2 hB
  have hApos : 0 < A.ncard := lt_of_lt_of_le hBpos (Set.ncard_le_ncard hBA hA)
  constructor
  · intro h
    have hlog : Real.log (A.ncard : ℝ) = Real.log (B.ncard : ℝ) := by
      have := sub_eq_zero.1 h
      simpa [uncertainty] using this
    have := Real.log_injOn_pos (by simp; exact_mod_cast hApos)
      (by simp; exact_mod_cast hBpos) hlog
    exact_mod_cast this
  · intro h
    simp [informationGain, uncertainty, h]

/-- Refining a finite nonempty context by any distinction gains information. -/
theorem t2_refine_gain_nonneg {C : Set S} (hC : C.Finite) (d : S → Prop) {s : S}
    (hs : s ∈ C) : 0 ≤ informationGain C (refineBy C d s) :=
  t2_informationGain_nonneg (refineBy_subset C d s) hC ⟨s, mem_refineBy_self hs⟩

/-! ## T3, T4 — feedback and inertness -/

/-- A cognitive system: an environment, a predictor, a step map, and a learning
rate that vanishes exactly when the prediction is correct. -/
structure CognitiveSystem (S : Type*) where
  env : S → S
  predict : S → S
  step : S → S
  learningRate : S → ℝ
  learningRate_nonneg : ∀ s, 0 ≤ learningRate s
  learningRate_eq_zero_iff : ∀ s, learningRate s = 0 ↔ predict s = env s

namespace CognitiveSystem

variable (C : CognitiveSystem S)

/-- The system mispredicts at `s`. -/
def feedbackError (s : S) : Prop := C.predict s ≠ C.env s

/-- The system predicts its environment perfectly. -/
def Perfect : Prop := ∀ s, C.predict s = C.env s

/-- The trajectory of the system from a starting state. -/
def trajectory (x : S) : ℕ → S := fun n => C.step^[n] x

@[simp] theorem trajectory_zero (x : S) : C.trajectory x 0 = x := rfl

theorem trajectory_succ (x : S) (n : ℕ) :
    C.trajectory x (n + 1) = C.step (C.trajectory x n) := by
  simp [trajectory, Function.iterate_succ_apply']

/-- **T3 (first half).** A perfect system has zero learning rate everywhere. -/
theorem t3_perfect_learningRate_zero (h : C.Perfect) (s : S) : C.learningRate s = 0 :=
  (C.learningRate_eq_zero_iff s).2 (h s)

/-- **T3 (second half).** A prediction error forces a strictly positive learning
rate. -/
theorem t3_error_learningRate_pos {s : S} (h : C.feedbackError s) : 0 < C.learningRate s :=
  lt_of_le_of_ne (C.learningRate_nonneg s) fun hc =>
    h ((C.learningRate_eq_zero_iff s).1 hc.symm)

end CognitiveSystem

/-- An error-driven system only moves when it has something to learn. -/
structure ErrorDriven (S : Type*) extends CognitiveSystem S where
  step_eq_self_of_no_learning : ∀ s, learningRate s = 0 → step s = s

namespace ErrorDriven

variable (E : ErrorDriven S)

/-- **T4 (first half).** A perfect error-driven system is inert. -/
theorem t4_perfect_step_id (h : E.toCognitiveSystem.Perfect) : E.step = id := by
  funext s
  exact E.step_eq_self_of_no_learning s (E.toCognitiveSystem.t3_perfect_learningRate_zero h s)

/-- **T4 (second half).** Its trajectories are constant. -/
theorem t4_perfect_trajectory_const (h : E.toCognitiveSystem.Perfect) (x : S) (n : ℕ) :
    E.toCognitiveSystem.trajectory x n = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CognitiveSystem.trajectory_succ, ih]
    have : E.step x = x := congrFun (t4_perfect_step_id E h) x
    exact this

end ErrorDriven

/-! ## T5 — recurrence -/

/-- The horizon after which a trajectory on a finite state space must repeat. -/
def t5Bound (S : Type*) [Fintype S] : ℕ := Fintype.card S

/-- **T5.** Any sequence in a finite type revisits a value within `card S` steps.
In particular every trajectory of a cognitive system is eventually recurrent. -/
theorem t5_pigeonholeRevisit [Fintype S] (f : ℕ → S) :
    ∃ i j, i < j ∧ j ≤ t5Bound S ∧ f i = f j := by
  have hcard : Fintype.card S < Fintype.card (Fin (Fintype.card S + 1)) := by simp
  obtain ⟨a, b, hab, hfab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (Fintype.card S + 1) => f k) hcard
  rcases lt_or_gt_of_ne (fun hc : (a : ℕ) = (b : ℕ) => hab (Fin.ext hc)) with h | h
  · exact ⟨a, b, h, Nat.lt_succ_iff.1 b.isLt, hfab⟩
  · exact ⟨b, a, h, Nat.lt_succ_iff.1 a.isLt, hfab.symm⟩

/-- The recurrence theorem applied to a cognitive trajectory. -/
theorem t5_trajectory_revisits [Fintype S] (C : CognitiveSystem S) (x : S) :
    ∃ i j, i < j ∧ j ≤ t5Bound S ∧ C.trajectory x i = C.trajectory x j :=
  t5_pigeonholeRevisit (C.trajectory x)

end PolymathAtlas.Gestalt.UCC
