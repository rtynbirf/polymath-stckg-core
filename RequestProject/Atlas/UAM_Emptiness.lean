import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Small witnesses, emptiness and equivalence of automata

If a deterministic automaton with `n` states accepts anything at all, then it
accepts a word of length `< n`: a longer run repeats a state, and the loop can
be cut out.  This *small witness* property turns emptiness into a bounded
search, and — through a product construction realising the symmetric difference
— makes equivalence of automata a bounded search too.

* `UAM.Emptiness.exists_short_of_accepts` — the small witness property;
* `UAM.Emptiness.accepts_eq_empty_iff` — emptiness is a bounded check;
* `UAM.Emptiness.decidableAcceptsNonempty` — non-emptiness is decidable;
* `UAM.Emptiness.symmDiffDFA`, `UAM.Emptiness.mem_symmDiff_accepts` — the
  symmetric-difference automaton;
* `UAM.Emptiness.accepts_eq_iff_symmDiff_empty` and
  `UAM.Emptiness.decidableAcceptsEq` — equivalence reduces to emptiness and is
  decidable.
-/

namespace UAM.Emptiness

universe u v w

variable {α : Type u} {σ : Type v} {τ : Type w}

/-! ## Cutting loops out of a run -/

/-- Cutting a loop out of a run does not change the final state. -/
theorem eval_take_append_drop (M : DFA α σ) (x : List α) {i j : ℕ}
    (h : M.eval (x.take i) = M.eval (x.take j)) :
    M.eval (x.take i ++ x.drop j) = M.eval x := by
  have hx : M.evalFrom (M.eval (x.take j)) (x.drop j) = M.eval x := by
    have := M.evalFrom_of_append M.start (x.take j) (x.drop j)
    rw [List.take_append_drop] at this
    exact this.symm
  rw [DFA.eval, M.evalFrom_of_append, ← DFA.eval, h]
  exact hx

/-- An accepted word at least as long as the number of states can be shortened. -/
theorem exists_shorter_accepted [Fintype σ] (M : DFA α σ) {v : List α} (hv : v ∈ M.accepts)
    (hlen : Fintype.card σ ≤ v.length) :
    ∃ u ∈ M.accepts, u.length < v.length := by
  classical
  have hcard : Fintype.card σ < Fintype.card (Fin (v.length + 1)) := by
    simpa using Nat.lt_succ_of_le hlen
  obtain ⟨i, j, hij, hstate⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (v.length + 1) => M.eval (v.take i)) hcard
  -- put the two indices in order
  have key : ∀ p q : Fin (v.length + 1), (p : ℕ) < (q : ℕ) →
      M.eval (v.take (p : ℕ)) = M.eval (v.take (q : ℕ)) →
      ∃ u ∈ M.accepts, u.length < v.length := by
    intro p q hpq hstate
    refine ⟨v.take (p : ℕ) ++ v.drop (q : ℕ), ?_, ?_⟩
    · rw [DFA.mem_accepts, eval_take_append_drop M v hstate]
      exact (DFA.mem_accepts M).1 hv
    · have hp : (p : ℕ) ≤ v.length := by omega
      have hq : (q : ℕ) ≤ v.length := by omega
      have hvpos : 0 < v.length := by omega
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with hlt | hlt
  · exact key i j hlt hstate
  · exact key j i hlt hstate.symm

/-- **Small witness property.**  An automaton with finitely many states that
accepts some word accepts one shorter than its number of states. -/
theorem exists_short_of_accepts [Fintype σ] (M : DFA α σ) {w : List α} (hw : w ∈ M.accepts) :
    ∃ v ∈ M.accepts, v.length < Fintype.card σ := by
  have aux : ∀ n : ℕ, ∀ x : List α, x.length = n → x ∈ M.accepts →
      ∃ v ∈ M.accepts, v.length < Fintype.card σ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn hx
      by_cases hlt : x.length < Fintype.card σ
      · exact ⟨x, hx, hlt⟩
      · push_neg at hlt
        obtain ⟨u, hu, hulen⟩ := exists_shorter_accepted M hx hlt
        exact ih u.length (by omega) u rfl hu
  exact aux w.length w rfl hw

/-- Emptiness of the accepted language is a bounded check. -/
theorem accepts_eq_empty_iff [Fintype σ] (M : DFA α σ) :
    (∀ w : List α, w ∉ M.accepts) ↔
      ∀ v : List α, v.length < Fintype.card σ → v ∉ M.accepts := by
  constructor
  · intro h v _ hv; exact h v hv
  · intro h w hw
    obtain ⟨v, hv, hvlen⟩ := exists_short_of_accepts M hw
    exact h v hvlen hv

/-- Non-emptiness is witnessed by a word of bounded length. -/
theorem accepts_nonempty_iff [Fintype σ] (M : DFA α σ) :
    (∃ w : List α, w ∈ M.accepts) ↔
      ∃ (n : Fin (Fintype.card σ)) (v : List.Vector α (n : ℕ)), v.toList ∈ M.accepts := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, hvlen⟩ := exists_short_of_accepts M hw
    exact ⟨⟨v.length, hvlen⟩, ⟨v, rfl⟩, hv⟩
  · rintro ⟨n, v, hv⟩
    exact ⟨v.toList, hv⟩

/-- Non-emptiness of the language of a finite automaton over a finite alphabet
is decidable. -/
instance decidableAcceptsNonempty [Fintype α] [Fintype σ] (M : DFA α σ)
    [DecidablePred (· ∈ M.accept)] : Decidable (∃ w : List α, w ∈ M.accepts) := by
  have : DecidablePred (fun w : List α => w ∈ M.accepts) := fun w =>
    decidable_of_iff _ (M.mem_accepts (x := w)).symm
  exact decidable_of_iff _ (accepts_nonempty_iff M).symm

/-! ## Equivalence through the symmetric difference -/

/-- The product automaton accepting the symmetric difference of two languages. -/
def symmDiffDFA (M : DFA α σ) (N : DFA α τ) : DFA α (σ × τ) where
  step p a := (M.step p.1 a, N.step p.2 a)
  start := (M.start, N.start)
  accept := {p | ¬ (p.1 ∈ M.accept ↔ p.2 ∈ N.accept)}

theorem evalFrom_symmDiff (M : DFA α σ) (N : DFA α τ) (q : σ) (r : τ) (w : List α) :
    (symmDiffDFA M N).evalFrom (q, r) w = (M.evalFrom q w, N.evalFrom r w) := by
  induction w generalizing q r with
  | nil => rfl
  | cons a t ih => simpa [DFA.evalFrom, symmDiffDFA] using ih (M.step q a) (N.step r a)

/-- The product automaton accepts exactly the symmetric difference. -/
theorem mem_symmDiff_accepts (M : DFA α σ) (N : DFA α τ) (w : List α) :
    w ∈ (symmDiffDFA M N).accepts ↔ ¬ (w ∈ M.accepts ↔ w ∈ N.accepts) := by
  rw [DFA.mem_accepts, DFA.mem_accepts, DFA.mem_accepts]
  have h : (symmDiffDFA M N).eval w = (M.eval w, N.eval w) :=
    evalFrom_symmDiff M N M.start N.start w
  rw [DFA.eval] at h ⊢
  rw [h]
  rfl

/-- Two automata are equivalent exactly when their symmetric difference is
empty. -/
theorem accepts_eq_iff_symmDiff_empty (M : DFA α σ) (N : DFA α τ) :
    M.accepts = N.accepts ↔ ∀ w : List α, w ∉ (symmDiffDFA M N).accepts := by
  constructor
  · intro h w hw
    rw [mem_symmDiff_accepts] at hw
    exact hw (by rw [h])
  · intro h
    ext w
    by_contra hne
    exact h w ((mem_symmDiff_accepts M N w).2 hne)

/-- Equivalence of two finite automata over a finite alphabet is decidable. -/
instance decidableAcceptsEq [Fintype α] [Fintype σ] [Fintype τ] (M : DFA α σ) (N : DFA α τ)
    [DecidablePred (· ∈ M.accept)] [DecidablePred (· ∈ N.accept)] :
    Decidable (M.accepts = N.accepts) := by
  have hacc : DecidablePred (· ∈ (symmDiffDFA M N).accept) := by
    intro p
    have : Decidable (p.1 ∈ M.accept ↔ p.2 ∈ N.accept) := inferInstance
    exact inferInstanceAs (Decidable ¬ _)
  have : Decidable (∃ w : List α, w ∈ (symmDiffDFA M N).accepts) :=
    decidableAcceptsNonempty (symmDiffDFA M N)
  have hiff : M.accepts = N.accepts ↔ ¬ ∃ w : List α, w ∈ (symmDiffDFA M N).accepts := by
    rw [accepts_eq_iff_symmDiff_empty]
    exact ⟨fun h ⟨w, hw⟩ => h w hw, fun h w hw => h ⟨w, hw⟩⟩
  exact decidable_of_iff _ hiff.symm

end UAM.Emptiness
