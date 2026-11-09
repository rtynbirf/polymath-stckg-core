import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pumping lemma for regular languages

Mathlib proves a pumping lemma for a *fixed* deterministic automaton
(`DFA.pumping_lemma`), phrased with the language operations `{a} * {b}∗ * {c}`.
This module repackages it as a statement about an arbitrary regular *language*,
in the familiar `x y^i z` form, and derives from it a reusable non-regularity
criterion together with a concrete separating example.

Main results:

* `UAM.PumpingLemma.regular_pumping` — every regular language has a pumping
  length `p > 0`.
* `UAM.PumpingLemma.not_isRegular_of_pumping_fails` — the contrapositive, in the
  shape used when proving a language irregular.
* `UAM.PumpingLemma.not_isRegular_unary_of_gaps` — a unary language whose set of
  lengths has, above every bound, an element followed by a gap of that size is
  not regular.
* `UAM.PumpingLemma.squareLengths_not_isRegular` — the language of unary words of
  square length is not regular.
-/

namespace UAM.PumpingLemma

open Language

variable {α : Type}

/-- `wordPow y i` is the `i`-fold concatenation `y ++ … ++ y` of a word. -/
def wordPow (y : List α) (i : ℕ) : List α := (List.replicate i y).flatten

@[simp] theorem wordPow_zero (y : List α) : wordPow y 0 = [] := rfl

@[simp] theorem wordPow_one (y : List α) : wordPow y 1 = y := by
  simp [wordPow]

theorem wordPow_length (y : List α) (i : ℕ) : (wordPow y i).length = i * y.length := by
  induction i with
  | zero => simp [wordPow]
  | succ n ih => simp [wordPow, List.replicate_succ, Nat.succ_mul, Nat.add_comm]

theorem wordPow_mem_kstar (y : List α) (i : ℕ) :
    wordPow y i ∈ KStar.kstar ({y} : Language α) := by
  rw [Language.mem_kstar]
  exact ⟨List.replicate i y, rfl, by intro z hz; simpa using List.eq_of_mem_replicate hz⟩

/-- **Pumping lemma for regular languages.**  Every regular language `L` admits a
positive pumping length `p`: any word of `L` of length at least `p` splits as
`x ++ y ++ z` with `|x ++ y| ≤ p` and `y ≠ []` such that every `x ++ y^i ++ z`
again lies in `L`. -/
theorem regular_pumping {L : Language α} (hL : L.IsRegular) :
    ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
      ∃ x y z : List α, w = x ++ y ++ z ∧ (x ++ y).length ≤ p ∧ y ≠ [] ∧
        ∀ i, x ++ wordPow y i ++ z ∈ L := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  refine ⟨Fintype.card σ, Fintype.card_pos_iff.2 ⟨M.start⟩, fun w hw hlen => ?_⟩
  obtain ⟨x, y, z, hw', hlen', hne, hsub⟩ := M.pumping_lemma hw hlen
  refine ⟨x, y, z, hw', by simpa using hlen', hne, fun i => ?_⟩
  exact hsub ⟨x ++ wordPow y i, ⟨x, rfl, wordPow y i, wordPow_mem_kstar y i, rfl⟩, z, rfl, rfl⟩

/-- Non-regularity criterion: if for every candidate pumping length some word of
`L` resists pumping, then `L` is not regular. -/
theorem not_isRegular_of_pumping_fails {L : Language α}
    (h : ∀ p : ℕ, 0 < p → ∃ w ∈ L, p ≤ w.length ∧
      ∀ x y z : List α, w = x ++ y ++ z → (x ++ y).length ≤ p → y ≠ [] →
        ∃ i, x ++ wordPow y i ++ z ∉ L) :
    ¬ L.IsRegular := by
  intro hL
  obtain ⟨p, hp, hpump⟩ := regular_pumping hL
  obtain ⟨w, hwL, hwlen, hw⟩ := h p hp
  obtain ⟨x, y, z, hsplit, hxy, hne, hmem⟩ := hpump w hwL hwlen
  obtain ⟨i, hi⟩ := hw x y z hsplit hxy hne
  exact hi (hmem i)

/-! ### A unary application -/

/-- The unary language determined by a set of admissible lengths. -/
def unaryLang (S : Set ℕ) : Language Unit := {w | w.length ∈ S}

@[simp] theorem mem_unaryLang {S : Set ℕ} {w : List Unit} : w ∈ unaryLang S ↔ w.length ∈ S :=
  Iff.rfl

/-- If, above every bound `p`, the length set `S` contains an element `n` such
that none of `n + 1, …, n + p` belongs to `S`, then the unary language of `S` is
not regular: pumping a nonempty block once more would land in the gap. -/
theorem not_isRegular_unary_of_gaps (S : Set ℕ)
    (hgap : ∀ p : ℕ, 0 < p → ∃ n ∈ S, p ≤ n ∧ ∀ k, 0 < k → k ≤ p → n + k ∉ S) :
    ¬ (unaryLang S).IsRegular := by
  refine not_isRegular_of_pumping_fails ?_
  intro p hp
  obtain ⟨n, hnS, hpn, hgapn⟩ := hgap p hp
  refine ⟨List.replicate n (), by simpa using hnS, by simpa using hpn, ?_⟩
  intro x y z hsplit hxy hne
  refine ⟨2, ?_⟩
  have hlen : x.length + y.length + z.length = n := by
    have := congrArg List.length hsplit
    simpa [Nat.add_assoc] using this.symm
  have hylen : 0 < y.length := List.length_pos_iff.2 hne
  have hyp : y.length ≤ p := le_trans (by simp) hxy
  have : (x ++ wordPow y 2 ++ z).length = n + y.length := by
    simp only [List.length_append, wordPow_length]
    omega
  simp only [mem_unaryLang, this]
  exact hgapn y.length hylen hyp

/-- The set of perfect squares. -/
def squares : Set ℕ := {n | ∃ m, n = m * m}

/-- The unary language of words whose length is a perfect square. -/
def squareLengths : Language Unit := unaryLang squares

/-- **The unary language of square lengths is not regular.**  Consecutive squares
are eventually more than `p` apart, so no pumping length can work. -/
theorem squareLengths_not_isRegular : ¬ squareLengths.IsRegular := by
  refine not_isRegular_unary_of_gaps squares ?_
  intro p hp
  refine ⟨p * p, ⟨p, rfl⟩, Nat.le_mul_of_pos_left p hp, ?_⟩
  rintro k hk hkp ⟨m, hm⟩
  have hmp : p < m := by nlinarith
  have : p + 1 ≤ m := hmp
  nlinarith

end UAM.PumpingLemma
