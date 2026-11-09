import RequestProject.Atlas.UAM_Syntactic
import RequestProject.Atlas.UAM_Idempotent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Algebraic pumping for regular languages

Combining the two previous modules — a regular language has a finite syntactic
monoid, and every element of a finite monoid has an idempotent power — gives a
purely algebraic pumping principle:

`regular_pumping_word`: for every regular language `L` and every word `w` there
is an exponent `n > 0` such that, *in every context*, the block `w ^ n` may be
replaced by `w ^ (n * k)` for any `k ≥ 1` without changing membership in `L`.

Unlike the automata-theoretic pumping lemma this version pumps a *prescribed*
word and is an equivalence, not merely an implication.
-/

namespace UAM.Pumping

open UAM.Syntactic UAM.Idempotent

variable {α : Type}

/-- **Algebraic pumping.**  For a regular language and any word `w` there is an
exponent `n > 0` such that `w ^ n` and `w ^ (n * k)` are interchangeable in every
context, for every `k ≥ 1`. -/
theorem regular_pumping_word {L : Language α} (hL : L.IsRegular) (w : FreeMonoid α) :
    ∃ n : ℕ, 0 < n ∧ ∀ (u v : FreeMonoid α) (k : ℕ), 0 < k →
      ((u * w ^ n * v).toList ∈ L ↔ (u * w ^ (n * k) * v).toList ∈ L) := by
  have hfin : Finite (SyntacticMonoid L) := (isRegular_iff_finite_syntacticMonoid L).1 hL
  obtain ⟨n, hn, hidem⟩ := exists_pow_isIdempotentElem (syntacticHom L w)
  refine ⟨n, hn, fun u v k hk => ?_⟩
  have hpow : syntacticHom L (w ^ (n * k)) = syntacticHom L (w ^ n) := by
    rw [map_pow, map_pow, pow_mul_of_isIdempotentElem hidem hk]
  exact (syntacticHom_eq_iff L (w ^ n) (w ^ (n * k))).1 hpow.symm u v

/-- The special case `k = 2`: the idempotent block may be doubled. -/
theorem regular_pumping_double {L : Language α} (hL : L.IsRegular) (w : FreeMonoid α) :
    ∃ n : ℕ, 0 < n ∧ ∀ u v : FreeMonoid α,
      ((u * w ^ n * v).toList ∈ L ↔ (u * w ^ n * w ^ n * v).toList ∈ L) := by
  obtain ⟨n, hn, h⟩ := regular_pumping_word hL w
  refine ⟨n, hn, fun u v => ?_⟩
  have := h u v 2 (by norm_num)
  rwa [show n * 2 = n + n by ring, pow_add, ← mul_assoc] at this

/-- A language that fails the algebraic pumping principle for some word is not
regular. -/
theorem not_isRegular_of_not_pumping {L : Language α} {w : FreeMonoid α}
    (h : ∀ n : ℕ, 0 < n → ∃ (u v : FreeMonoid α) (k : ℕ), 0 < k ∧
      ¬((u * w ^ n * v).toList ∈ L ↔ (u * w ^ (n * k) * v).toList ∈ L)) :
    ¬ L.IsRegular := by
  intro hL
  obtain ⟨n, hn, hpump⟩ := regular_pumping_word hL w
  obtain ⟨u, v, k, hk, hne⟩ := h n hn
  exact hne (hpump u v k hk)

end UAM.Pumping
