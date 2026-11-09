import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Idempotent powers in a finite monoid

Every element of a finite monoid has an idempotent power: there is `n > 0` with
`x ^ n * x ^ n = x ^ n` (`exists_pow_isIdempotentElem`).  This is the algebraic
engine behind pumping arguments — the "eventually periodic" behaviour of the
powers of a single element.

The proof is the standard one: the powers of `x` cannot be pairwise distinct, so
they are eventually periodic with some period `p > 0`, and any multiple of `p`
that is large enough is an idempotent exponent.
-/

namespace UAM.Idempotent

variable {M : Type*} [Monoid M]

/-- Eventual periodicity: if `x ^ i = x ^ (i + p)` then the exponent may be
increased by `p` at any point beyond `i`. -/
theorem pow_add_period {x : M} {i p : ℕ} (h : x ^ i = x ^ (i + p)) (k : ℕ) :
    x ^ (i + k + p) = x ^ (i + k) := by
  have h1 : x ^ (i + k + p) = x ^ (i + p) * x ^ k := by
    rw [← pow_add]; congr 1; omega
  have h2 : x ^ (i + k) = x ^ i * x ^ k := by rw [← pow_add]
  rw [h1, h2, h]

/-- Eventual periodicity for arbitrary multiples of the period. -/
theorem pow_add_mul_period {x : M} {i p : ℕ} (h : x ^ i = x ^ (i + p)) (k t : ℕ) :
    x ^ (i + k + t * p) = x ^ (i + k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have : i + k + (t + 1) * p = (i + (k + t * p)) + p := by ring
    rw [this, pow_add_period h (k + t * p)]
    have : i + (k + t * p) = i + k + t * p := by ring
    rw [this, ih]

/-- **Every element of a finite monoid has an idempotent power.** -/
theorem exists_pow_isIdempotentElem [Finite M] (x : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (x ^ n) := by
  obtain ⟨a, b, hab, hpow⟩ : ∃ a b : ℕ, a ≠ b ∧ x ^ a = x ^ b :=
    have : ¬ Function.Injective (fun n : ℕ => x ^ n) := fun hinj =>
      not_injective_infinite_finite _ hinj
    by
      simp only [Function.Injective, not_forall] at this
      obtain ⟨a, b, hab, hne⟩ := this
      exact ⟨a, b, hne, hab⟩
  -- normalise so that the smaller exponent comes first
  obtain ⟨i, p, hp, hper⟩ : ∃ i p : ℕ, 0 < p ∧ x ^ i = x ^ (i + p) := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b - a, by omega, by rw [hpow]; congr 1; omega⟩
    · exact ⟨b, a - b, by omega, by rw [← hpow]; congr 1; omega⟩
  refine ⟨p * (i + 1), by positivity, ?_⟩
  have hge : i ≤ p * (i + 1) := by nlinarith
  set n := p * (i + 1) with hn
  have hsplit : n + n = i + (n - i) + (i + 1) * p := by
    have : p * (i + 1) = (i + 1) * p := by ring
    omega
  have : IsIdempotentElem (x ^ n) := by
    show x ^ n * x ^ n = x ^ n
    rw [← pow_add, hsplit, pow_add_mul_period hper (n - i) (i + 1)]
    congr 1
    omega
  exact this

/-- The idempotent power absorbs all further multiples of its exponent. -/
theorem pow_mul_of_isIdempotentElem {x : M} {n : ℕ} (h : IsIdempotentElem (x ^ n)) {k : ℕ}
    (hk : 0 < k) : x ^ (n * k) = x ^ n := by
  rw [pow_mul]
  exact h.pow_eq hk.ne'

end UAM.Idempotent
