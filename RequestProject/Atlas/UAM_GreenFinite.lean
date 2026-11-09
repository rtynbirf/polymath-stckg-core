import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Idempotent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Green's relations in a finite monoid: `J = D`

In an arbitrary monoid `D ⊆ J`, and the inclusion can be strict.  In a *finite*
monoid the two relations coincide.  The proof rests on the stability of finite
monoids:

* `UAM.Green.rEquiv_of_jEquiv_mul` — if `a * b` is `J`-equivalent to `a` then it
  is already `R`-equivalent to `a`;
* `UAM.Green.lEquiv_of_jEquiv_mul` — the dual statement on the left.

Both are proved by iterating an equation `a = u * a * w` and passing to an
exponent at which `u` and `w` become idempotent, which is possible because the
monoid is finite (`UAM.Idempotent.exists_pow_isIdempotentElem`).

The main theorem is `UAM.Green.jEquiv_iff_dEquiv`.
-/

namespace UAM.Green

variable {M : Type*} [Monoid M]

/-! ## Iterating a two-sided equation -/

/-- If `a = u * a * w` then `a = uⁿ * a * wⁿ` for every `n`. -/
theorem eq_pow_mul_pow {a u w : M} (h : a = u * a * w) (n : ℕ) : a = u ^ n * a * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc a = u * a * w := h
      _ = u * (u ^ n * a * w ^ n) * w := by rw [← ih]
      _ = u ^ (n + 1) * a * w ^ (n + 1) := by
          rw [pow_succ w, pow_succ' u]; simp [mul_assoc]

/-- Two elements of a finite monoid have idempotent powers with a common
exponent. -/
theorem exists_common_idempotent_pow [Finite M] (x y : M) :
    ∃ n : ℕ, 0 < n ∧ IsIdempotentElem (x ^ n) ∧ IsIdempotentElem (y ^ n) := by
  obtain ⟨n₁, hn₁, h₁⟩ := UAM.Idempotent.exists_pow_isIdempotentElem x
  obtain ⟨n₂, hn₂, h₂⟩ := UAM.Idempotent.exists_pow_isIdempotentElem y
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_, ?_⟩
  · rw [UAM.Idempotent.pow_mul_of_isIdempotentElem h₁ hn₂]
    exact h₁
  · rw [Nat.mul_comm, UAM.Idempotent.pow_mul_of_isIdempotentElem h₂ hn₁]
    exact h₂

/-! ## Stability -/

/-- **Right stability of a finite monoid.**  If `a * b` is `J`-equivalent to `a`
then the two are `R`-equivalent. -/
theorem rEquiv_of_jEquiv_mul [Finite M] {a b : M} (h : JEquiv (a * b) a) :
    REquiv (a * b) a := by
  obtain ⟨u, v, huv⟩ := h.2
  have hstep : a = u * a * (b * v) := by
    conv_lhs => rw [huv]
    simp [mul_assoc]
  obtain ⟨n, hn, he, hf⟩ := exists_common_idempotent_pow u (b * v)
  have hiter : a = u ^ n * a * (b * v) ^ n := eq_pow_mul_pow hstep n
  have hfix : a * (b * v) ^ n = a := by
    calc a * (b * v) ^ n = u ^ n * a * (b * v) ^ n * (b * v) ^ n := by rw [← hiter]
      _ = u ^ n * a * ((b * v) ^ n * (b * v) ^ n) := by rw [mul_assoc]
      _ = u ^ n * a * (b * v) ^ n := by rw [hf]
      _ = a := hiter.symm
  refine ⟨⟨b, rfl⟩, ⟨v * (b * v) ^ (n - 1), ?_⟩⟩
  have hsplit : (b * v) ^ n = b * (v * (b * v) ^ (n - 1)) := by
    have h1 : (b * v) ^ n = (b * v) * (b * v) ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h1, mul_assoc]
  calc a = a * (b * v) ^ n := hfix.symm
    _ = a * (b * (v * (b * v) ^ (n - 1))) := by rw [hsplit]
    _ = a * b * (v * (b * v) ^ (n - 1)) := by rw [mul_assoc]

/-- **Left stability of a finite monoid.**  If `a * b` is `J`-equivalent to `b`
then the two are `L`-equivalent. -/
theorem lEquiv_of_jEquiv_mul [Finite M] {a b : M} (h : JEquiv (a * b) b) :
    LEquiv (a * b) b := by
  obtain ⟨u, v, huv⟩ := h.2
  have hstep : b = (u * a) * b * v := by
    conv_lhs => rw [huv]
    simp [mul_assoc]
  obtain ⟨n, hn, he, hf⟩ := exists_common_idempotent_pow (u * a) v
  have hiter : b = (u * a) ^ n * b * v ^ n := eq_pow_mul_pow hstep n
  have hfix : (u * a) ^ n * b = b := by
    calc (u * a) ^ n * b = (u * a) ^ n * ((u * a) ^ n * b * v ^ n) := by rw [← hiter]
      _ = (u * a) ^ n * (u * a) ^ n * b * v ^ n := by simp [mul_assoc]
      _ = (u * a) ^ n * b * v ^ n := by rw [he]
      _ = b := hiter.symm
  refine ⟨⟨a, rfl⟩, ⟨(u * a) ^ (n - 1) * u, ?_⟩⟩
  have hsplit : (u * a) ^ n = (u * a) ^ (n - 1) * (u * a) := by
    rw [← pow_succ]
    congr 1
    omega
  calc b = (u * a) ^ n * b := hfix.symm
    _ = (u * a) ^ (n - 1) * (u * a) * b := by rw [hsplit]
    _ = (u * a) ^ (n - 1) * u * (a * b) := by simp [mul_assoc]

/-! ## `J = D` -/

/-- **In a finite monoid, `J`-equivalence implies `D`-equivalence.** -/
theorem dEquiv_of_jEquiv [Finite M] {x y : M} (h : JEquiv x y) : DEquiv x y := by
  obtain ⟨u, v, huv⟩ := h.1
  refine ⟨y * v, ?_, ?_⟩
  · -- `x = u * (y * v)` is `L`-equivalent to `y * v`
    have hx : x = u * (y * v) := by rw [huv, mul_assoc]
    have hj : JEquiv (u * (y * v)) (y * v) := by
      refine ⟨⟨u, 1, by simp⟩, ?_⟩
      have h1 : JLe (y * v) y := ⟨1, v, by simp⟩
      have h2 : JLe y x := h.2
      have h3 : JLe x (u * (y * v)) := by rw [← hx]; exact jLe_refl x
      exact jLe_trans (jLe_trans h1 h2) h3
    have := lEquiv_of_jEquiv_mul hj
    rwa [← hx] at this
  · -- `y * v` is `R`-equivalent to `y`
    have hj : JEquiv (y * v) y := by
      refine ⟨⟨1, v, by simp⟩, ?_⟩
      have h2 : JLe y x := h.2
      have h3 : JLe x (y * v) := ⟨u, 1, by rw [huv]; simp [mul_assoc]⟩
      exact jLe_trans h2 h3
    exact rEquiv_of_jEquiv_mul hj

/-- **Green's relations `J` and `D` coincide in a finite monoid.** -/
theorem jEquiv_iff_dEquiv [Finite M] (x y : M) : JEquiv x y ↔ DEquiv x y :=
  ⟨dEquiv_of_jEquiv, jEquiv_of_dEquiv⟩

end UAM.Green
