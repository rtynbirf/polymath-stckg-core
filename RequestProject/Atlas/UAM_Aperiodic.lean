import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Idempotent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Aperiodic monoids are exactly the `H`-trivial ones

A monoid is *aperiodic* when every element satisfies `x ^ (n + 1) = x ^ n` for
some `n`, and it is *`H`-trivial* when Green's relation `H` is equality.  For a
finite monoid the two conditions agree:

* `UAM.Green.aperiodic_of_hTrivial` — an `H`-trivial finite monoid is aperiodic,
  because `x ^ n` and `x ^ (n + 1)` are `H`-equivalent as soon as `x ^ n` is
  idempotent;
* `UAM.Green.hTrivial_of_aperiodic` — an aperiodic finite monoid is `H`-trivial.
  If `x H y`, write `y = x * a` and `x = y * b`; multiplication by `a` is then
  injective on the `L`-class of `x`, so `x * a ^ k = x` for some `k ≥ 1`, and
  aperiodicity of `a` upgrades this to `x * a = x`, that is `x = y`.

The two combine into `UAM.Green.aperiodic_iff_hTrivial`.
-/

namespace UAM.Green

variable {M : Type*} [Monoid M]

/-! ## The two conditions -/

/-- A monoid is aperiodic when every element has a stable power. -/
def Aperiodic (M : Type*) [Monoid M] : Prop := ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n

/-- A monoid is `H`-trivial when `H`-equivalent elements are equal. -/
def HTrivial (M : Type*) [Monoid M] : Prop := ∀ x y : M, HEquiv x y → x = y

/-- Once a power is stable, all larger powers agree with it. -/
theorem pow_eq_of_pow_succ_eq {x : M} {n : ℕ} (h : x ^ (n + 1) = x ^ n) (t : ℕ) :
    x ^ (n + t) = x ^ n := by
  induction t with
  | zero => simp
  | succ t ih =>
    have : n + (t + 1) = (n + t) + 1 := by omega
    rw [this, pow_succ, ih, ← pow_succ, h]

/-! ## `H`-trivial implies aperiodic -/

/-- **An `H`-trivial finite monoid is aperiodic.** -/
theorem aperiodic_of_hTrivial [Finite M] (h : HTrivial M) : Aperiodic M := by
  intro x
  obtain ⟨n, hn, hidem⟩ := UAM.Idempotent.exists_pow_isIdempotentElem x
  refine ⟨n, h _ _ ?_⟩
  have hdouble : x ^ (n + n) = x ^ n := by rw [pow_add]; exact hidem
  have hsplitL : x ^ n = x ^ (n - 1) * x ^ (n + 1) := by
    rw [← pow_add]
    have : n - 1 + (n + 1) = n + n := by omega
    rw [this, hdouble]
  have hsplitR : x ^ n = x ^ (n + 1) * x ^ (n - 1) := by
    rw [← pow_add]
    have : n + 1 + (n - 1) = n + n := by omega
    rw [this, hdouble]
  exact ⟨⟨⟨x, by rw [← pow_succ']⟩, ⟨x ^ (n - 1), hsplitL⟩⟩,
    ⟨⟨x, by rw [← pow_succ]⟩, ⟨x ^ (n - 1), hsplitR⟩⟩⟩

/-! ## Aperiodic implies `H`-trivial -/

section Aperiodic

variable {x y a b : M}

/-- Elements of the `L`-class of `x` are unchanged by multiplying by `a` and
then by `b`, when `x * a = y` and `y * b = x`. -/
theorem mul_mul_eq_self_of_lLe (hxa : x * a = y) (hyb : y * b = x) {z : M} (hz : LLe z x) :
    z * a * b = z := by
  obtain ⟨c, rfl⟩ := hz
  calc c * x * a * b = c * (x * a) * b := by rw [mul_assoc c x a]
    _ = c * (y * b) := by rw [hxa, mul_assoc]
    _ = c * x := by rw [hyb]

/-- Every power `x * a ^ i` stays in the `L`-class of `x`. -/
theorem lLe_mul_pow (hxa : x * a = y) (hyx : LLe y x) (i : ℕ) : LLe (x * a ^ i) x := by
  induction i with
  | zero => exact ⟨1, by simp⟩
  | succ i ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨u, hu⟩ := hyx
    refine ⟨c * u, ?_⟩
    calc x * a ^ (i + 1) = (x * a ^ i) * a := by rw [pow_succ, mul_assoc]
      _ = c * x * a := by rw [hc]
      _ = c * (x * a) := by rw [mul_assoc]
      _ = c * y := by rw [hxa]
      _ = c * (u * x) := by rw [hu]
      _ = c * u * x := by rw [mul_assoc]

/-- Cancelling one factor `a` from `x * a ^ (i + 1)`. -/
theorem mul_pow_succ_mul (hxa : x * a = y) (hyb : y * b = x) (hyx : LLe y x) (i : ℕ) :
    x * a ^ (i + 1) * b = x * a ^ i := by
  have hz : LLe (x * a ^ i) x := lLe_mul_pow hxa hyx i
  have := mul_mul_eq_self_of_lLe hxa hyb hz
  calc x * a ^ (i + 1) * b = (x * a ^ i) * a * b := by rw [pow_succ, ← mul_assoc]
    _ = x * a ^ i := this

/-- From a coincidence `x * a ^ i = x * a ^ j` the smaller exponent may be
cancelled. -/
theorem mul_pow_eq_of_mul_pow_eq (hxa : x * a = y) (hyb : y * b = x) (hyx : LLe y x) :
    ∀ (i j : ℕ), i ≤ j → x * a ^ i = x * a ^ j → x = x * a ^ (j - i) := by
  intro i
  induction i with
  | zero => intro j _ h; simpa using h
  | succ i ih =>
    intro j hij h
    have hj : j = (j - 1) + 1 := by omega
    have h1 : x * a ^ (i + 1) * b = x * a ^ i := mul_pow_succ_mul hxa hyb hyx i
    have h2 : x * a ^ j * b = x * a ^ (j - 1) := by
      rw [hj]
      exact mul_pow_succ_mul hxa hyb hyx (j - 1)
    have h3 : x * a ^ i = x * a ^ (j - 1) := by
      rw [← h1, ← h2, h]
    have h4 := ih (j - 1) (by omega) h3
    have : j - 1 - i = j - (i + 1) := by omega
    rwa [this] at h4

/-- Multiplying `x` by a power of `a` that fixes it stays fixed. -/
theorem mul_pow_mul_eq {k : ℕ} (h : x * a ^ k = x) (t : ℕ) : x * a ^ (k * t) = x := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hexp : k * (t + 1) = k * t + k := by ring
    rw [hexp, pow_add, ← mul_assoc, ih, h]

end Aperiodic

/-- **An aperiodic finite monoid is `H`-trivial.** -/
theorem hTrivial_of_aperiodic [Finite M] (h : Aperiodic M) : HTrivial M := by
  intro x y hxy
  obtain ⟨⟨-, hyx⟩, ⟨b, hxb⟩, ⟨a, hya⟩⟩ := hxy
  -- `y = x * a` and `x = y * b`
  have hxa : x * a = y := hya.symm
  have hyb : y * b = x := hxb.symm
  -- the sequence `x * aⁱ` cannot be injective in a finite monoid
  obtain ⟨i, j, hij, heq⟩ : ∃ i j : ℕ, i ≠ j ∧ x * a ^ i = x * a ^ j :=
    have hni : ¬ Function.Injective (fun n : ℕ => x * a ^ n) := fun hinj =>
      not_injective_infinite_finite _ hinj
    by
      simp only [Function.Injective, not_forall] at hni
      obtain ⟨i, j, hji, hne⟩ := hni
      exact ⟨i, j, hne, hji⟩
  obtain ⟨p, q, hpq, hlt⟩ : ∃ p q : ℕ, x * a ^ p = x * a ^ q ∧ p < q := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, heq, hlt⟩
    · exact ⟨j, i, heq.symm, hgt⟩
  set k := q - p with hk
  have hk0 : 0 < k := by omega
  have hfix : x * a ^ k = x :=
    (mul_pow_eq_of_mul_pow_eq hxa hyb hyx p q (by omega) hpq).symm
  -- aperiodicity of `a` makes a large enough power of `a` stable
  obtain ⟨m, hm⟩ := h a
  set K := k * (m + 1) with hK
  have hKm : m ≤ K := by
    have : m + 1 ≤ k * (m + 1) := Nat.le_mul_of_pos_left _ hk0
    omega
  have hstable : a ^ K = a ^ (K + 1) := by
    have h1 : a ^ K = a ^ m := by
      have : K = m + (K - m) := by omega
      rw [this, pow_eq_of_pow_succ_eq hm]
    have h2 : a ^ (K + 1) = a ^ m := by
      have : K + 1 = m + (K + 1 - m) := by omega
      rw [this, pow_eq_of_pow_succ_eq hm]
    rw [h1, h2]
  have hxK : x * a ^ K = x := mul_pow_mul_eq hfix (m + 1)
  calc x = x * a ^ K := hxK.symm
    _ = x * a ^ (K + 1) := by rw [hstable]
    _ = x * a ^ K * a := by rw [pow_succ, ← mul_assoc]
    _ = x * a := by rw [hxK]
    _ = y := hxa

/-- **A finite monoid is aperiodic exactly when it is `H`-trivial.** -/
theorem aperiodic_iff_hTrivial [Finite M] : Aperiodic M ↔ HTrivial M :=
  ⟨hTrivial_of_aperiodic, aperiodic_of_hTrivial⟩

end UAM.Green
