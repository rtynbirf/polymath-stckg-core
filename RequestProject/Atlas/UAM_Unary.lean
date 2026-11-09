import RequestProject.Atlas.UAM_Pumping
import RequestProject.UAM_MyhillNerode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Unary regular languages are exactly the ultimately periodic ones

Over a one-letter alphabet a word is determined by its length, so a language is
the same thing as a set of natural numbers.  This module proves the classical
characterisation: such a language is regular precisely when its set of lengths is
*ultimately periodic*, i.e. periodic from some point on.

Main results:

* `UAM.Unary.leftQuotient_unary_eq_iff` — two unary left quotients agree exactly
  when the corresponding shifted length sets agree;
* `UAM.Unary.ultimatelyPeriodic_of_isRegular` and
  `UAM.Unary.isRegular_of_ultimatelyPeriodic` — the two directions;
* `UAM.Unary.isRegular_iff_ultimatelyPeriodic` — the characterisation, and
  `UAM.Unary.isRegular_unaryLang_iff` its restatement for `unaryLang`;
* `UAM.Unary.not_ultimatelyPeriodic_setOfPrimes` and
  `UAM.Unary.primeLengths_not_isRegular` — the unary language of prime lengths is
  not regular;
* `UAM.Unary.not_ultimatelyPeriodic_squares` — and neither is the language of
  square lengths.
-/

namespace UAM.Unary

open Language UAM.PumpingLemma

/-- The unary word of a given length. -/
def unaryWord (n : ℕ) : List Unit := List.replicate n ()

@[simp] theorem length_unaryWord (n : ℕ) : (unaryWord n).length = n := by
  simp [unaryWord]

theorem unaryWord_add (m n : ℕ) : unaryWord (m + n) = unaryWord m ++ unaryWord n := by
  rw [unaryWord, unaryWord, unaryWord, List.replicate_add]

/-- Every word over a one-letter alphabet is the unary word of its length. -/
theorem eq_unaryWord (w : List Unit) : w = unaryWord w.length := by
  induction w with
  | nil => rfl
  | cons a t ih => cases a; simpa [unaryWord, List.replicate_succ] using congrArg (List.cons ()) ih

/-- The set of lengths of the words of a unary language. -/
def lengthSet (L : Language Unit) : Set ℕ := {n | unaryWord n ∈ L}

theorem mem_iff_length_mem (L : Language Unit) (w : List Unit) :
    w ∈ L ↔ w.length ∈ lengthSet L := by
  constructor
  · intro hw; simpa [lengthSet, ← eq_unaryWord w] using hw
  · intro hw
    have : unaryWord w.length ∈ L := hw
    rwa [← eq_unaryWord w] at this

/-- A set of naturals is ultimately periodic if it is invariant under a fixed
positive shift above some threshold. -/
def UltimatelyPeriodic (S : Set ℕ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → (n ∈ S ↔ n + p ∈ S)

theorem mem_leftQuotient_unary (L : Language Unit) (n : ℕ) (v : List Unit) :
    v ∈ L.leftQuotient (unaryWord n) ↔ n + v.length ∈ lengthSet L := by
  rw [Language.mem_leftQuotient]
  constructor
  · intro h
    have : unaryWord n ++ unaryWord v.length ∈ L := by rwa [← eq_unaryWord v]
    simpa [lengthSet, unaryWord_add] using this
  · intro h
    have : unaryWord (n + v.length) ∈ L := h
    rw [unaryWord_add] at this
    rwa [← eq_unaryWord v] at this

/-- Unary left quotients are equal exactly when the shifted length sets agree. -/
theorem leftQuotient_unary_eq_iff (L : Language Unit) (m n : ℕ) :
    L.leftQuotient (unaryWord m) = L.leftQuotient (unaryWord n) ↔
      ∀ k, (m + k ∈ lengthSet L ↔ n + k ∈ lengthSet L) := by
  constructor
  · intro h k
    have h1 : unaryWord k ∈ L.leftQuotient (unaryWord m) ↔
        unaryWord k ∈ L.leftQuotient (unaryWord n) := by rw [h]
    rwa [mem_leftQuotient_unary, mem_leftQuotient_unary, length_unaryWord] at h1
  · intro h
    ext v
    rw [mem_leftQuotient_unary, mem_leftQuotient_unary]
    exact h v.length

theorem leftQuotient_unary_shift (L : Language Unit) {m n : ℕ}
    (h : L.leftQuotient (unaryWord m) = L.leftQuotient (unaryWord n)) (k : ℕ) :
    L.leftQuotient (unaryWord (m + k)) = L.leftQuotient (unaryWord (n + k)) := by
  rw [leftQuotient_unary_eq_iff] at h ⊢
  intro j
  have := h (k + j)
  simpa [Nat.add_assoc] using this

/-- Regular unary languages have ultimately periodic length sets. -/
theorem ultimatelyPeriodic_of_isRegular {L : Language Unit} (h : L.IsRegular) :
    UltimatelyPeriodic (lengthSet L) := by
  have hfin : (Set.range L.leftQuotient).Finite :=
    Language.IsRegular.finite_range_leftQuotient h
  obtain ⟨i, -, j, -, hne, heq⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo
      (f := fun n : ℕ => L.leftQuotient (unaryWord n))
      (fun n _ => Set.mem_range_self (unaryWord n)) hfin
  rcases Nat.lt_or_ge i j with hij | hij
  · refine ⟨i, j - i, by omega, ?_⟩
    intro n hn
    have hshift := leftQuotient_unary_shift L heq (n - i)
    rw [show i + (n - i) = n by omega, show j + (n - i) = n + (j - i) by omega] at hshift
    have := (leftQuotient_unary_eq_iff L n (n + (j - i))).1 hshift 0
    simpa using this
  · have hji : j < i := by omega
    refine ⟨j, i - j, by omega, ?_⟩
    intro n hn
    have hshift := leftQuotient_unary_shift L heq.symm (n - j)
    rw [show j + (n - j) = n by omega, show i + (n - j) = n + (i - j) by omega] at hshift
    have := (leftQuotient_unary_eq_iff L n (n + (i - j))).1 hshift 0
    simpa using this

/-- Unary languages with ultimately periodic length sets are regular. -/
theorem isRegular_of_ultimatelyPeriodic {L : Language Unit}
    (h : UltimatelyPeriodic (lengthSet L)) : L.IsRegular := by
  obtain ⟨N, p, hp, hper⟩ := h
  have key : ∀ n, N ≤ n →
      L.leftQuotient (unaryWord n) = L.leftQuotient (unaryWord (n + p)) := by
    intro n hn
    rw [leftQuotient_unary_eq_iff]
    intro k
    have := hper (n + k) (by omega)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  -- every quotient equals one taken at an index below `N + p`
  have small : ∀ n : ℕ, ∃ m, m < N + p ∧
      L.leftQuotient (unaryWord n) = L.leftQuotient (unaryWord m) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hlt : n < N + p
      · exact ⟨n, hlt, rfl⟩
      · have hge : N ≤ n - p := by omega
        obtain ⟨m, hm, hmeq⟩ := ih (n - p) (by omega)
        refine ⟨m, hm, ?_⟩
        have := key (n - p) hge
        rw [show n - p + p = n by omega] at this
        rw [← this, hmeq]
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hsub : Set.range L.leftQuotient ⊆
      (fun m : ℕ => L.leftQuotient (unaryWord m)) '' (Set.Iio (N + p)) := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨m, hm, hmeq⟩ := small w.length
    refine ⟨m, hm, ?_⟩
    show L.leftQuotient (unaryWord m) = L.leftQuotient w
    rw [← hmeq, ← eq_unaryWord w]
  exact Set.Finite.subset ((Set.finite_Iio (N + p)).image _) hsub

/-- **Unary characterisation.** A language over a one-letter alphabet is regular
iff its set of lengths is ultimately periodic. -/
theorem isRegular_iff_ultimatelyPeriodic (L : Language Unit) :
    L.IsRegular ↔ UltimatelyPeriodic (lengthSet L) :=
  ⟨ultimatelyPeriodic_of_isRegular, isRegular_of_ultimatelyPeriodic⟩

@[simp] theorem lengthSet_unaryLang (S : Set ℕ) : lengthSet (unaryLang S) = S := by
  ext n
  show (unaryWord n).length ∈ S ↔ n ∈ S
  rw [length_unaryWord]

/-- The same characterisation, phrased for the language of words whose length
lies in a prescribed set. -/
theorem isRegular_unaryLang_iff (S : Set ℕ) :
    (unaryLang S).IsRegular ↔ UltimatelyPeriodic S := by
  rw [isRegular_iff_ultimatelyPeriodic, lengthSet_unaryLang]

/-! ## Two non-examples -/

/-- The set of primes is not ultimately periodic: from a prime `q` above the
threshold one reaches the composite number `q * (1 + p)`. -/
theorem not_ultimatelyPeriodic_setOfPrimes : ¬ UltimatelyPeriodic {n : ℕ | n.Prime} := by
  rintro ⟨N, p, hp, hper⟩
  obtain ⟨q, hqN, hq⟩ := Nat.exists_infinite_primes (N + 2)
  have hstep : ∀ k, q + k * p ∈ {n : ℕ | n.Prime} := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k ih =>
      have := (hper (q + k * p) (by omega)).1 ih
      have hrw : q + k * p + p = q + (k + 1) * p := by ring
      rwa [hrw] at this
  have hmem : q + q * p ∈ {n : ℕ | n.Prime} := hstep q
  have hfact : q + q * p = q * (1 + p) := by ring
  rw [hfact] at hmem
  have hq1 : 1 < q := hq.one_lt
  have : ¬ (q * (1 + p)).Prime := by
    intro hpr
    rcases (Nat.prime_mul_iff.1 hpr) with ⟨_, h1⟩ | ⟨_, h1⟩
    · omega
    · omega
  exact this hmem

/-- The unary language of prime lengths is not regular. -/
theorem primeLengths_not_isRegular : ¬ (unaryLang {n : ℕ | n.Prime}).IsRegular := by
  rw [isRegular_unaryLang_iff]
  exact not_ultimatelyPeriodic_setOfPrimes

/-- The set of perfect squares is not ultimately periodic. -/
theorem not_ultimatelyPeriodic_squares : ¬ UltimatelyPeriodic squares := by
  intro h
  exact squareLengths_not_isRegular ((isRegular_unaryLang_iff squares).2 h)

end UAM.Unary
