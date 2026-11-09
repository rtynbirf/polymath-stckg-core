import RequestProject.Atlas.UAM_Noncounting
import RequestProject.Atlas.UAM_Kleene

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Star-free languages are noncounting

The *star-free* languages form the smallest class of languages containing the
empty language and the singletons `{a}` and closed under boolean operations and
concatenation — Kleene star is deliberately absent.

This module proves the easy (but combinatorially substantial) half of
Schützenberger's theorem:

* `UAM.StarFree.IsStarFree.isRegular` — every star-free language is regular;
* `UAM.StarFree.IsStarFree.noncounting` — every star-free language is
  noncounting, i.e. some exponent `n` makes `n` and `n + 1` repetitions of an
  arbitrary factor indistinguishable;
* consequently `UAM.StarFree.IsStarFree.aperiodic` — the syntactic monoid of a
  star-free language is aperiodic.

The heart of the argument is closure of the noncounting languages under
concatenation (`UAM.StarFree.noncounting_mul`), which rests on the free-monoid
factorisation lemma `UAM.StarFree.pow_split`.

Finally the parity language over a one-letter alphabet is regular but counting,
hence not star-free (`UAM.StarFree.exists_regular_not_starFree`): the inclusion
of the star-free languages in the regular ones is strict.
-/

namespace UAM.StarFree

open UAM.Syntactic UAM.Green

variable {α : Type}

/-! ## Splitting a power in a free monoid -/

/-- Levi's lemma: two factorisations of the same element of a free monoid have a
common refinement. -/
theorem mul_eq_mul_iff (a b c d : FreeMonoid α) :
    a * b = c * d ↔ (∃ e : FreeMonoid α, c = a * e ∧ b = e * d)
      ∨ ∃ e : FreeMonoid α, a = c * e ∧ d = e * b :=
  List.append_eq_append_iff

/-- A product in a free monoid is trivial only if both factors are. -/
theorem mul_eq_one_iff (a b : FreeMonoid α) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  List.append_eq_nil_iff

/-- Any factorisation `w * v = u ^ N` of a nontrivial power cuts inside one of
the `N` copies of `u`: there are `i + j + 1 = N` and a factorisation
`u = u' * u''` with `w = u ^ i * u'` and `v = u'' * u ^ j`. -/
theorem pow_split (u : FreeMonoid α) :
    ∀ N : ℕ, 0 < N → ∀ w v : FreeMonoid α, w * v = u ^ N →
      ∃ (i j : ℕ) (u' u'' : FreeMonoid α),
        u' * u'' = u ∧ i + j + 1 = N ∧ w = u ^ i * u' ∧ v = u'' * u ^ j := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ N ih =>
    intro _ w v h
    rw [pow_succ' u N] at h
    rcases (mul_eq_mul_iff w v u (u ^ N)).mp h with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · exact ⟨0, N, w, c, hc1.symm, by omega, by simp, hc2⟩
    · rcases Nat.eq_zero_or_pos N with rfl | hN
      · rw [pow_zero] at hc2
        obtain ⟨hb, hv⟩ := (mul_eq_one_iff c v).mp hc2.symm
        refine ⟨0, 0, u, 1, mul_one u, by omega, ?_, ?_⟩
        · rw [pow_zero, one_mul, hc1, hb, mul_one]
        · rw [hv, pow_zero, mul_one]
      · obtain ⟨i, j, u', u'', hu, hij, hcw, hv⟩ := ih hN c v hc2.symm
        refine ⟨i + 1, j, u', u'', hu, by omega, ?_, hv⟩
        rw [hc1, hcw, pow_succ' u i, mul_assoc]

/-! ## Elementary facts about noncounting languages -/

/-- The length of a power in a free monoid. -/
theorem length_pow (u : FreeMonoid α) (n : ℕ) :
    (u ^ n).toList.length = n * u.toList.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    show ((u ^ n).toList ++ u.toList).length = _
    rw [List.length_append, ih]
    ring

/-- Noncounting exponents can always be increased by one. -/
theorem noncounting_succ {L : Language α} {n : ℕ} (h : Noncounting L n) :
    Noncounting L (n + 1) := by
  intro u x y
  have h1 := h u (x * u) y
  rw [mul_assoc x u (u ^ n), ← pow_succ' u n, mul_assoc x u (u ^ (n + 1)),
    ← pow_succ' u (n + 1)] at h1
  exact h1

/-- Noncounting exponents can always be increased. -/
theorem noncounting_mono {L : Language α} {n m : ℕ} (h : Noncounting L n) (hnm : n ≤ m) :
    Noncounting L m := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact noncounting_succ ih

/-- A language all of whose words are shorter than `n` is `n`-noncounting: with
`n` copies of a nonempty factor present, neither side can belong to it. -/
theorem noncounting_of_bounded {L : Language α} {n : ℕ}
    (h : ∀ w ∈ L, w.length < n) : Noncounting L n := by
  intro u x y
  rcases eq_or_ne u 1 with rfl | hu
  · simp
  · have hpos : 0 < u.toList.length := by
      rcases Nat.eq_zero_or_pos u.toList.length with hc | hc
      · exact absurd (List.eq_nil_of_length_eq_zero hc) hu
      · exact hc
    have key : ∀ k : ℕ, n ≤ k → (x * u ^ k * y).toList ∉ L := by
      intro k hk hmem
      have hlt := h _ hmem
      have hlen : (x * u ^ k * y).toList.length
          = x.toList.length + k * u.toList.length + y.toList.length := by
        show (x.toList ++ (u ^ k).toList ++ y.toList).length = _
        rw [List.length_append, List.length_append, length_pow]
      have : k ≤ k * u.toList.length := Nat.le_mul_of_pos_right k hpos
      omega
    constructor
    · intro hm; exact absurd hm (key n le_rfl)
    · intro hm; exact absurd hm (key (n + 1) (by omega))

theorem noncounting_zero : Noncounting (0 : Language α) 1 :=
  noncounting_of_bounded (fun _ hw => absurd hw (Set.notMem_empty _))

theorem noncounting_one : Noncounting (1 : Language α) 1 :=
  noncounting_of_bounded (by
    intro w hw
    rw [Language.mem_one] at hw
    simp [hw])

theorem noncounting_singleton (a : α) : Noncounting ({[a]} : Language α) 2 :=
  noncounting_of_bounded (by
    intro w hw
    have hwa : w = [a] := hw
    simp [hwa])

theorem noncounting_compl {L : Language α} {n : ℕ} (h : Noncounting L n) :
    Noncounting Lᶜ n := fun u x y => not_congr (h u x y)

theorem noncounting_add {L M : Language α} {n : ℕ}
    (hL : Noncounting L n) (hM : Noncounting M n) : Noncounting (L + M) n := by
  intro u x y
  rw [Language.mem_add, Language.mem_add]
  exact or_congr (hL u x y) (hM u x y)

/-! ## Closure of the noncounting languages under concatenation -/

/-- Membership in a product, phrased in the free monoid. -/
theorem mem_mul_free (L M : Language α) (z : FreeMonoid α) :
    z.toList ∈ L * M ↔ ∃ z₁ z₂ : FreeMonoid α, z₁.toList ∈ L ∧ z₂.toList ∈ M ∧ z = z₁ * z₂ := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, b, ha, hb, hab.symm⟩
  · rintro ⟨z₁, z₂, h1, h2, rfl⟩
    exact ⟨z₁, h1, z₂, h2, rfl⟩

/-- Regluing the two halves of a cut made inside a power. -/
theorem glue (u u' u'' x y : FreeMonoid α) (hu : u' * u'' = u) (a b : ℕ) :
    (x * u ^ a * u') * (u'' * u ^ b * y) = x * u ^ (a + b + 1) * y := by
  rw [show a + b + 1 = a + (1 + b) by omega, pow_add, pow_add, pow_one, ← hu]
  simp only [mul_assoc]

/-- **Noncounting languages are closed under concatenation.**  If `L` and `M`
are `k`-noncounting then `L * M` is `(2 * k + 1)`-noncounting: a cut of
`x * u ^ (2k+1) * y` either misses the block of `u`'s entirely, or leaves at
least `k` copies of `u` on one of the two sides. -/
theorem noncounting_mul {L M : Language α} {k : ℕ}
    (hL : Noncounting L k) (hM : Noncounting M k) : Noncounting (L * M) (2 * k + 1) := by
  intro u x y
  constructor
  · intro hmem
    obtain ⟨z₁, z₂, h1, h2, hz⟩ := (mem_mul_free L M _).1 hmem
    rw [mul_assoc] at hz
    rcases (mul_eq_mul_iff x (u ^ (2 * k + 1) * y) z₁ z₂).mp hz with
      ⟨as, ha1, ha2⟩ | ⟨bs, hb1, hb2⟩
    · rcases (mul_eq_mul_iff (u ^ (2 * k + 1)) y as z₂).mp ha2 with
        ⟨cs, hc1, hc2⟩ | ⟨ds, hd1, hd2⟩
      · -- the cut is inside `y`
        refine (mem_mul_free L M _).2 ⟨x * u ^ (2 * k + 1 + 1) * cs, z₂, ?_, h2, ?_⟩
        · have hz1 : z₁ = x * u ^ (2 * k + 1) * cs := by rw [ha1, hc1, mul_assoc]
          rw [hz1] at h1
          exact (noncounting_mono hL (by omega) u x cs).1 h1
        · rw [hc2]; simp only [mul_assoc]
      · -- the cut is inside the block of `u`'s
        obtain ⟨i, j, u', u'', hu, hij, hasi, hdsj⟩ :=
          pow_split u (2 * k + 1) (by omega) as ds hd1.symm
        have hz1 : z₁ = x * u ^ i * u' := by rw [ha1, hasi, mul_assoc]
        have hz2 : z₂ = u'' * u ^ j * y := by rw [hd2, hdsj, mul_assoc]
        rcases (by omega : k ≤ i ∨ k ≤ j) with hik | hjk
        · refine (mem_mul_free L M _).2 ⟨x * u ^ (i + 1) * u', z₂, ?_, h2, ?_⟩
          · rw [hz1] at h1
            exact (noncounting_mono hL hik u x u').1 h1
          · rw [hz2, glue u u' u'' x y hu (i + 1) j,
              show i + 1 + j + 1 = 2 * k + 1 + 1 from by omega]
        · refine (mem_mul_free L M _).2 ⟨z₁, u'' * u ^ (j + 1) * y, h1, ?_, ?_⟩
          · rw [hz2] at h2
            exact (noncounting_mono hM hjk u u'' y).1 h2
          · rw [hz1, glue u u' u'' x y hu i (j + 1),
              show i + (j + 1) + 1 = 2 * k + 1 + 1 from by omega]
    · -- the cut is inside `x`
      refine (mem_mul_free L M _).2 ⟨z₁, bs * u ^ (2 * k + 1 + 1) * y, h1, ?_, ?_⟩
      · have hz2 : z₂ = bs * u ^ (2 * k + 1) * y := by rw [hb2, mul_assoc]
        rw [hz2] at h2
        exact (noncounting_mono hM (by omega) u bs y).1 h2
      · rw [hb1]; simp only [mul_assoc]
  · intro hmem
    obtain ⟨z₁, z₂, h1, h2, hz⟩ := (mem_mul_free L M _).1 hmem
    rw [mul_assoc] at hz
    rcases (mul_eq_mul_iff x (u ^ (2 * k + 1 + 1) * y) z₁ z₂).mp hz with
      ⟨as, ha1, ha2⟩ | ⟨bs, hb1, hb2⟩
    · rcases (mul_eq_mul_iff (u ^ (2 * k + 1 + 1)) y as z₂).mp ha2 with
        ⟨cs, hc1, hc2⟩ | ⟨ds, hd1, hd2⟩
      · refine (mem_mul_free L M _).2 ⟨x * u ^ (2 * k + 1) * cs, z₂, ?_, h2, ?_⟩
        · have hz1 : z₁ = x * u ^ (2 * k + 1 + 1) * cs := by rw [ha1, hc1, mul_assoc]
          rw [hz1] at h1
          exact (noncounting_mono hL (by omega) u x cs).2 h1
        · rw [hc2]; simp only [mul_assoc]
      · obtain ⟨i, j, u', u'', hu, hij, hasi, hdsj⟩ :=
          pow_split u (2 * k + 1 + 1) (by omega) as ds hd1.symm
        have hz1 : z₁ = x * u ^ i * u' := by rw [ha1, hasi, mul_assoc]
        have hz2 : z₂ = u'' * u ^ j * y := by rw [hd2, hdsj, mul_assoc]
        rcases (by omega : k + 1 ≤ i ∨ k + 1 ≤ j) with hik | hjk
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          refine (mem_mul_free L M _).2 ⟨x * u ^ i' * u', z₂, ?_, h2, ?_⟩
          · rw [hz1] at h1
            exact (noncounting_mono hL (by omega) u x u').2 h1
          · rw [hz2, glue u u' u'' x y hu i' j,
              show i' + j + 1 = 2 * k + 1 from by omega]
        · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          refine (mem_mul_free L M _).2 ⟨z₁, u'' * u ^ j' * y, h1, ?_, ?_⟩
          · rw [hz2] at h2
            exact (noncounting_mono hM (by omega) u u'' y).2 h2
          · rw [hz1, glue u u' u'' x y hu i j',
              show i + j' + 1 = 2 * k + 1 from by omega]
    · refine (mem_mul_free L M _).2 ⟨z₁, bs * u ^ (2 * k + 1) * y, h1, ?_, ?_⟩
      · have hz2 : z₂ = bs * u ^ (2 * k + 1 + 1) * y := by rw [hb2, mul_assoc]
        rw [hz2] at h2
        exact (noncounting_mono hM (by omega) u bs y).2 h2
      · rw [hb1]; simp only [mul_assoc]

/-! ## Star-free languages -/

/-- The star-free languages: generated from `∅`, `{ε}` and the letters by union,
complement and concatenation. -/
inductive IsStarFree : Language α → Prop
  | zero : IsStarFree 0
  | one : IsStarFree 1
  | char (a : α) : IsStarFree {[a]}
  | compl {L : Language α} : IsStarFree L → IsStarFree Lᶜ
  | add {L M : Language α} : IsStarFree L → IsStarFree M → IsStarFree (L + M)
  | mul {L M : Language α} : IsStarFree L → IsStarFree M → IsStarFree (L * M)

/-- Every star-free language is regular. -/
theorem IsStarFree.isRegular {L : Language α} (h : IsStarFree L) : L.IsRegular := by
  induction h with
  | zero => exact UAM.Kleene.isRegular_zero
  | one => exact UAM.Kleene.isRegular_one
  | char a => exact UAM.Kleene.isRegular_singleton a
  | compl _ ih => exact Language.IsRegular.compl ih
  | add _ _ ihL ihM => exact Language.IsRegular.add ihL ihM
  | mul _ _ ihL ihM => exact UAM.Kleene.isRegular_mul ihL ihM

/-- **Every star-free language is noncounting.** -/
theorem IsStarFree.noncounting {L : Language α} (h : IsStarFree L) : ∃ n, Noncounting L n := by
  induction h with
  | zero => exact ⟨1, noncounting_zero⟩
  | one => exact ⟨1, noncounting_one⟩
  | char a => exact ⟨2, noncounting_singleton a⟩
  | compl _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n, noncounting_compl hn⟩
  | add _ _ ihL ihM =>
    obtain ⟨n, hn⟩ := ihL
    obtain ⟨m, hm⟩ := ihM
    exact ⟨max n m, noncounting_add (noncounting_mono hn (le_max_left n m))
      (noncounting_mono hm (le_max_right n m))⟩
  | mul _ _ ihL ihM =>
    obtain ⟨n, hn⟩ := ihL
    obtain ⟨m, hm⟩ := ihM
    exact ⟨2 * max n m + 1, noncounting_mul (noncounting_mono hn (le_max_left n m))
      (noncounting_mono hm (le_max_right n m))⟩

/-- **The syntactic monoid of a star-free language is aperiodic.**  This is the
easy half of Schützenberger's theorem. -/
theorem IsStarFree.aperiodic {L : Language α} (h : IsStarFree L) [Finite (SyntacticMonoid L)] :
    Aperiodic (SyntacticMonoid L) :=
  (noncounting_iff_aperiodic L).1 h.noncounting

/-! ## The parity language is regular but not star-free -/

/-- A two-state automaton toggling on every letter. -/
def parityDFA : DFA Unit Bool where
  step b _ := !b
  start := false
  accept := {false}

/-- Words of even length over a one-letter alphabet. -/
def parityLang : Language Unit := {w | Even w.length}

theorem parityDFA_evalFrom (w : List Unit) (b : Bool) :
    parityDFA.evalFrom b w = if Even w.length then b else !b := by
  induction w generalizing b with
  | nil => simp [DFA.evalFrom]
  | cons a w ih =>
    have hstep : parityDFA.evalFrom b (a :: w) = parityDFA.evalFrom (!b) w := rfl
    rw [hstep, ih, List.length_cons]
    by_cases h : Even w.length <;> simp [h, Nat.even_add_one]

theorem parityDFA_accepts : parityDFA.accepts = parityLang := by
  ext w
  have h1 : w ∈ parityDFA.accepts ↔ parityDFA.evalFrom false w = false := Iff.rfl
  have h2 : w ∈ parityLang ↔ Even w.length := Iff.rfl
  rw [h1, h2, parityDFA_evalFrom]
  by_cases h : Even w.length <;> simp [h]

theorem parityLang_isRegular : parityLang.IsRegular :=
  ⟨Bool, inferInstance, parityDFA, parityDFA_accepts⟩

theorem parityLang_not_noncounting : ¬ ∃ n, Noncounting parityLang n := by
  rintro ⟨n, hn⟩
  have h := hn (FreeMonoid.of ()) 1 1
  have hlen : ∀ m : ℕ, ((1 : FreeMonoid Unit) * (FreeMonoid.of ()) ^ m * 1).toList.length = m := by
    intro m
    rw [mul_one, one_mul, length_pow]
    simp
  have hmem : ∀ m : ℕ,
      ((1 : FreeMonoid Unit) * (FreeMonoid.of ()) ^ m * 1).toList ∈ parityLang ↔ Even m := by
    intro m
    show Even _ ↔ Even m
    rw [hlen m]
  rw [hmem n, hmem (n + 1), Nat.even_add_one] at h
  tauto

/-- **The parity language is regular but not star-free**, so the star-free
languages form a proper subclass of the regular languages. -/
theorem parityLang_not_starFree : ¬ IsStarFree parityLang := fun h =>
  parityLang_not_noncounting h.noncounting

theorem exists_regular_not_starFree :
    ∃ L : Language Unit, L.IsRegular ∧ ¬ IsStarFree L :=
  ⟨parityLang, parityLang_isRegular, parityLang_not_starFree⟩

end UAM.StarFree
