import RequestProject.Atlas.UAM_StarFreeClosure
import RequestProject.Atlas.UAM_Unary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Schützenberger's theorem over a one-letter alphabet

`UAM.StarFree.IsStarFree.noncounting` gives the easy half of Schützenberger's
theorem: star-free languages are noncounting, hence have aperiodic syntactic
monoids.  The converse is hard in general, but over a *one-letter* alphabet it
is elementary, and this module proves it:

* `UAM.StarFree.finite_or_cofinite_of_noncounting` — a noncounting language over
  `Unit` is finite or cofinite, because the noncounting condition forces
  membership to be constant on all lengths above the noncounting exponent;
* `UAM.StarFree.isStarFree_of_finite_or_cofinite` — finite and cofinite
  languages are star-free (over an arbitrary alphabet);
* `UAM.StarFree.starFree_iff_noncounting_unary` and
  `UAM.StarFree.starFree_iff_finite_or_cofinite_unary` — over `Unit` the
  star-free languages are exactly the noncounting ones, exactly the languages
  that are finite or cofinite;
* `UAM.StarFree.starFree_iff_aperiodic_unary` — **Schützenberger's theorem for a
  one-letter alphabet**: a regular unary language is star-free exactly when its
  syntactic monoid is aperiodic.
-/

namespace UAM.StarFree

open UAM.Unary UAM.Syntactic UAM.Green

/-! ## Finite and cofinite languages are star-free -/

/-- The complement of a finite language is star-free. -/
theorem isStarFree_of_cofinite {α : Type} {L : Language α} (h : (Lᶜ : Language α).Finite) :
    IsStarFree L := by
  have hc := IsStarFree.compl (isStarFree_of_finite h)
  rwa [compl_compl] at hc

theorem isStarFree_of_finite_or_cofinite {α : Type} {L : Language α}
    (h : L.Finite ∨ (Lᶜ : Language α).Finite) : IsStarFree L :=
  h.elim isStarFree_of_finite isStarFree_of_cofinite

/-! ## Unary words as powers of the single letter -/

theorem toList_pow_of (k : ℕ) :
    ((FreeMonoid.of () : FreeMonoid Unit) ^ k).toList = unaryWord k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    show ((FreeMonoid.of () : FreeMonoid Unit) ^ k).toList ++ [()] = unaryWord (k + 1)
    rw [ih, unaryWord, unaryWord, List.replicate_succ']

/-- Over a one-letter alphabet there are only finitely many words of bounded
length. -/
theorem shortWords_finite (n : ℕ) : {w : List Unit | w.length < n}.Finite := by
  refine Set.Finite.subset ((Set.finite_lt_nat n).image unaryWord) ?_
  intro w hw
  exact ⟨w.length, hw, (eq_unaryWord w).symm⟩

/-! ## Noncounting unary languages are finite or cofinite -/

/-- Above the noncounting exponent, membership of a unary language cannot change
from one length to the next. -/
theorem mem_iff_succ_mem_of_noncounting {L : Language Unit} {n : ℕ} (h : Noncounting L n)
    {m : ℕ} (hm : n ≤ m) : unaryWord m ∈ L ↔ unaryWord (m + 1) ∈ L := by
  have hcat : ∀ k : ℕ, ((FreeMonoid.ofList (unaryWord (m - n)) : FreeMonoid Unit)
      * (FreeMonoid.of ()) ^ k * 1).toList = unaryWord (m - n + k) := by
    intro k
    rw [mul_one]
    show unaryWord (m - n) ++ ((FreeMonoid.of () : FreeMonoid Unit) ^ k).toList = _
    rw [toList_pow_of, unaryWord_add]
  have key := h (FreeMonoid.of ()) (FreeMonoid.ofList (unaryWord (m - n))) 1
  rw [hcat n, hcat (n + 1), show m - n + n = m by omega,
    show m - n + (n + 1) = m + 1 by omega] at key
  exact key

/-- **A noncounting language over a one-letter alphabet is finite or
cofinite.** -/
theorem finite_or_cofinite_of_noncounting {L : Language Unit} {n : ℕ} (h : Noncounting L n) :
    L.Finite ∨ (Lᶜ : Language Unit).Finite := by
  have stable : ∀ k : ℕ, (unaryWord (n + k) ∈ L ↔ unaryWord n ∈ L) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := mem_iff_succ_mem_of_noncounting h (m := n + k) (Nat.le_add_right n k)
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      exact hstep.symm.trans ih
  have stable' : ∀ m : ℕ, n ≤ m → (unaryWord m ∈ L ↔ unaryWord n ∈ L) := by
    intro m hm
    have := stable (m - n)
    rwa [show n + (m - n) = m by omega] at this
  by_cases hn : unaryWord n ∈ L
  · right
    refine Set.Finite.subset (shortWords_finite n) ?_
    intro w hw
    by_contra hlt
    have hge : n ≤ w.length := by
      simp only [Set.mem_setOf_eq, not_lt] at hlt
      exact hlt
    refine hw ?_
    rw [eq_unaryWord w]
    exact (stable' w.length hge).2 hn
  · left
    refine Set.Finite.subset (shortWords_finite n) ?_
    intro w hw
    by_contra hlt
    have hge : n ≤ w.length := by
      simp only [Set.mem_setOf_eq, not_lt] at hlt
      exact hlt
    refine hn ((stable' w.length hge).1 ?_)
    rw [← eq_unaryWord w]
    exact hw

/-! ## The characterisations -/

/-- Over a one-letter alphabet, noncounting languages are star-free. -/
theorem isStarFree_of_noncounting_unary {L : Language Unit} (h : ∃ n, Noncounting L n) :
    IsStarFree L := by
  obtain ⟨n, hn⟩ := h
  exact isStarFree_of_finite_or_cofinite (finite_or_cofinite_of_noncounting hn)

/-- **Over a one-letter alphabet the star-free languages are exactly the
noncounting ones.** -/
theorem starFree_iff_noncounting_unary (L : Language Unit) :
    IsStarFree L ↔ ∃ n, Noncounting L n :=
  ⟨IsStarFree.noncounting, isStarFree_of_noncounting_unary⟩

/-- **Over a one-letter alphabet the star-free languages are exactly the finite
and the cofinite ones.** -/
theorem starFree_iff_finite_or_cofinite_unary (L : Language Unit) :
    IsStarFree L ↔ (L.Finite ∨ (Lᶜ : Language Unit).Finite) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.noncounting
    exact finite_or_cofinite_of_noncounting hn
  · exact isStarFree_of_finite_or_cofinite

/-- **Schützenberger's theorem for a one-letter alphabet**: a regular unary
language is star-free exactly when its syntactic monoid is aperiodic. -/
theorem starFree_iff_aperiodic_unary (L : Language Unit) (hL : L.IsRegular) :
    IsStarFree L ↔ Aperiodic (SyntacticMonoid L) := by
  haveI : Finite (SyntacticMonoid L) := (isRegular_iff_finite_syntacticMonoid L).1 hL
  rw [starFree_iff_noncounting_unary, noncounting_iff_aperiodic L]

/-- Over a one-letter alphabet, star-freeness and `H`-triviality of the
syntactic monoid agree for regular languages. -/
theorem starFree_iff_hTrivial_unary (L : Language Unit) (hL : L.IsRegular) :
    IsStarFree L ↔ HTrivial (SyntacticMonoid L) := by
  haveI : Finite (SyntacticMonoid L) := (isRegular_iff_finite_syntacticMonoid L).1 hL
  rw [starFree_iff_aperiodic_unary L hL]
  exact aperiodic_iff_hTrivial

/-- The parity language is neither finite nor cofinite, which re-proves that it
is not star-free. -/
theorem parityLang_not_finite_or_cofinite :
    ¬ (parityLang.Finite ∨ (parityLangᶜ : Language Unit).Finite) := fun h =>
  parityLang_not_starFree (isStarFree_of_finite_or_cofinite h)

end UAM.StarFree
