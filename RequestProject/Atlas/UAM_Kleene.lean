import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Closure of the regular languages under concatenation and Kleene star

Mathlib proves that regular languages are closed under union, intersection and
complement, and characterises regularity by finiteness of the set of left
quotients.  This module adds the two missing Kleene operations:

* `UAM.Kleene.isRegular_mul` — regular languages are closed under concatenation;
* `UAM.Kleene.isRegular_kstar` — regular languages are closed under Kleene star.

Both are proved by the derivative (left-quotient) method: every left quotient of
`L * M`, respectively of `L∗`, is reconstructed from finitely much data built out
of left quotients of `L` and of `M`, so the set of left quotients stays finite.

Combining the two with Mathlib's union closure gives Kleene's theorem in the
direction *every regular expression denotes a regular language*
(`UAM.Kleene.isRegular_matches'`).
-/

namespace UAM.Kleene

open scoped Computability

universe u

variable {α : Type u}

/-! ## Concatenation -/

/-- The finite data determining the left quotient of `L * M` by a word: the left
quotient of `L`, together with the set of left quotients of `M` by the suffixes
whose complementary prefix lies in `L`. -/
def mulData (L M : Language α) (w : List α) : Language α × Set (Language α) :=
  (L.leftQuotient w, {t | ∃ p s : List α, w = p ++ s ∧ p ∈ L ∧ t = M.leftQuotient s})

/-- Reconstruction of the left quotient of `L * M` from `mulData`. -/
def mulRebuild (M : Language α) (d : Language α × Set (Language α)) : Language α :=
  {y | y ∈ d.1 * M ∨ ∃ t ∈ d.2, y ∈ t}

/-- Brzozowski-style derivative formula for a concatenation. -/
theorem leftQuotient_mul (L M : Language α) (w : List α) :
    (L * M).leftQuotient w = mulRebuild M (mulData L M w) := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    have hy' : w ++ y ∈ L * M := (Language.mem_leftQuotient w y).1 hy
    obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.1 hy'
    rcases List.append_eq_append_iff.1 hab with ⟨c, hw, hb'⟩ | ⟨c, ha', hy'⟩
    · refine Or.inr ⟨M.leftQuotient c, ⟨a, c, hw, ha, rfl⟩, ?_⟩
      exact (Language.mem_leftQuotient c y).2 (by rw [← hb']; exact hb)
    · refine Or.inl (Language.mem_mul.2 ⟨c, ?_, b, hb, hy'.symm⟩)
      exact (Language.mem_leftQuotient w c).2 (by rw [← ha']; exact ha)
  · intro hy
    refine (Language.mem_leftQuotient w y).2 ?_
    rcases hy with hy | ⟨t, ⟨p, s, hw, hp, rfl⟩, hyt⟩
    · obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.1 hy
      have haL : w ++ a ∈ L := (Language.mem_leftQuotient w a).1 ha
      refine Language.mem_mul.2 ⟨w ++ a, haL, b, hb, ?_⟩
      rw [List.append_assoc, hab]
    · have hs : s ++ y ∈ M := (Language.mem_leftQuotient s y).1 hyt
      refine Language.mem_mul.2 ⟨p, hp, s ++ y, hs, ?_⟩
      rw [← List.append_assoc, ← hw]

theorem range_mulData_subset (L M : Language α) :
    Set.range (mulData L M) ⊆
      (Set.range L.leftQuotient) ×ˢ {S : Set (Language α) | S ⊆ Set.range M.leftQuotient} := by
  rintro _ ⟨w, rfl⟩
  refine ⟨⟨w, rfl⟩, ?_⟩
  rintro t ⟨p, s, -, -, rfl⟩
  exact ⟨s, rfl⟩

/-- **Regular languages are closed under concatenation.** -/
theorem isRegular_mul {L M : Language α} (hL : L.IsRegular) (hM : M.IsRegular) :
    (L * M).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hfin : (Set.range (mulData L M)).Finite :=
    Set.Finite.subset
      (Set.Finite.prod hL.finite_range_leftQuotient
        (Set.Finite.finite_subsets hM.finite_range_leftQuotient))
      (range_mulData_subset L M)
  refine Set.Finite.subset (Set.Finite.image (mulRebuild M) hfin) ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨mulData L M w, ⟨w, rfl⟩, (leftQuotient_mul L M w).symm⟩

/-! ## Kleene star -/

/-- Prefixing a word of `L` to a word of `L∗` stays in `L∗`. -/
theorem cons_mem_kstar {L : Language α} {x y : List α} (hx : x ∈ L) (hy : y ∈ L∗) :
    x ++ y ∈ L∗ := by
  obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 hy
  refine Language.mem_kstar.2 ⟨x :: S, by simp, ?_⟩
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hx
  · exact hS z hz

/-- `L∗` is closed under concatenation. -/
theorem append_mem_kstar {L : Language α} {x y : List α} (hx : x ∈ L∗) (hy : y ∈ L∗) :
    x ++ y ∈ L∗ := by
  obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.1 hx
  obtain ⟨T, rfl, hT⟩ := Language.mem_kstar.1 hy
  refine Language.mem_kstar.2 ⟨S ++ T, by simp, ?_⟩
  intro z hz
  rcases List.mem_append.1 hz with h | h
  · exact hS z h
  · exact hT z h

/-- The finite data determining the left quotient of `L∗` by a word: whether the
word itself lies in `L∗`, together with the set of left quotients of `L` by the
suffixes whose complementary prefix lies in `L∗`. -/
def starData (L : Language α) (w : List α) : Prop × Set (Language α) :=
  (w ∈ L∗, {t | ∃ p a : List α, w = p ++ a ∧ p ∈ L∗ ∧ t = L.leftQuotient a})

/-- Reconstruction of the left quotient of `L∗` from `starData`. -/
def starRebuild (L : Language α) (d : Prop × Set (Language α)) : Language α :=
  {y | (d.1 ∧ y ∈ L∗) ∨ ∃ t ∈ d.2, y ∈ t * L∗}

/-- Splitting a factorisation of `w ++ y` into words of `L`: either the split
point falls at a factor boundary, or it falls strictly inside a factor, in which
case `y` starts with the remainder of that factor. -/
private theorem star_split (L : Language α) (S : List (List α)) (hS : ∀ z ∈ S, z ∈ L)
    (w y : List α) (hwy : w ++ y = S.flatten) :
    (w ∈ L∗ ∧ y ∈ L∗) ∨
      ∃ p a : List α, w = p ++ a ∧ p ∈ L∗ ∧ y ∈ (L.leftQuotient a) * L∗ := by
  induction S generalizing w with
  | nil =>
    have h0 : w ++ y = [] := by simpa using hwy
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h0
    exact Or.inl ⟨Language.nil_mem_kstar L, Language.nil_mem_kstar L⟩
  | cons f T ih =>
    have hf : f ∈ L := hS f (List.mem_cons_self ..)
    have hT : ∀ z ∈ T, z ∈ L := fun z hz => hS z (List.mem_cons_of_mem _ hz)
    have hflat : w ++ y = f ++ T.flatten := by simpa using hwy
    rcases List.append_eq_append_iff.1 hflat with ⟨c, hf', hy'⟩ | ⟨c, hw', hT'⟩
    · refine Or.inr ⟨[], w, by simp, Language.nil_mem_kstar L, ?_⟩
      refine Language.mem_mul.2 ⟨c, ?_, T.flatten, ?_, hy'.symm⟩
      · exact (Language.mem_leftQuotient w c).2 (by rw [← hf']; exact hf)
      · exact Language.mem_kstar.2 ⟨T, rfl, hT⟩
    · rcases ih hT c hT'.symm with ⟨hc, hy⟩ | ⟨p, a, hca, hp, hy⟩
      · refine Or.inl ⟨?_, hy⟩
        rw [hw']
        exact cons_mem_kstar hf hc
      · refine Or.inr ⟨f ++ p, a, ?_, ?_, hy⟩
        · rw [hw', hca, List.append_assoc]
        · exact cons_mem_kstar hf hp

/-- Brzozowski-style derivative formula for a Kleene star. -/
theorem leftQuotient_kstar (L : Language α) (w : List α) :
    (L∗).leftQuotient w = starRebuild L (starData L w) := by
  apply Set.ext
  intro y
  constructor
  · intro hy
    have hmem : w ++ y ∈ L∗ := (Language.mem_leftQuotient w y).1 hy
    obtain ⟨S, hS, hSL⟩ := Language.mem_kstar.1 hmem
    rcases star_split L S hSL w y hS with ⟨hw, hy'⟩ | ⟨p, a, hpa, hp, hy'⟩
    · exact Or.inl ⟨hw, hy'⟩
    · exact Or.inr ⟨L.leftQuotient a, ⟨p, a, hpa, hp, rfl⟩, hy'⟩
  · intro hy
    refine (Language.mem_leftQuotient w y).2 ?_
    rcases hy with ⟨hw, hy⟩ | ⟨t, ⟨p, a, hpa, hp, rfl⟩, hy⟩
    · exact append_mem_kstar hw hy
    · obtain ⟨b, hb, c, hc, hbc⟩ := Language.mem_mul.1 hy
      have hab : a ++ b ∈ L := (Language.mem_leftQuotient a b).1 hb
      rw [hpa, ← hbc, List.append_assoc, ← List.append_assoc a b c]
      exact append_mem_kstar hp (cons_mem_kstar hab hc)

theorem range_starData_subset (L : Language α) :
    Set.range (starData L) ⊆
      (Set.univ : Set Prop) ×ˢ {S : Set (Language α) | S ⊆ Set.range L.leftQuotient} := by
  rintro _ ⟨w, rfl⟩
  refine ⟨Set.mem_univ _, ?_⟩
  rintro t ⟨p, a, -, -, rfl⟩
  exact ⟨a, rfl⟩

/-- **Regular languages are closed under Kleene star.** -/
theorem isRegular_kstar {L : Language α} (hL : L.IsRegular) : (L∗).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hfin : (Set.range (starData L)).Finite :=
    Set.Finite.subset
      (Set.Finite.prod Set.finite_univ
        (Set.Finite.finite_subsets hL.finite_range_leftQuotient))
      (range_starData_subset L)
  refine Set.Finite.subset (Set.Finite.image (starRebuild L) hfin) ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨starData L w, ⟨w, rfl⟩, (leftQuotient_kstar L w).symm⟩

/-! ## Kleene's theorem: regular expressions denote regular languages -/

private theorem mem_singleton_language (a x : List α) :
    x ∈ ({a} : Language α) ↔ x = a := Iff.rfl

theorem isRegular_zero : (0 : Language α).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hsub : Set.range (0 : Language α).leftQuotient ⊆ {0} := by
    rintro _ ⟨w, rfl⟩
    ext y
    simp [Language.mem_leftQuotient]
  exact Set.Finite.subset (Set.finite_singleton _) hsub

theorem isRegular_one : (1 : Language α).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hsub : Set.range (1 : Language α).leftQuotient ⊆ {1, 0} := by
    rintro _ ⟨w, rfl⟩
    rcases eq_or_ne w [] with rfl | hw
    · left; ext y; simp
    · right; ext y
      simp [Language.mem_leftQuotient, Language.mem_one, hw]
  exact Set.Finite.subset (Set.toFinite _) hsub

theorem isRegular_singleton (a : α) : ({[a]} : Language α).IsRegular := by
  classical
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  have hsub : Set.range ({[a]} : Language α).leftQuotient ⊆ {{[a]}, 1, 0} := by
    rintro _ ⟨w, rfl⟩
    match w with
    | [] => exact Or.inl (by ext y; simp)
    | [b] =>
      rcases eq_or_ne b a with rfl | hb
      · refine Or.inr (Or.inl ?_)
        ext y
        simp [Language.mem_leftQuotient, mem_singleton_language, Language.mem_one]
      · refine Or.inr (Or.inr ?_)
        ext y
        simp [Language.mem_leftQuotient, mem_singleton_language, hb]
    | b :: c :: t =>
      refine Or.inr (Or.inr ?_)
      ext y
      simp [Language.mem_leftQuotient, mem_singleton_language]
  exact Set.Finite.subset (Set.toFinite _) hsub

/-- **Kleene's theorem (one direction).**  The language denoted by a regular
expression is a regular language. -/
theorem isRegular_matches' (P : RegularExpression α) : P.matches'.IsRegular := by
  induction P with
  | zero => exact isRegular_zero
  | epsilon => exact isRegular_one
  | char a => exact isRegular_singleton a
  | plus P Q ihP ihQ => exact Language.IsRegular.add ihP ihQ
  | comp P Q ihP ihQ => exact isRegular_mul ihP ihQ
  | star P ihP => exact isRegular_kstar ihP

end UAM.Kleene
