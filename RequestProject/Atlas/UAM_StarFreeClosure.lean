import RequestProject.Atlas.UAM_StarFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Closure properties of the star-free languages

The inductive definition `UAM.StarFree.IsStarFree` lists only union, complement
and concatenation.  This module derives the remaining boolean operations and a
few further closure properties:

* `isStarFree_univ`, `isStarFree_inter`, `isStarFree_sdiff`;
* `isStarFree_singleton`, `isStarFree_of_finite` — every finite language is
  star-free;
* `isStarFree_reverse` — the class is closed under reversal;
* `isStarFree_leftQuotient` — the class is closed under left quotients by a
  word, computed with the usual derivative rules;
* `isStarFree_rightQuotient` — and, by reversal, under right quotients.
-/

namespace UAM.StarFree

variable {α : Type}

/-! ## Boolean operations -/

theorem isStarFree_univ : IsStarFree (Set.univ : Language α) := by
  have h : (Set.univ : Language α) = (0 : Language α)ᶜ := by
    ext w
    simp only [Set.mem_univ, true_iff]
    exact fun hw => hw
  rw [h]
  exact IsStarFree.compl IsStarFree.zero

theorem isStarFree_inter {L M : Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L ⊓ M) := by
  have h : L ⊓ M = (Lᶜ + Mᶜ)ᶜ := by
    rw [Language.add_def]
    ext w
    constructor
    · rintro ⟨h1, h2⟩ (hc | hc)
      · exact hc h1
      · exact hc h2
    · intro hc
      exact ⟨not_not.1 fun hn => hc (Or.inl hn), not_not.1 fun hn => hc (Or.inr hn)⟩
  rw [h]
  exact IsStarFree.compl (IsStarFree.add (IsStarFree.compl hL) (IsStarFree.compl hM))

theorem isStarFree_sdiff {L M : Language α} (hL : IsStarFree L) (hM : IsStarFree M) :
    IsStarFree (L \ M) := by
  have h : L \ M = L ⊓ Mᶜ := by ext w; exact Iff.rfl
  rw [h]
  exact isStarFree_inter hL (IsStarFree.compl hM)

/-! ## Finite languages -/

theorem isStarFree_singleton (w : List α) : IsStarFree ({w} : Language α) := by
  induction w with
  | nil =>
    have h : ({([] : List α)} : Language α) = 1 := by
      ext v
      exact Set.mem_singleton_iff.trans (Language.mem_one v).symm
    rw [h]
    exact IsStarFree.one
  | cons a w ih =>
    have h : ({a :: w} : Language α) = {[a]} * {w} := by
      ext v
      rw [Language.mem_mul]
      constructor
      · intro hv
        have hv' : v = a :: w := hv
        exact ⟨[a], rfl, w, rfl, hv'.symm⟩
      · rintro ⟨u, hu, x, hx, rfl⟩
        have hu' : u = [a] := hu
        have hx' : x = w := hx
        show u ++ x = a :: w
        rw [hu', hx']
        rfl
    rw [h]
    exact IsStarFree.mul (IsStarFree.char a) ih

theorem isStarFree_of_finite {L : Language α} (h : L.Finite) : IsStarFree L := by
  induction L, h using Set.Finite.induction_on with
  | empty => exact IsStarFree.zero
  | @insert w s _ _ ih =>
    have hins : (insert w s : Set (List α))
        = (({w} : Language α) + (show Language α from s) : Language α) := by
      rw [Language.add_def]
      ext v
      exact Set.mem_insert_iff.trans (or_congr Set.mem_singleton_iff.symm Iff.rfl)
    rw [hins]
    exact IsStarFree.add (isStarFree_singleton w) ih

/-! ## Reversal -/

theorem reverse_compl (L : Language α) : (Lᶜ).reverse = (L.reverse)ᶜ := by
  ext w
  exact Iff.rfl

theorem reverse_singleton (a : α) : ({[a]} : Language α).reverse = {[a]} := by
  ext w
  constructor
  · intro h
    have hw : w.reverse = [a] := h
    have := congrArg List.reverse hw
    simpa using this
  · intro h
    have hw : w = [a] := h
    show w.reverse = [a]
    rw [hw]
    rfl

theorem reverse_zero : (0 : Language α).reverse = 0 := by
  ext w
  exact Iff.rfl

theorem reverse_one : (1 : Language α).reverse = 1 := by
  ext w
  constructor
  · intro h
    have hw : w.reverse = [] := h
    have := congrArg List.reverse hw
    simpa using this
  · intro h
    have hw : w = [] := h
    show w.reverse = []
    rw [hw]
    rfl

theorem isStarFree_reverse {L : Language α} (h : IsStarFree L) : IsStarFree L.reverse := by
  induction h with
  | zero => rw [reverse_zero]; exact IsStarFree.zero
  | one => rw [reverse_one]; exact IsStarFree.one
  | char a => rw [reverse_singleton a]; exact IsStarFree.char a
  | compl _ ih => rw [reverse_compl]; exact IsStarFree.compl ih
  | add _ _ ihL ihM => rw [Language.reverse_add]; exact IsStarFree.add ihL ihM
  | mul _ _ ihL ihM => rw [Language.reverse_mul]; exact IsStarFree.mul ihM ihL

/-! ## Left quotients -/

theorem leftQuotient_compl (L : Language α) (x : List α) :
    (Lᶜ).leftQuotient x = (L.leftQuotient x)ᶜ := by
  ext y
  exact Iff.rfl

theorem leftQuotient_add (L M : Language α) (x : List α) :
    (L + M).leftQuotient x = L.leftQuotient x + M.leftQuotient x := by
  ext y
  exact Iff.rfl

/-- The derivative of a product.  The factor `1 ⊓ L` is `{ε}` when `L` contains
the empty word and `∅` otherwise, which avoids a decidability assumption. -/
theorem leftQuotient_mul_cons (L M : Language α) (a : α) :
    (L * M).leftQuotient [a]
      = (L.leftQuotient [a]) * M + (1 ⊓ L) * (M.leftQuotient [a]) := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_add, Language.mem_mul, Language.mem_mul,
    Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    obtain _ | ⟨b, u'⟩ := u
    · have hv' : v = a :: y := by simpa using huv
      subst hv'
      refine Or.inr ⟨[], ⟨(Language.mem_one _).2 rfl, hu⟩, y, ?_, rfl⟩
      rw [Language.mem_leftQuotient]
      simpa using hv
    · have hb : b = a := by simpa using congrArg (fun l => l.head?) huv
      subst hb
      have hy : u' ++ v = y := by simpa using huv
      refine Or.inl ⟨u', ?_, v, hv, hy⟩
      rw [Language.mem_leftQuotient]
      simpa using hu
  · rintro (⟨u, hu, v, hv, rfl⟩ | ⟨u, ⟨hu1, hu2⟩, v, hv, rfl⟩)
    · rw [Language.mem_leftQuotient] at hu
      exact ⟨a :: u, by simpa using hu, v, hv, rfl⟩
    · have hu' : u = [] := (Language.mem_one _).1 hu1
      subst hu'
      rw [Language.mem_leftQuotient] at hv
      exact ⟨[], hu2, a :: v, by simpa using hv, rfl⟩

theorem leftQuotient_zero_cons (a : α) : ((0 : Language α)).leftQuotient [a] = 0 := by
  ext y
  exact Iff.rfl

theorem leftQuotient_one_cons (a : α) : ((1 : Language α)).leftQuotient [a] = 0 := by
  ext y
  constructor
  · intro h
    have h' : a :: y = [] := (Language.mem_one _).1 h
    exact absurd h' (by simp)
  · intro h
    exact absurd h (Set.notMem_empty _)

theorem leftQuotient_char_self (a : α) : ({[a]} : Language α).leftQuotient [a] = 1 := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_one]
  constructor
  · intro h
    have h' : [a] ++ y = [a] := h
    simpa using h'
  · intro h
    show [a] ++ y = [a]
    rw [h]
    rfl

theorem leftQuotient_char_ne {a b : α} (hab : a ≠ b) :
    ({[b]} : Language α).leftQuotient [a] = 0 := by
  ext y
  constructor
  · intro h
    have h' : [a] ++ y = [b] := h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h'
    exact absurd h'.1 hab
  · intro h
    exact absurd h (Set.notMem_empty _)

/-- **The star-free languages are closed under left quotient by a letter.** -/
theorem isStarFree_leftQuotient_cons {L : Language α} (h : IsStarFree L) (a : α) :
    IsStarFree (L.leftQuotient [a]) := by
  induction h with
  | zero => rw [leftQuotient_zero_cons]; exact IsStarFree.zero
  | one => rw [leftQuotient_one_cons]; exact IsStarFree.zero
  | char b =>
    by_cases hab : a = b
    · subst hab
      rw [leftQuotient_char_self]
      exact IsStarFree.one
    · rw [leftQuotient_char_ne hab]
      exact IsStarFree.zero
  | compl _ ih => rw [leftQuotient_compl]; exact IsStarFree.compl ih
  | add _ _ ihL ihM => rw [leftQuotient_add]; exact IsStarFree.add ihL ihM
  | mul hL hM ihL ihM =>
    rw [leftQuotient_mul_cons]
    exact IsStarFree.add (IsStarFree.mul ihL hM)
      (IsStarFree.mul (isStarFree_inter IsStarFree.one hL) ihM)

/-- **The star-free languages are closed under left quotient by a word.** -/
theorem isStarFree_leftQuotient {L : Language α} (h : IsStarFree L) (x : List α) :
    IsStarFree (L.leftQuotient x) := by
  induction x generalizing L with
  | nil =>
    have h0 : L.leftQuotient [] = L := by ext y; exact Iff.rfl
    rw [h0]
    exact h
  | cons a x ih =>
    have hsplit : L.leftQuotient (a :: x) = (L.leftQuotient [a]).leftQuotient x := by
      ext y
      rw [Language.mem_leftQuotient, Language.mem_leftQuotient, Language.mem_leftQuotient]
      simp
    rw [hsplit]
    exact ih (isStarFree_leftQuotient_cons h a)

/-! ## Right quotients -/

/-- The right quotient of `L` by a word `x` is the reversal of a left quotient
of the reversal of `L`. -/
theorem rightQuotient_eq (L : Language α) (x : List α) :
    {w : List α | w ++ x ∈ L} = ((L.reverse).leftQuotient x.reverse).reverse := by
  ext w
  show w ++ x ∈ L ↔ w.reverse ∈ (L.reverse).leftQuotient x.reverse
  rw [Language.mem_leftQuotient]
  show _ ↔ (x.reverse ++ w.reverse).reverse ∈ L
  rw [List.reverse_append, List.reverse_reverse, List.reverse_reverse]

/-- **The star-free languages are closed under right quotient by a word.** -/
theorem isStarFree_rightQuotient {L : Language α} (h : IsStarFree L) (x : List α) :
    IsStarFree {w : List α | w ++ x ∈ L} := by
  rw [rightQuotient_eq]
  exact isStarFree_reverse (isStarFree_leftQuotient (isStarFree_reverse h) x.reverse)

end UAM.StarFree
