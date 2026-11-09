import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Directionality: left and right structure of words

Words carry two dual "directions": the *prefix* (left) direction and the
*suffix* (right) direction, exchanged by reversal.  This module develops the
elementary theory of these directions:

* `UAM.Directionality.wpow` — the `n`-th power of a word, with the arithmetic
  laws `wpow_add`, `wpow_length` and `wpow_comm`;
* `UAM.Directionality.commute_iff_wpow` — the Lyndon–Schützenberger
  commutation theorem: two words commute exactly when both are powers of a
  common word;
* `UAM.Directionality.Conjugate` — conjugacy of words (`x = uv`, `y = vu`),
  shown to be an equivalence relation preserving length;
* the reversal duality `isSuffix_reverse_iff` between the two directions.
-/

namespace UAM.Directionality

universe u

variable {α : Type u}

/-! ## Powers of a word -/

/-- The `n`-fold concatenation of a word with itself. -/
def wpow (z : List α) : ℕ → List α
  | 0 => []
  | n + 1 => z ++ wpow z n

@[simp] theorem wpow_zero (z : List α) : wpow z 0 = [] := rfl

@[simp] theorem wpow_succ (z : List α) (n : ℕ) : wpow z (n + 1) = z ++ wpow z n := rfl

@[simp] theorem wpow_one (z : List α) : wpow z 1 = z := by simp [wpow]

@[simp] theorem wpow_nil (n : ℕ) : wpow ([] : List α) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wpow, ih]

theorem wpow_add (z : List α) (m n : ℕ) : wpow z (m + n) = wpow z m ++ wpow z n := by
  induction m with
  | zero => simp
  | succ m ih => simp [wpow, ih, Nat.succ_add, List.append_assoc]

theorem wpow_length (z : List α) (n : ℕ) : (wpow z n).length = n * z.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [wpow, ih, Nat.succ_mul, Nat.add_comm]

/-- Powers of a fixed word commute with one another. -/
theorem wpow_comm (z : List α) (m n : ℕ) :
    wpow z m ++ wpow z n = wpow z n ++ wpow z m := by
  rw [← wpow_add, ← wpow_add, Nat.add_comm]

theorem wpow_eq_nil_iff {z : List α} {n : ℕ} :
    wpow z n = [] ↔ z = [] ∨ n = 0 := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inr hn
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simp [wpow] at h
      exact Or.inl h.1
  · rintro (rfl | rfl) <;> simp

/-! ## The commutation theorem -/

private theorem commute_aux :
    ∀ N : ℕ, ∀ x y : List α, x.length + y.length ≤ N → x ++ y = y ++ x →
      ∃ (z : List α) (m n : ℕ), x = wpow z m ∧ y = wpow z n := by
  intro N
  induction N with
  | zero =>
    intro x y hlen _
    have hx : x = [] := List.length_eq_zero_iff.1 (by omega)
    have hy : y = [] := List.length_eq_zero_iff.1 (by omega)
    exact ⟨[], 0, 0, by simp [hx], by simp [hy]⟩
  | succ N ih =>
    intro x y hlen hxy
    rcases eq_or_ne x [] with rfl | hx
    · exact ⟨y, 0, 1, by simp, by simp⟩
    rcases eq_or_ne y [] with rfl | hy
    · exact ⟨x, 1, 0, by simp, by simp⟩
    have hxpos : 0 < x.length := List.length_pos_iff.2 hx
    have hypos : 0 < y.length := List.length_pos_iff.2 hy
    rcases List.append_eq_append_iff.1 hxy with ⟨as, hy1, hy2⟩ | ⟨bs, hx1, hx2⟩
    · -- `y = x ++ as` and `y = as ++ x`, so `x` and `as` commute
      have hcomm : x ++ as = as ++ x := by rw [← hy1, ← hy2]
      have hlen' : x.length + as.length ≤ N := by
        have : y.length = x.length + as.length := by rw [hy1]; simp
        omega
      obtain ⟨z, m, n, hxz, hasz⟩ := ih x as hlen' hcomm
      exact ⟨z, m, m + n, hxz, by rw [hy1, wpow_add, hxz, hasz]⟩
    · -- `x = y ++ bs` and `x = bs ++ y`, so `y` and `bs` commute
      have hcomm : y ++ bs = bs ++ y := by rw [← hx1, ← hx2]
      have hlen' : y.length + bs.length ≤ N := by
        have : x.length = y.length + bs.length := by rw [hx1]; simp
        omega
      obtain ⟨z, m, n, hyz, hbsz⟩ := ih y bs hlen' hcomm
      exact ⟨z, m + n, m, by rw [hx1, wpow_add, hyz, hbsz], hyz⟩

/-- **Lyndon–Schützenberger.**  Two words commute if and only if they are
powers of one and the same word. -/
theorem commute_iff_wpow (x y : List α) :
    x ++ y = y ++ x ↔ ∃ (z : List α) (m n : ℕ), x = wpow z m ∧ y = wpow z n := by
  constructor
  · intro h
    exact commute_aux (x.length + y.length) x y le_rfl h
  · rintro ⟨z, m, n, rfl, rfl⟩
    exact wpow_comm z m n

/-- A word commutes with all its own powers. -/
theorem commute_wpow_self (x : List α) (n : ℕ) : x ++ wpow x n = wpow x n ++ x := by
  have := wpow_comm x 1 n
  simpa using this

/-! ## Conjugacy -/

/-- Two words are conjugate when one is a cyclic rotation of the other. -/
def Conjugate (x y : List α) : Prop := ∃ u v : List α, x = u ++ v ∧ y = v ++ u

theorem conjugate_refl (x : List α) : Conjugate x x := ⟨[], x, by simp, by simp⟩

theorem conjugate_symm {x y : List α} (h : Conjugate x y) : Conjugate y x := by
  obtain ⟨u, v, rfl, rfl⟩ := h
  exact ⟨v, u, rfl, rfl⟩

theorem conjugate_length {x y : List α} (h : Conjugate x y) : x.length = y.length := by
  obtain ⟨u, v, rfl, rfl⟩ := h
  simp [Nat.add_comm]

/-- Conjugate words satisfy the classical equation `x u = u y`. -/
theorem exists_conjugator {x y : List α} (h : Conjugate x y) :
    ∃ u : List α, x ++ u = u ++ y := by
  obtain ⟨u, v, rfl, rfl⟩ := h
  exact ⟨u, by simp⟩

theorem conjugate_trans {x y w : List α} (h₁ : Conjugate x y) (h₂ : Conjugate y w) :
    Conjugate x w := by
  obtain ⟨u, v, rfl, rfl⟩ := h₁
  obtain ⟨p, q, hy, rfl⟩ := h₂
  -- `v ++ u = p ++ q`; split according to where the cut falls
  rcases List.append_eq_append_iff.1 hy with ⟨as, hp, hu⟩ | ⟨bs, hv, hq⟩
  · exact ⟨as, q ++ v, by simp [hu], by simp [hp]⟩
  · exact ⟨u ++ p, bs, by simp [hv], by simp [hq]⟩

/-- Conjugacy is an equivalence relation on words. -/
theorem conjugate_equivalence : Equivalence (@Conjugate α) :=
  ⟨conjugate_refl, conjugate_symm, conjugate_trans⟩

/-! ## Reversal exchanges the two directions -/

theorem isSuffix_reverse_iff (x y : List α) :
    x.reverse <:+ y.reverse ↔ x <+: y := List.reverse_suffix

theorem isPrefix_reverse_iff (x y : List α) :
    x.reverse <+: y.reverse ↔ x <:+ y := List.reverse_prefix

/-- A word that is a prefix of another and at least as long is equal to it. -/
theorem eq_of_isPrefix_of_length_le {x y : List α} (h : x <+: y) (hlen : y.length ≤ x.length) :
    x = y := by
  obtain ⟨t, rfl⟩ := h
  rw [List.length_append] at hlen
  have ht : t = [] := List.length_eq_zero_iff.1 (by omega)
  simp [ht]

/-- The prefix relation is antisymmetric: the two directions cannot disagree. -/
theorem isPrefix_antisymm {x y : List α} (h₁ : x <+: y) (h₂ : y <+: x) : x = y :=
  eq_of_isPrefix_of_length_le h₁ h₂.length_le

/-- Of two prefixes of a common word, one is a prefix of the other:
the left direction is linearly ordered. -/
theorem isPrefix_total {x y w : List α} (h₁ : x <+: w) (h₂ : y <+: w) :
    x <+: y ∨ y <+: x :=
  List.prefix_or_prefix_of_prefix h₁ h₂

end UAM.Directionality
