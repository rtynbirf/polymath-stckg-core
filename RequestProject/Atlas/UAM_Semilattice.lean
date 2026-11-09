import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Idempotent commutative monoids are semilattices

An idempotent commutative monoid carries a canonical partial order,
`x ≼ y ↔ x * y = x`, for which the product is the greatest lower bound and the
unit is the top element.  Conversely, a meet-semilattice with a top element is
an idempotent commutative monoid under `⊓`.  This module makes the
correspondence precise:

* `UAM.Semilattice.Divides` — the canonical order of an idempotent monoid;
* `UAM.Semilattice.mul_isGLB` — the product is the greatest lower bound;
* `UAM.Semilattice.toSemilatticeInf` — the induced meet-semilattice;
* `UAM.Semilattice.ofSemilatticeInf` — the converse construction;
* `UAM.Semilattice.divides_eq_le` — the two constructions agree on the order.
-/

namespace UAM.Semilattice

universe u

variable {M : Type u} [CommMonoid M]

/-- The canonical order of an idempotent commutative monoid. -/
def Divides (x y : M) : Prop := x * y = x

theorem divides_trans {x y z : M} (hxy : Divides x y) (hyz : Divides y z) : Divides x z := by
  unfold Divides at *
  calc x * z = (x * y) * z := by rw [hxy]
    _ = x * (y * z) := by rw [mul_assoc]
    _ = x * y := by rw [hyz]
    _ = x := hxy

theorem divides_antisymm {x y : M} (hxy : Divides x y) (hyx : Divides y x) : x = y := by
  unfold Divides at *
  rw [← hxy, mul_comm, hyx]

theorem divides_one (x : M) : Divides x 1 := by simp [Divides]

/-- Anything below both factors is below their product: the product is the meet. -/
theorem divides_mul_of_divides {x y z : M} (hx : Divides z x) (hy : Divides z y) :
    Divides z (x * y) := by
  unfold Divides at *
  calc z * (x * y) = (z * x) * y := by rw [mul_assoc]
    _ = z * y := by rw [hx]
    _ = z := hy

section Idempotent

variable (hidem : ∀ x : M, x * x = x)

include hidem

theorem divides_refl (x : M) : Divides x x := hidem x

/-- The product is below each factor. -/
theorem mul_divides_left (x y : M) : Divides (x * y) x := by
  unfold Divides
  calc x * y * x = (x * x) * y := mul_right_comm x y x
    _ = x * y := by rw [hidem]

theorem mul_divides_right (x y : M) : Divides (x * y) y := by
  have := mul_divides_left hidem y x
  rwa [mul_comm y x] at this

/-- The product of an idempotent commutative monoid is the greatest lower bound
of its factors for the canonical order. -/
theorem mul_isGLB (x y : M) :
    Divides (x * y) x ∧ Divides (x * y) y ∧
      ∀ z : M, Divides z x → Divides z y → Divides z (x * y) :=
  ⟨mul_divides_left hidem x y, mul_divides_right hidem x y,
    fun _ hx hy => divides_mul_of_divides hx hy⟩

/-- An idempotent commutative monoid is a meet-semilattice with top element `1`. -/
def toSemilatticeInf : SemilatticeInf M where
  le x y := Divides x y
  le_refl := divides_refl hidem
  le_trans _ _ _ := divides_trans
  le_antisymm _ _ := divides_antisymm
  inf x y := x * y
  inf_le_left := mul_divides_left hidem
  inf_le_right := mul_divides_right hidem
  le_inf _ _ _ := divides_mul_of_divides

theorem toSemilatticeInf_le (x y : M) :
    (toSemilatticeInf hidem).le x y ↔ Divides x y := Iff.rfl

theorem toSemilatticeInf_inf (x y : M) :
    (toSemilatticeInf hidem).inf x y = x * y := rfl

/-- The unit is the greatest element. -/
theorem divides_one_top (x : M) : (toSemilatticeInf hidem).le x 1 := divides_one x

end Idempotent

/-! ## The converse construction -/

section OfLattice

variable {L : Type u} [SemilatticeInf L] [OrderTop L]

/-- A meet-semilattice with a top element is a commutative monoid under `⊓`. -/
def ofSemilatticeInf : CommMonoid L where
  mul x y := x ⊓ y
  mul_assoc _ _ _ := inf_assoc _ _ _
  one := ⊤
  one_mul _ := top_inf_eq _
  mul_one _ := inf_top_eq _
  mul_comm _ _ := inf_comm _ _

theorem ofSemilatticeInf_mul (x y : L) : (ofSemilatticeInf).mul x y = x ⊓ y := rfl

/-- The monoid built from a semilattice is idempotent. -/
theorem ofSemilatticeInf_idem (x : L) : (ofSemilatticeInf).mul x x = x := inf_idem x

/-- The order recovered from the monoid is the original order. -/
theorem divides_eq_le (x y : L) : (ofSemilatticeInf).mul x y = x ↔ x ≤ y :=
  inf_eq_left

end OfLattice

/-! ## Example: languages under intersection -/

section Languages

variable {α : Type u}

/-- Sets of words form an idempotent commutative monoid under intersection. -/
theorem inter_idem (S : Set (List α)) : S ∩ S = S := Set.inter_self S

theorem inter_isGLB (S T U : Set (List α)) :
    S ∩ T ⊆ S ∧ S ∩ T ⊆ T ∧ (U ⊆ S → U ⊆ T → U ⊆ S ∩ T) :=
  ⟨Set.inter_subset_left, Set.inter_subset_right, fun h₁ h₂ => Set.subset_inter h₁ h₂⟩

end Languages

end UAM.Semilattice
