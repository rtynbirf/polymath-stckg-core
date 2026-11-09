import RequestProject.Atlas.UAM_Syntactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Congruences saturating a language

A congruence of the free monoid *saturates* a language when equivalent words are
equi-members of it.  The syntactic congruence is the coarsest such congruence,
and a language is regular exactly when *some* saturating congruence has finitely
many classes:

* `UAM.Congruence.Saturates` — the saturation property;
* `UAM.Congruence.syntacticCon_saturates` — the syntactic congruence saturates;
* `UAM.Congruence.le_syntacticCon_of_saturates` — it is the coarsest one;
* `UAM.Congruence.finite_syntacticMonoid_of_finite_quotient` — a finite
  saturating congruence forces a finite syntactic monoid;
* `UAM.Congruence.isRegular_iff_exists_finite_saturating_con` — the
  Myhill–Nerode criterion in congruence form.
-/

namespace UAM.Congruence

open UAM.Syntactic

variable {α : Type}

/-- A congruence saturates a language when related words are equi-members. -/
def Saturates (c : Con (FreeMonoid α)) (L : Language α) : Prop :=
  ∀ x y : FreeMonoid α, c x y → (x.toList ∈ L ↔ y.toList ∈ L)

/-- The syntactic congruence saturates its language. -/
theorem syntacticCon_saturates (L : Language α) : Saturates (syntacticCon L) L :=
  fun _ _ h => mem_iff_of_syntacticRel h

/-- Any saturating congruence refines the syntactic congruence: the syntactic
congruence is the coarsest congruence saturating the language. -/
theorem le_syntacticCon_of_saturates {c : Con (FreeMonoid α)} {L : Language α}
    (h : Saturates c L) {x y : FreeMonoid α} (hxy : c x y) : SyntacticRel L x y := by
  intro u v
  have : c (u * x * v) (u * y * v) := c.mul (c.mul (c.refl u) hxy) (c.refl v)
  exact h _ _ this

/-- The quotient by a saturating congruence maps onto the syntactic monoid. -/
theorem syntacticMonoid_surjective_of_saturates {c : Con (FreeMonoid α)} {L : Language α}
    (h : Saturates c L) :
    ∃ g : c.Quotient → SyntacticMonoid L, Function.Surjective g := by
  refine ⟨Con.lift c (syntacticHom L) ?_, ?_⟩
  · intro x y hxy
    exact (syntacticHom_eq_iff L x y).2 (le_syntacticCon_of_saturates h hxy)
  · intro m
    obtain ⟨x, rfl⟩ := syntacticHom_surjective L m
    exact ⟨c.mk' x, rfl⟩

/-- If some saturating congruence has finitely many classes, so has the
syntactic congruence. -/
theorem finite_syntacticMonoid_of_finite_quotient {c : Con (FreeMonoid α)} {L : Language α}
    (hsat : Saturates c L) (hfin : Finite c.Quotient) : Finite (SyntacticMonoid L) := by
  obtain ⟨g, hg⟩ := syntacticMonoid_surjective_of_saturates hsat
  exact Finite.of_surjective g hg

/-- **Myhill–Nerode, congruence form.**  A language is regular exactly when some
congruence of the free monoid with finitely many classes saturates it. -/
theorem isRegular_iff_exists_finite_saturating_con (L : Language α) :
    L.IsRegular ↔ ∃ c : Con (FreeMonoid α), Saturates c L ∧ Finite c.Quotient := by
  constructor
  · intro hL
    have hfin : Finite (SyntacticMonoid L) := (isRegular_iff_finite_syntacticMonoid L).1 hL
    exact ⟨syntacticCon L, syntacticCon_saturates L, hfin⟩
  · rintro ⟨c, hsat, hfin⟩
    exact (isRegular_iff_finite_syntacticMonoid L).2
      (finite_syntacticMonoid_of_finite_quotient hsat hfin)

/-! ## Refinement of congruences -/

/-- A finer congruence still saturates. -/
theorem Saturates.mono {c d : Con (FreeMonoid α)} {L : Language α}
    (hcd : ∀ x y : FreeMonoid α, d x y → c x y) (h : Saturates c L) : Saturates d L :=
  fun x y hxy => h x y (hcd x y hxy)

/-- The trivial congruence (equality) saturates every language. -/
theorem saturates_bot (L : Language α) : Saturates (⊥ : Con (FreeMonoid α)) L := by
  intro x y hxy
  have : x = y := hxy
  rw [this]

/-- The full congruence saturates only the trivial languages. -/
theorem saturates_top_iff (L : Language α) :
    Saturates (⊤ : Con (FreeMonoid α)) L ↔
      (∀ x : FreeMonoid α, x.toList ∈ L) ∨ (∀ x : FreeMonoid α, x.toList ∉ L) := by
  constructor
  · intro h
    by_cases hL : ∀ x : FreeMonoid α, x.toList ∉ L
    · exact Or.inr hL
    · push_neg at hL
      obtain ⟨y, hy⟩ := hL
      exact Or.inl fun x => (h y x trivial).1 hy
  · rintro (h | h) x y _
    · exact ⟨fun _ => h y, fun _ => h x⟩
    · exact ⟨fun hx => absurd hx (h x), fun hy => absurd hy (h y)⟩

end UAM.Congruence
