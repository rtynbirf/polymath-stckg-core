import RequestProject.Atlas.UAM_Morphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The syntactic congruence and the syntactic monoid

Two words are *syntactically equivalent* for a language `L` when they can be
substituted for one another inside any context without changing membership in
`L`.  This is a two-sided congruence on the free monoid of words, so the
quotient `SyntacticMonoid L` is a monoid, and the quotient map recognizes `L`
(`syntacticMonoid_recognizes`).

The syntactic monoid is the canonical recognizing monoid:

* it is a quotient of any monoid recognizing `L`, hence finite whenever `L` is
  recognizable (`finite_syntacticMonoid_of_isRecognizable`);
* conversely, if it is finite it recognizes `L`, so `L` is regular.

Together these give `isRegular_iff_finite_syntacticMonoid`: a language is
regular exactly when its syntactic monoid is finite.
-/

namespace UAM.Syntactic

open UAM.Free UAM.Morphism

variable {α : Type}

/-! ## The syntactic congruence -/

/-- Words that can be exchanged in every context without changing membership. -/
def SyntacticRel (L : Language α) (x y : FreeMonoid α) : Prop :=
  ∀ u v : FreeMonoid α, (u * x * v).toList ∈ L ↔ (u * y * v).toList ∈ L

/-- The syntactic congruence of a language. -/
def syntacticCon (L : Language α) : Con (FreeMonoid α) where
  r := SyntacticRel L
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h u v => (h u v).symm
      trans := fun h₁ h₂ u v => (h₁ u v).trans (h₂ u v) }
  mul' := by
    intro w x y z hwx hyz u v
    calc (u * (w * y) * v).toList ∈ L
        ↔ (u * w * (y * v)).toList ∈ L := by simp only [mul_assoc]
      _ ↔ (u * x * (y * v)).toList ∈ L := hwx u (y * v)
      _ ↔ (u * x * y * v).toList ∈ L := by simp only [mul_assoc]
      _ ↔ (u * x * z * v).toList ∈ L := hyz (u * x) v
      _ ↔ (u * (x * z) * v).toList ∈ L := by simp only [mul_assoc]

/-- The syntactic monoid of a language. -/
def SyntacticMonoid (L : Language α) : Type := (syntacticCon L).Quotient

instance (L : Language α) : Monoid (SyntacticMonoid L) :=
  inferInstanceAs (Monoid (syntacticCon L).Quotient)

/-- The canonical surjection from words onto the syntactic monoid. -/
def syntacticHom (L : Language α) : FreeMonoid α →* SyntacticMonoid L := (syntacticCon L).mk'

theorem syntacticHom_surjective (L : Language α) : Function.Surjective (syntacticHom L) :=
  Con.mk'_surjective

theorem syntacticHom_eq_iff (L : Language α) (x y : FreeMonoid α) :
    syntacticHom L x = syntacticHom L y ↔ SyntacticRel L x y :=
  Con.eq _

/-- Syntactically equivalent words are equi-members of the language. -/
theorem mem_iff_of_syntacticRel {L : Language α} {x y : FreeMonoid α}
    (h : SyntacticRel L x y) : x.toList ∈ L ↔ y.toList ∈ L := by
  simpa using h 1 1


/-! ## Evaluation through a homomorphism -/

theorem eval_hom_of {M : Type} [Monoid M] (φ : FreeMonoid α →* M) (x : List α) :
    eval (fun a => φ (FreeMonoid.of a)) x = φ (FreeMonoid.ofList x) := by
  induction x with
  | nil => simp
  | cons a t ih =>
    rw [eval_cons, ih, ← map_mul]
    rfl

/-! ## The syntactic monoid recognizes the language -/

/-- The accepting set of the syntactic monoid. -/
def syntacticAccept (L : Language α) : Set (SyntacticMonoid L) :=
  {m | ∃ x : FreeMonoid α, syntacticHom L x = m ∧ x.toList ∈ L}

/-- The syntactic monoid, with the quotient map, recognizes the language. -/
theorem syntacticMonoid_recognizes (L : Language α) :
    Recognizes (M := SyntacticMonoid L) (fun a => syntacticHom L (FreeMonoid.of a))
      (syntacticAccept L) L := by
  intro x
  rw [eval_hom_of (syntacticHom L) x]
  constructor
  · intro hx
    exact ⟨FreeMonoid.ofList x, rfl, hx⟩
  · rintro ⟨y, hy, hyL⟩
    exact (mem_iff_of_syntacticRel ((syntacticHom_eq_iff L y (FreeMonoid.ofList x)).1 hy)).1 hyL

/-- If the syntactic monoid is finite, the language is recognizable. -/
theorem isRecognizable_of_finite_syntacticMonoid {L : Language α}
    (h : Finite (SyntacticMonoid L)) : IsRecognizable L :=
  ⟨SyntacticMonoid L, inferInstance, h, fun a => syntacticHom L (FreeMonoid.of a),
    syntacticAccept L, syntacticMonoid_recognizes L⟩

/-! ## The syntactic monoid is a quotient of any recognizing monoid -/

/-- Words with the same image in a recognizing monoid are syntactically
equivalent. -/
theorem syntacticRel_of_eval_eq {L : Language α} {M : Type} [Monoid M] {f : α → M} {P : Set M}
    (hrec : Recognizes f P L) {x y : FreeMonoid α}
    (h : eval f x.toList = eval f y.toList) : SyntacticRel L x y := by
  intro u v
  have hx : (u * x * v).toList = u.toList ++ x.toList ++ v.toList := rfl
  have hy : (u * y * v).toList = u.toList ++ y.toList ++ v.toList := rfl
  rw [hrec _, hrec _, hx, hy, eval_append, eval_append, eval_append, eval_append, h]

/-- The syntactic monoid of a recognizable language is finite. -/
theorem finite_syntacticMonoid_of_isRecognizable {L : Language α} (h : IsRecognizable L) :
    Finite (SyntacticMonoid L) := by
  classical
  obtain ⟨M, _, hM, f, P, hrec⟩ := h
  refine Finite.of_surjective
    (fun m : M => if hx : ∃ x : FreeMonoid α, eval f x.toList = m then
      syntacticHom L hx.choose else 1) ?_
  intro c
  obtain ⟨x, rfl⟩ := syntacticHom_surjective L c
  have hex : ∃ y : FreeMonoid α, eval f y.toList = eval f x.toList := ⟨x, rfl⟩
  refine ⟨eval f x.toList, ?_⟩
  dsimp only
  rw [dif_pos hex]
  exact (syntacticHom_eq_iff L _ x).2 (syntacticRel_of_eval_eq hrec hex.choose_spec)

/-! ## The characterization -/

/-- **A language is regular exactly when its syntactic monoid is finite.** -/
theorem isRegular_iff_finite_syntacticMonoid (L : Language α) :
    L.IsRegular ↔ Finite (SyntacticMonoid L) :=
  ⟨fun h => finite_syntacticMonoid_of_isRecognizable (IsRegular.isRecognizable h),
   fun h => IsRecognizable.isRegular (isRecognizable_of_finite_syntacticMonoid h)⟩

end UAM.Syntactic
