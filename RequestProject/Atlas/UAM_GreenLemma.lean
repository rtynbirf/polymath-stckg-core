import RequestProject.Atlas.UAM_Aperiodic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Green's lemma and the maximal subgroups of a monoid

Green's lemma says that if `a R b`, witnessed by `b = a * s` and `a = b * t`,
then right translation by `s` maps the `L`-class of `a` into the `L`-class of
`b`, is undone by right translation by `t`, and moves no element out of its
`R`-class (`UAM.Green.green_lemma_R`, and dually `UAM.Green.green_lemma_L`).

Its main consequence here is **Green's theorem on maximal subgroups**: the
`H`-class of an idempotent `e` is a group with identity `e`
(`UAM.Green.maximalSubgroup`).  Every element of that `H`-class is fixed by `e`
on both sides (`UAM.Green.mul_idem_left`, `UAM.Green.mul_idem_right`) and has a
two-sided inverse inside it (`UAM.Green.exists_hEquiv_inverse`).

Combining this with `UAM.Green.aperiodic_iff_hTrivial` gives a third
characterisation of aperiodicity for finite monoids: *all maximal subgroups are
trivial* (`UAM.Green.aperiodic_iff_subgroups_trivial`).
-/

namespace UAM.Green

variable {M : Type*} [Monoid M]

/-! ## Green's lemma -/

/-- **Green's lemma**, `R`-version.  If `b = a * s` and `a = b * t`, then right
translation by `s` maps the `L`-class of `a` into the `L`-class of `b`, is
undone by right translation by `t`, and moves no element out of its
`R`-class. -/
theorem green_lemma_R {a b s t : M} (hb : b = a * s) (ha : a = b * t)
    {x : M} (hx : LEquiv x a) :
    LEquiv (x * s) b ∧ x * s * t = x ∧ REquiv x (x * s) := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hx
  have hfix : x * s * t = x := by
    rw [hu]
    conv_rhs => rw [ha, hb]
    simp only [mul_assoc]
  refine ⟨⟨⟨u, ?_⟩, ⟨v, ?_⟩⟩, hfix, ⟨⟨t, hfix.symm⟩, ⟨s, rfl⟩⟩⟩
  · rw [hu, hb, mul_assoc]
  · rw [hb, hv, mul_assoc]

/-- **Green's lemma**, `L`-version.  If `b = s * a` and `a = t * b`, then left
translation by `s` maps the `R`-class of `a` into the `R`-class of `b`, is
undone by left translation by `t`, and moves no element out of its
`L`-class. -/
theorem green_lemma_L {a b s t : M} (hb : b = s * a) (ha : a = t * b)
    {x : M} (hx : REquiv x a) :
    REquiv (s * x) b ∧ t * (s * x) = x ∧ LEquiv x (s * x) := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hx
  have hfix : t * (s * x) = x := by
    rw [hu]
    conv_rhs => rw [ha, hb]
    simp only [mul_assoc]
  refine ⟨⟨⟨u, ?_⟩, ⟨v, ?_⟩⟩, hfix, ⟨⟨t, hfix.symm⟩, ⟨s, rfl⟩⟩⟩
  · rw [hu, hb, mul_assoc]
  · rw [hb, hv, mul_assoc]

/-! ## The `H`-class of an idempotent -/

section Idempotent

variable {e : M} (he : IsIdempotentElem e)

include he

/-- An idempotent acts as a right identity on its own `H`-class. -/
theorem mul_idem_right {x : M} (hx : HEquiv x e) : x * e = x := by
  have hee : e * e = e := he
  obtain ⟨u, hu⟩ := hx.1.1
  rw [hu, mul_assoc, hee]

/-- An idempotent acts as a left identity on its own `H`-class. -/
theorem mul_idem_left {x : M} (hx : HEquiv x e) : e * x = x := by
  have hee : e * e = e := he
  obtain ⟨u, hu⟩ := hx.2.1
  rw [hu, ← mul_assoc, hee]

/-- **Every element of the `H`-class of an idempotent has a two-sided inverse
inside that `H`-class.** -/
theorem exists_hEquiv_inverse {x : M} (hx : HEquiv x e) :
    ∃ y : M, HEquiv y e ∧ x * y = e ∧ y * x = e := by
  have hee : e * e = e := he
  obtain ⟨t, ht⟩ := hx.2.2
  obtain ⟨v, hv⟩ := hx.1.2
  have hxe : x * e = x := mul_idem_right he hx
  have hex : e * x = x := mul_idem_left he hx
  have hxyr : x * (e * t * e) = e := by
    calc x * (e * t * e) = x * e * t * e := by simp only [mul_assoc]
      _ = x * t * e := by rw [hxe]
      _ = e * e := by rw [← ht]
      _ = e := hee
  have hylx : e * v * e * x = e := by
    calc e * v * e * x = e * v * (e * x) := by simp only [mul_assoc]
      _ = e * v * x := by rw [hex]
      _ = e * e := by rw [mul_assoc, ← hv]
      _ = e := hee
  have hyle : e * v * e * e = e * v * e := by simp only [mul_assoc, hee]
  have heyr : e * (e * t * e) = e * t * e := by simp only [← mul_assoc, hee]
  have hyy : e * v * e = e * t * e := by
    calc e * v * e = e * v * e * e := hyle.symm
      _ = e * v * e * (x * (e * t * e)) := by rw [hxyr]
      _ = e * v * e * x * (e * t * e) := by simp only [mul_assoc]
      _ = e * (e * t * e) := by rw [hylx]
      _ = e * t * e := heyr
  have hyrx : e * t * e * x = e := by rw [← hyy]; exact hylx
  exact ⟨e * t * e, ⟨⟨⟨e * t, rfl⟩, ⟨x, hxyr.symm⟩⟩,
    ⟨⟨t * e, mul_assoc e t e⟩, ⟨x, hyrx.symm⟩⟩⟩, hxyr, hyrx⟩

/-- The `H`-class of an idempotent is closed under multiplication. -/
theorem hEquiv_mul {x z : M} (hx : HEquiv x e) (hz : HEquiv z e) : HEquiv (x * z) e := by
  obtain ⟨yx, _, hxyx, hyxx⟩ := exists_hEquiv_inverse he hx
  obtain ⟨yz, _, hzyz, hyzz⟩ := exists_hEquiv_inverse he hz
  have hze : z * e = z := mul_idem_right he hz
  have hex : e * x = x := mul_idem_left he hx
  have hez : e * z = z := mul_idem_left he hz
  have hxe : x * e = x := mul_idem_right he hx
  have h1 : x * z * (yz * yx) = e := by
    calc x * z * (yz * yx) = x * (z * yz) * yx := by simp only [mul_assoc]
      _ = x * e * yx := by rw [hzyz]
      _ = x * yx := by rw [hxe]
      _ = e := hxyx
  have h2 : yz * yx * (x * z) = e := by
    calc yz * yx * (x * z) = yz * (yx * x) * z := by simp only [mul_assoc]
      _ = yz * e * z := by rw [hyxx]
      _ = yz * z := by rw [mul_assoc, hez]
      _ = e := hyzz
  exact ⟨⟨⟨x * z, by rw [mul_assoc, hze]⟩, ⟨yz * yx, h2.symm⟩⟩,
    ⟨⟨x * z, by rw [← mul_assoc, hex]⟩, ⟨yz * yx, h1.symm⟩⟩⟩

/-- **Green's theorem**: the `H`-class of an idempotent `e` is a group with
identity `e`. -/
noncomputable def maximalSubgroup : Group {x : M // HEquiv x e} where
  mul a b := ⟨a.1 * b.1, hEquiv_mul he a.2 b.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one := ⟨e, hEquiv_refl e⟩
  one_mul a := Subtype.ext (mul_idem_left he a.2)
  mul_one a := Subtype.ext (mul_idem_right he a.2)
  inv a := ⟨Classical.choose (exists_hEquiv_inverse he a.2),
    (Classical.choose_spec (exists_hEquiv_inverse he a.2)).1⟩
  inv_mul_cancel a :=
    Subtype.ext (Classical.choose_spec (exists_hEquiv_inverse he a.2)).2.2

end Idempotent

/-! ## Aperiodicity and trivial subgroups -/

/-- In an `H`-trivial monoid every `H`-class is a singleton. -/
theorem subsingleton_hClass_of_hTrivial (h : HTrivial M) (e : M) :
    Subsingleton {x : M // HEquiv x e} :=
  ⟨fun a b => Subtype.ext ((h _ _ a.2).trans (h _ _ b.2).symm)⟩

/-- If `x ^ n` is idempotent then `x ^ (n + 1)` is `H`-equivalent to it. -/
theorem hEquiv_pow_succ {x : M} {n : ℕ} (hn : 0 < n) (hidem : IsIdempotentElem (x ^ n)) :
    HEquiv (x ^ (n + 1)) (x ^ n) := by
  have hdouble : x ^ (n + n) = x ^ n := by rw [pow_add]; exact hidem
  have hsplitL : x ^ n = x ^ (n - 1) * x ^ (n + 1) := by
    rw [← pow_add]
    have hrw : n - 1 + (n + 1) = n + n := by omega
    rw [hrw, hdouble]
  have hsplitR : x ^ n = x ^ (n + 1) * x ^ (n - 1) := by
    rw [← pow_add]
    have hrw : n + 1 + (n - 1) = n + n := by omega
    rw [hrw, hdouble]
  exact ⟨⟨⟨x, by rw [← pow_succ']⟩, ⟨x ^ (n - 1), hsplitL⟩⟩,
    ⟨⟨x, by rw [← pow_succ]⟩, ⟨x ^ (n - 1), hsplitR⟩⟩⟩

/-- **A finite monoid is aperiodic exactly when all of its maximal subgroups are
trivial.** -/
theorem aperiodic_iff_subgroups_trivial [Finite M] :
    Aperiodic M ↔ ∀ e : M, IsIdempotentElem e → Subsingleton {x : M // HEquiv x e} := by
  constructor
  · intro h e _
    exact subsingleton_hClass_of_hTrivial (hTrivial_of_aperiodic h) e
  · intro h x
    obtain ⟨n, hn, hidem⟩ := UAM.Idempotent.exists_pow_isIdempotentElem x
    refine ⟨n, ?_⟩
    haveI := h (x ^ n) hidem
    have hsub : (⟨x ^ (n + 1), hEquiv_pow_succ hn hidem⟩ : {y : M // HEquiv y (x ^ n)})
        = ⟨x ^ n, hEquiv_refl _⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val hsub

end UAM.Green
