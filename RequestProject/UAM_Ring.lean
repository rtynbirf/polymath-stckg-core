import RequestProject.Atlas.UAM_Kleene
import RequestProject.Atlas.UAM_KleeneConverse
import RequestProject.Atlas.UAM_Closure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The regular languages as a Kleene subalgebra

`Language α` carries the structure of a Kleene algebra: a semiring under union
and concatenation, together with the star operation.  This module packages the
closure properties proved elsewhere in the development as a concrete
substructure of that Kleene algebra.

* `UAM.Ring.regularSubsemiring` — the regular languages form a subsemiring of
  `Language α`: they contain `0` and `1` and are closed under union and
  concatenation;
* `UAM.Ring.kstar_mem`, `compl_mem`, `inf_mem` — the carrier is moreover closed
  under Kleene star, complement and intersection;
* `UAM.Ring.regular_kleene_closed` — all of these closure properties bundled;
* `UAM.Ring.mem_regularSubsemiring_iff_isRegexLang` — over a finite alphabet the
  carrier is exactly the set of languages denoted by regular expressions, i.e.
  the subsemiring is the image of the free Kleene algebra of regular
  expressions.
-/

namespace UAM.Ring

open scoped Computability

universe u

variable {α : Type u}

/-! ## The subsemiring -/

/-- The regular languages form a subsemiring of the semiring of all languages. -/
def regularSubsemiring (α : Type u) : Subsemiring (Language α) where
  carrier := {L : Language α | L.IsRegular}
  zero_mem' := UAM.Kleene.isRegular_zero
  one_mem' := UAM.Kleene.isRegular_one
  add_mem' := fun hL hM => Language.IsRegular.add hL hM
  mul_mem' := fun hL hM => UAM.Kleene.isRegular_mul hL hM

@[simp] theorem mem_regularSubsemiring {L : Language α} :
    L ∈ regularSubsemiring α ↔ L.IsRegular := Iff.rfl

/-! ## Closure beyond the semiring operations -/

/-- The carrier of `regularSubsemiring` is closed under Kleene star. -/
theorem kstar_mem {L : Language α} (hL : L ∈ regularSubsemiring α) :
    L∗ ∈ regularSubsemiring α :=
  UAM.Kleene.isRegular_kstar hL

/-- The carrier of `regularSubsemiring` is closed under complement. -/
theorem compl_mem {L : Language α} (hL : L ∈ regularSubsemiring α) :
    Lᶜ ∈ regularSubsemiring α :=
  Language.IsRegular.compl hL

/-- The carrier of `regularSubsemiring` is closed under intersection. -/
theorem inf_mem {L M : Language α} (hL : L ∈ regularSubsemiring α)
    (hM : M ∈ regularSubsemiring α) : L ⊓ M ∈ regularSubsemiring α :=
  Language.IsRegular.inf hL hM

/-- The carrier of `regularSubsemiring` is closed under reversal. -/
theorem reverse_mem {L : Language α} (hL : L ∈ regularSubsemiring α) :
    L.reverse ∈ regularSubsemiring α :=
  UAM.Closure.isRegular_reverse hL

/-- **The regular languages are a Boolean Kleene subalgebra.**  They contain the
two constants and are closed under union, concatenation, star, intersection,
complement and reversal. -/
theorem regular_kleene_closed :
    (0 : Language α).IsRegular ∧ (1 : Language α).IsRegular ∧
      (∀ L M : Language α, L.IsRegular → M.IsRegular → (L + M).IsRegular) ∧
      (∀ L M : Language α, L.IsRegular → M.IsRegular → (L * M).IsRegular) ∧
      (∀ L : Language α, L.IsRegular → (L∗).IsRegular) ∧
      (∀ L M : Language α, L.IsRegular → M.IsRegular → (L ⊓ M).IsRegular) ∧
      (∀ L : Language α, L.IsRegular → (Lᶜ).IsRegular) ∧
      (∀ L : Language α, L.IsRegular → L.reverse.IsRegular) :=
  ⟨UAM.Kleene.isRegular_zero, UAM.Kleene.isRegular_one,
    fun _ _ hL hM => Language.IsRegular.add hL hM,
    fun _ _ hL hM => UAM.Kleene.isRegular_mul hL hM,
    fun _ hL => UAM.Kleene.isRegular_kstar hL,
    fun _ _ hL hM => Language.IsRegular.inf hL hM,
    fun _ hL => Language.IsRegular.compl hL,
    fun _ hL => UAM.Closure.isRegular_reverse hL⟩

/-- The language of a regular expression is a member of the subsemiring. -/
theorem matches'_mem (P : RegularExpression α) :
    P.matches' ∈ regularSubsemiring α :=
  UAM.Kleene.isRegular_matches' P

/-- Over a finite alphabet the subsemiring is exactly the set of languages
denoted by regular expressions. -/
theorem mem_regularSubsemiring_iff_isRegexLang {β : Type} [Fintype β] {L : Language β} :
    L ∈ regularSubsemiring β ↔ ∃ P : RegularExpression β, P.matches' = L :=
  UAM.Kleene.isRegular_iff_isRegexLang

/-- The regular languages over a finite alphabet are precisely the image of the
denotation map on regular expressions. -/
theorem regularSubsemiring_carrier_eq_range_matches' {β : Type} [Fintype β] :
    (regularSubsemiring β : Set (Language β)) =
      Set.range (fun P : RegularExpression β => P.matches') := by
  ext L
  simpa using (mem_regularSubsemiring_iff_isRegexLang (β := β) (L := L))

end UAM.Ring
