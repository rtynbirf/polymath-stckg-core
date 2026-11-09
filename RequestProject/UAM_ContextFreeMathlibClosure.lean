import RequestProject.UAM_ContextFreeMathlib
import RequestProject.UAM_ContextFreeFinitaryClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Closure properties for Mathlib's `Language.IsContextFree`

`UAM.ContextFree.isCFL_iff_isContextFree` identifies the class `IsCFL` of this
development with Mathlib's `Language.IsContextFree`.  Transporting the closure
theorems proved for `IsCFL` along that equivalence gives the closure properties
for Mathlib's predicate: union, concatenation, Kleene star, intersection with a
regular language, and homomorphic images, together with the inclusion of the
regular languages.
-/

namespace UAM.ContextFree

open scoped Computability

variable {T : Type}

/-- Every regular language over a finite alphabet is context-free. -/
theorem mathlibIsContextFree_of_isRegular [Finite T] {L : Language T} (h : L.IsRegular) :
    Language.IsContextFree L :=
  (isCFL_iff_isContextFree L).1 (isCFL_of_isRegular h)

/-- **Context-free languages are closed under union.** -/
theorem isContextFree_add {L₁ L₂ : Language T}
    (h₁ : Language.IsContextFree L₁) (h₂ : Language.IsContextFree L₂) :
    Language.IsContextFree (L₁ + L₂) :=
  (isCFL_iff_isContextFree _).1
    (((isCFL_iff_isContextFree L₁).2 h₁).union ((isCFL_iff_isContextFree L₂).2 h₂))

/-- **Context-free languages are closed under concatenation.** -/
theorem isContextFree_mul {L₁ L₂ : Language T}
    (h₁ : Language.IsContextFree L₁) (h₂ : Language.IsContextFree L₂) :
    Language.IsContextFree (L₁ * L₂) :=
  (isCFL_iff_isContextFree _).1
    (((isCFL_iff_isContextFree L₁).2 h₁).mul ((isCFL_iff_isContextFree L₂).2 h₂))

/-- **Context-free languages are closed under Kleene star.** -/
theorem isContextFree_kstar {L : Language T} (h : Language.IsContextFree L) :
    Language.IsContextFree (L∗) :=
  (isCFL_iff_isContextFree _).1 (((isCFL_iff_isContextFree L).2 h).kstar)

/-- **The intersection of a context-free language with a regular language is
context-free.** -/
theorem isContextFree_inter_regular {L R : Language T}
    (hL : Language.IsContextFree L) (hR : R.IsRegular) :
    Language.IsContextFree (L ⊓ R) :=
  (isCFL_iff_isContextFree _).1 (((isCFL_iff_isContextFree L).2 hL).inter_regular hR)

/-- **Context-free languages are closed under homomorphic images.** -/
theorem isContextFree_hom {L : Language T} (h : Language.IsContextFree L) {T' : Type}
    (f : T → List T') :
    Language.IsContextFree {w' : List T' | ∃ w ∈ L, w' = hom f w} :=
  (isCFL_iff_isContextFree _).1 (((isCFL_iff_isContextFree L).2 h).hom f)

end UAM.ContextFree
