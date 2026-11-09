import RequestProject.Atlas.UAM_StarFreeLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Subword constraints are star-free

For a fixed word `u = a₁ ⋯ aₙ`, the language of words containing `u` as a
*scattered subword* is the concatenation `Σ* a₁ Σ* a₂ ⋯ Σ* aₙ Σ*`, which is
star-free because no Kleene star beyond the full language `Σ* = ⊤` is involved.

* `UAM.StarFree.subseqLang` — the language above, defined by recursion on `u`;
* `UAM.StarFree.mem_subseqLang` — it consists exactly of the words having `u` as
  a sublist (Mathlib's `List.Sublist` is the scattered-subword relation);
* `UAM.StarFree.isStarFree_containsSubword`,
  `UAM.StarFree.isStarFree_avoidsSubword` — containing, or avoiding, a fixed
  subword is a star-free condition;
* `UAM.StarFree.isStarFree_containsAllSubwords` — hence so is any finite
  conjunction of subword constraints; the piecewise testable languages, the
  Boolean combinations of such constraints, are therefore star-free.
-/

namespace UAM.StarFree

variable {α : Type}

/-- The language of words containing `u` as a scattered subword. -/
def subseqLang : List α → Language α
  | [] => (⊤ : Language α)
  | a :: u => (⊤ : Language α) * ({[a]} : Language α) * subseqLang u

theorem mem_top_mul_char_mul (a : α) (L : Language α) (w : List α) :
    w ∈ (⊤ : Language α) * ({[a]} : Language α) * L ↔ ∃ x y, w = x ++ a :: y ∧ y ∈ L := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨z, hz, y, hy, rfl⟩
    rw [Language.mem_mul] at hz
    obtain ⟨x, -, c, hc, rfl⟩ := hz
    have hc' : c = [a] := hc
    exact ⟨x, y, by rw [hc']; simp, hy⟩
  · rintro ⟨x, y, rfl, hy⟩
    exact ⟨x ++ [a], Language.mem_mul.2 ⟨x, trivial, [a], rfl, rfl⟩, y, hy, by simp⟩

theorem mem_subseqLang (u w : List α) : w ∈ subseqLang u ↔ u.Sublist w := by
  induction u generalizing w with
  | nil => exact ⟨fun _ => List.nil_sublist w, fun _ => trivial⟩
  | cons a u ih =>
    rw [subseqLang, mem_top_mul_char_mul]
    constructor
    · rintro ⟨x, y, rfl, hy⟩
      exact (List.cons_sublist_cons.2 ((ih y).1 hy)).trans
        (List.sublist_append_right x (a :: y))
    · intro h
      obtain ⟨r₁, r₂, rfl, ha, hu⟩ := List.cons_sublist_iff.1 h
      obtain ⟨x, z, rfl⟩ := List.append_of_mem ha
      exact ⟨x, z ++ r₂, by simp, (ih _).2 (hu.trans (List.sublist_append_right z r₂))⟩

theorem isStarFree_subseqLang (u : List α) : IsStarFree (subseqLang u) := by
  induction u with
  | nil => exact isStarFree_top
  | cons a u ih =>
    rw [subseqLang]
    exact IsStarFree.mul (IsStarFree.mul isStarFree_top (IsStarFree.char a)) ih

/-- **Containing a fixed scattered subword is a star-free condition.** -/
theorem isStarFree_containsSubword (u : List α) :
    IsStarFree {w : List α | u.Sublist w} := by
  have h : {w : List α | u.Sublist w} = subseqLang u := by
    ext w
    exact (mem_subseqLang u w).symm
  rw [h]
  exact isStarFree_subseqLang u

theorem isStarFree_avoidsSubword (u : List α) :
    IsStarFree {w : List α | ¬ u.Sublist w} := by
  have h : {w : List α | ¬ u.Sublist w} = ({w : List α | u.Sublist w})ᶜ := rfl
  rw [h]
  exact IsStarFree.compl (isStarFree_containsSubword u)

/-- A finite conjunction of subword constraints is star-free.  Together with
`IsStarFree.compl` and `IsStarFree.add` this shows that every piecewise testable
language — every Boolean combination of subword constraints — is star-free. -/
theorem isStarFree_containsAllSubwords (us : List (List α)) :
    IsStarFree {w : List α | ∀ u ∈ us, u.Sublist w} := by
  induction us with
  | nil =>
    have h : {w : List α | ∀ u ∈ ([] : List (List α)), u.Sublist w} = (⊤ : Language α) := by
      ext w
      exact ⟨fun _ => trivial, fun _ u hu => absurd hu (List.not_mem_nil)⟩
    rw [h]
    exact isStarFree_top
  | cons u us ih =>
    have h : {w : List α | ∀ v ∈ u :: us, v.Sublist w}
        = ({w : List α | u.Sublist w} : Language α) ⊓ {w : List α | ∀ v ∈ us, v.Sublist w} := by
      ext w
      constructor
      · intro hw
        exact ⟨hw u (List.mem_cons_self ..), fun v hv => hw v (List.mem_cons_of_mem u hv)⟩
      · rintro ⟨h1, h2⟩ v hv
        rcases List.mem_cons.1 hv with rfl | hv'
        · exact h1
        · exact h2 v hv'
    rw [h]
    exact isStarFree_inter (isStarFree_containsSubword u) ih

end UAM.StarFree
