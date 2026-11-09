import RequestProject.Atlas.UAM_StarFreeLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Star-free languages and letter-to-letter morphisms

A map `f : α → β` on letters induces the length-preserving monoid morphism
`List.map f` on words.  Taking preimages along it,

`UAM.StarFree.comap f L = {w | w.map f ∈ L}`,

commutes with all the operations generating the star-free languages: it is a
Boolean-algebra map (`comap_compl`, `comap_add`) and a morphism for
concatenation (`comap_mul`), while the preimage of a letter is the finite union
of the letters above it (`comap_char`).  Hence

* `UAM.StarFree.isStarFree_comap` — **the star-free languages are closed under
  inverse letter-to-letter morphisms** (over a finite source alphabet), and
* `UAM.StarFree.isStarFree_map_equiv` — in particular under renaming the
  alphabet along a bijection.

Finiteness of the source alphabet is genuinely needed: the preimage of a letter
is the union of all letters mapping to it.
-/

namespace UAM.StarFree

variable {α β : Type}

/-- The preimage of a language along the letter-to-letter morphism induced by
`f`. -/
def comap (f : α → β) (L : Language β) : Language α := {w | w.map f ∈ L}

@[simp] theorem mem_comap (f : α → β) (L : Language β) (w : List α) :
    w ∈ comap f L ↔ w.map f ∈ L := Iff.rfl

theorem comap_zero (f : α → β) : comap f (0 : Language β) = 0 := by
  ext w
  exact Iff.rfl

theorem comap_one (f : α → β) : comap f (1 : Language β) = 1 := by
  ext w
  rw [mem_comap, Language.mem_one, Language.mem_one]
  constructor
  · intro h
    exact List.eq_nil_of_map_eq_nil h
  · intro h
    rw [h]
    rfl

theorem comap_compl (f : α → β) (L : Language β) : comap f Lᶜ = (comap f L)ᶜ := by
  ext w
  exact Iff.rfl

theorem comap_add (f : α → β) (L M : Language β) :
    comap f (L + M) = comap f L + comap f M := by
  ext w
  rw [mem_comap, Language.mem_add, Language.mem_add, mem_comap, mem_comap]

theorem comap_mul (f : α → β) (L M : Language β) :
    comap f (L * M) = comap f L * comap f M := by
  ext w
  rw [mem_comap, Language.mem_mul, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨w.take u.length, ?_, w.drop u.length, ?_, by simp⟩
    · rw [mem_comap, List.map_take, ← huv]
      simpa using hu
    · rw [mem_comap, List.map_drop, ← huv]
      simpa using hv
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u.map f, hu, v.map f, hv, by simp⟩

/-- The preimage of a letter is the union of the letters lying above it. -/
theorem comap_char [Fintype α] [DecidableEq β] (f : α → β) (b : β) :
    comap f ({[b]} : Language β)
      = ∑ a : α, (if f a = b then ({[a]} : Language α) else 0) := by
  ext w
  rw [mem_sum_iff]
  constructor
  · intro hw
    have hw' : w.map f = [b] := hw
    obtain ⟨a, ha, hfa⟩ : ∃ a, w = [a] ∧ f a = b := by
      match w, hw' with
      | [a], h => exact ⟨a, rfl, by simpa using h⟩
    refine ⟨a, Finset.mem_univ a, ?_⟩
    rw [if_pos hfa]
    exact ha
  · rintro ⟨a, -, hw⟩
    by_cases hc : f a = b
    · rw [if_pos hc] at hw
      have hw' : w = [a] := hw
      show w.map f = [b]
      rw [hw', List.map_cons, List.map_nil, hc]
    · rw [if_neg hc] at hw
      exact absurd hw (Set.notMem_empty w)

/-- **The star-free languages are closed under inverse letter-to-letter
morphisms.** -/
theorem isStarFree_comap [Fintype α] {L : Language β} (h : IsStarFree L) (f : α → β) :
    IsStarFree (comap f L) := by
  classical
  induction h with
  | zero => rw [comap_zero]; exact IsStarFree.zero
  | one => rw [comap_one]; exact IsStarFree.one
  | char b =>
    rw [comap_char]
    refine isStarFree_sum Finset.univ fun a _ => ?_
    by_cases hc : f a = b
    · rw [if_pos hc]; exact IsStarFree.char a
    · rw [if_neg hc]; exact IsStarFree.zero
  | compl _ ih => rw [comap_compl]; exact IsStarFree.compl ih
  | add _ _ ihL ihM => rw [comap_add]; exact IsStarFree.add ihL ihM
  | mul _ _ ihL ihM => rw [comap_mul]; exact IsStarFree.mul ihL ihM

/-- The image of a star-free language under a bijective renaming of the
alphabet is star-free: the image along `e` is the preimage along `e.symm`. -/
theorem isStarFree_map_equiv [Fintype β] {L : Language α} (h : IsStarFree L)
    (e : α ≃ β) : IsStarFree {w : List β | w.map e.symm ∈ L} :=
  isStarFree_comap h _

end UAM.StarFree
