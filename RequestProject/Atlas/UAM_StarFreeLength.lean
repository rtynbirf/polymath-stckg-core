import RequestProject.Atlas.UAM_StarFreeClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Length constraints and factor constraints are star-free

Over a finite alphabet the languages defined by a constraint on the length of a
word, or by the presence of a fixed factor, are star-free:

* `UAM.StarFree.isStarFree_sum` — the class is closed under finite unions;
* `UAM.StarFree.alphabetLang` is the language of one-letter words, and
  `UAM.StarFree.alphabetLang_pow` identifies its `n`-th power with the words of
  length exactly `n`;
* `UAM.StarFree.isStarFree_lengthEq`, `isStarFree_lengthGe`,
  `isStarFree_lengthLt`, `isStarFree_lengthLe`, `isStarFree_lengthGt` — all the
  length constraints;
* `UAM.StarFree.isStarFree_containsFactor` and
  `UAM.StarFree.isStarFree_avoidsFactor` — containing (resp. avoiding) a fixed
  factor is star-free, over an arbitrary alphabet.
-/

namespace UAM.StarFree

variable {α : Type} {ι : Type}

/-! ## Finite unions -/

theorem mem_sum_iff {f : ι → Language α} (s : Finset ι) (w : List α) :
    w ∈ (∑ i ∈ s, f i) ↔ ∃ i ∈ s, w ∈ f i := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    constructor
    · intro h; exact absurd h (Set.notMem_empty w)
    · rintro ⟨i, hi, -⟩; exact absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Language.mem_add, ih]
    constructor
    · rintro (h | ⟨i, hi, hw⟩)
      · exact ⟨a, Finset.mem_insert_self a s, h⟩
      · exact ⟨i, Finset.mem_insert_of_mem hi, hw⟩
    · rintro ⟨i, hi, hw⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact Or.inl hw
      · exact Or.inr ⟨i, hi', hw⟩

/-- The star-free languages are closed under finite unions. -/
theorem isStarFree_sum {f : ι → Language α} (s : Finset ι)
    (h : ∀ i ∈ s, IsStarFree (f i)) : IsStarFree (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsStarFree.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsStarFree.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## The alphabet as a language -/

/-- The language of all one-letter words. -/
def alphabetLang (α : Type) [Fintype α] : Language α := ∑ a : α, ({[a]} : Language α)

variable [Fintype α]

theorem mem_alphabetLang (w : List α) : w ∈ alphabetLang α ↔ ∃ a, w = [a] := by
  rw [alphabetLang, mem_sum_iff]
  constructor
  · rintro ⟨a, -, hw⟩
    exact ⟨a, hw⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, Finset.mem_univ a, rfl⟩

theorem alphabetLang_eq_length_one : alphabetLang α = {w : List α | w.length = 1} := by
  ext w
  rw [mem_alphabetLang]
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro hw
    have hw' : w.length = 1 := hw
    match w, hw' with
    | [a], _ => exact ⟨a, rfl⟩

theorem isStarFree_alphabetLang : IsStarFree (alphabetLang α) :=
  isStarFree_sum Finset.univ fun a _ => IsStarFree.char a

/-- The `n`-th power of the alphabet is the language of words of length `n`. -/
theorem alphabetLang_pow (n : ℕ) :
    (alphabetLang α) ^ n = {w : List α | w.length = n} := by
  induction n with
  | zero =>
    ext w
    rw [pow_zero, Language.mem_one]
    constructor
    · intro hw; rw [hw]; rfl
    · intro hw
      have : w.length = 0 := hw
      exact List.eq_nil_of_length_eq_zero this
  | succ n ih =>
    ext w
    rw [pow_succ, Language.mem_mul]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      have hul : u.length = n := by rw [ih] at hu; exact hu
      obtain ⟨a, rfl⟩ := (mem_alphabetLang v).1 hv
      show (u ++ [a]).length = n + 1
      simp [hul]
    · intro hw
      have hw' : w.length = n + 1 := hw
      refine ⟨w.take n, ?_, w.drop n, ?_, by simp⟩
      · rw [ih]
        show (w.take n).length = n
        simp [hw']
      · rw [mem_alphabetLang]
        have hlen : (w.drop n).length = 1 := by simp [hw']
        match hd : w.drop n, hlen with
        | [a], _ => exact ⟨a, rfl⟩

/-! ## Length constraints -/

theorem isStarFree_lengthEq (n : ℕ) : IsStarFree {w : List α | w.length = n} := by
  rw [← alphabetLang_pow n]
  induction n with
  | zero => rw [pow_zero]; exact IsStarFree.one
  | succ n ih => rw [pow_succ]; exact IsStarFree.mul ih isStarFree_alphabetLang

/-- The language of all words (the top element of the Boolean algebra of
languages) is star-free. -/
theorem isStarFree_top {β : Type} : IsStarFree (⊤ : Language β) := by
  have h : (⊤ : Language β) = (Set.univ : Language β) := rfl
  rw [h]
  exact isStarFree_univ

theorem lengthGe_eq (n : ℕ) :
    {w : List α | n ≤ w.length} = (alphabetLang α) ^ n * (⊤ : Language α) := by
  ext w
  rw [Language.mem_mul]
  constructor
  · intro hw
    have hw' : n ≤ w.length := hw
    refine ⟨w.take n, ?_, w.drop n, trivial, by simp⟩
    rw [alphabetLang_pow]
    show (w.take n).length = n
    simp [hw']
  · rintro ⟨u, hu, v, -, rfl⟩
    rw [alphabetLang_pow] at hu
    have hu' : u.length = n := hu
    show n ≤ (u ++ v).length
    simp [hu']

theorem isStarFree_lengthGe (n : ℕ) : IsStarFree {w : List α | n ≤ w.length} := by
  rw [lengthGe_eq n]
  refine IsStarFree.mul ?_ isStarFree_top
  rw [alphabetLang_pow]
  exact isStarFree_lengthEq n

theorem isStarFree_lengthLt (n : ℕ) : IsStarFree {w : List α | w.length < n} := by
  have h : {w : List α | w.length < n} = ({w : List α | n ≤ w.length})ᶜ := by
    ext w
    exact Nat.not_le.symm
  rw [h]
  exact IsStarFree.compl (isStarFree_lengthGe n)

theorem isStarFree_lengthGt (n : ℕ) : IsStarFree {w : List α | n < w.length} := by
  have h : {w : List α | n < w.length} = {w : List α | n + 1 ≤ w.length} := by
    ext w
    exact Iff.rfl
  rw [h]
  exact isStarFree_lengthGe (n + 1)

theorem isStarFree_lengthLe (n : ℕ) : IsStarFree {w : List α | w.length ≤ n} := by
  have h : {w : List α | w.length ≤ n} = {w : List α | w.length < n + 1} := by
    ext w
    exact Nat.lt_succ_iff.symm
  rw [h]
  exact isStarFree_lengthLt (n + 1)

/-! ## Factor constraints -/

/-- Containing a fixed factor is a star-free condition (no finiteness of the
alphabet is needed). -/
theorem isStarFree_containsFactor {β : Type} (u : List β) :
    IsStarFree ((⊤ : Language β) * ({u} : Language β) * (⊤ : Language β)) :=
  IsStarFree.mul (IsStarFree.mul isStarFree_top (isStarFree_singleton u)) isStarFree_top

theorem mem_containsFactor {β : Type} (u w : List β) :
    w ∈ (⊤ : Language β) * ({u} : Language β) * (⊤ : Language β) ↔
      ∃ x y, w = x ++ u ++ y := by
  rw [Language.mem_mul]
  constructor
  · rintro ⟨z, hz, y, -, rfl⟩
    rw [Language.mem_mul] at hz
    obtain ⟨x, -, u', hu', rfl⟩ := hz
    have hu'' : u' = u := hu'
    exact ⟨x, y, by rw [hu'']⟩
  · rintro ⟨x, y, rfl⟩
    refine ⟨x ++ u, ?_, y, trivial, rfl⟩
    exact Language.mem_mul.2 ⟨x, trivial, u, rfl, rfl⟩

/-- Avoiding a fixed factor is a star-free condition. -/
theorem isStarFree_avoidsFactor {β : Type} (u : List β) :
    IsStarFree {w : List β | ¬ ∃ x y, w = x ++ u ++ y} := by
  have h : {w : List β | ¬ ∃ x y, w = x ++ u ++ y}
      = ((⊤ : Language β) * ({u} : Language β) * (⊤ : Language β))ᶜ := by
    ext w
    exact not_congr (mem_containsFactor u w).symm
  rw [h]
  exact IsStarFree.compl (isStarFree_containsFactor u)

end UAM.StarFree
