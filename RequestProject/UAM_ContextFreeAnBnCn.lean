import RequestProject.UAM_ContextFreePumping

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `aⁿbⁿcⁿ` is beyond Chomsky normal form grammars

The pumping lemma of `UAM.ContextFree.Pumping` is applied to the classical
three-letter language `{aⁿbⁿcⁿ}`.  Pumping twice keeps the word sorted, which
forces the two pumped factors to be constant; pumping down to zero forces the
three letter counts to move together, which a pair of constant factors cannot
achieve.

Main results:

* `UAM.ContextFree.AnBnCn.count_w3` — the letter counts of `aⁿbⁿcⁿ`;
* `UAM.ContextFree.AnBnCn.constant_of_sorted_self` — a word whose square is
  sorted is constant;
* `UAM.ContextFree.AnBnCn.not_cnf_language` — no grammar in Chomsky normal form
  generates `{aⁿbⁿcⁿ}`.
-/

namespace UAM.ContextFree.AnBnCn

open UAM.ContextFree UAM.ContextFree.Pumping

/-- The three-letter alphabet. -/
abbrev Sym := Fin 3

/-- Every letter has a different letter available. -/
theorem exists_ne (a : Sym) : ∃ j : Sym, j ≠ a := by revert a; decide

/-- Two letters never exhaust the three-letter alphabet. -/
theorem exists_ne₂ (a b : Sym) : ∃ j : Sym, j ≠ a ∧ j ≠ b := by revert a b; decide

/-- The word `aⁿbⁿcⁿ`. -/
def w3 (n : ℕ) : List Sym :=
  List.replicate n 0 ++ List.replicate n 1 ++ List.replicate n 2

/-- The language `{aⁿbⁿcⁿ}`. -/
def abc : Set (List Sym) := {w | ∃ n, w = w3 n}

@[simp] theorem length_w3 (n : ℕ) : (w3 n).length = 3 * n := by
  simp [w3]; ring

theorem count_w3 (j : Sym) (n : ℕ) : (w3 n).count j = n := by
  fin_cases j <;> simp [w3, List.count_replicate]

theorem sorted_w3 (n : ℕ) : (w3 n).Pairwise (· ≤ · : Sym → Sym → Prop) := by
  have hrep : ∀ (m : ℕ) (a : Sym), (List.replicate m a).Pairwise (· ≤ · : Sym → Sym → Prop) := by
    intro m a
    exact List.pairwise_replicate.2 (Or.inr le_rfl)
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨hrep n 0, hrep n 1, ?_⟩, hrep n 2, ?_⟩
  · intro a ha b hb
    rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
    decide
  · intro a ha b hb
    rcases List.mem_append.1 ha with h | h <;>
      rw [List.eq_of_mem_replicate h, List.eq_of_mem_replicate hb] <;> decide

theorem sorted_of_mem_abc {w : List Sym} (h : w ∈ abc) : w.Pairwise (· ≤ · : Sym → Sym → Prop) := by
  obtain ⟨n, rfl⟩ := h
  exact sorted_w3 n

theorem count_of_mem_abc {w : List Sym} (h : w ∈ abc) (i j : Sym) :
    w.count i = w.count j := by
  obtain ⟨n, rfl⟩ := h
  rw [count_w3, count_w3]

/-- A word whose square is sorted is constant. -/
theorem constant_of_sorted_self {v : List Sym} (h : (v ++ v).Pairwise (· ≤ · : Sym → Sym → Prop)) :
    ∀ a ∈ v, ∀ b ∈ v, a = b := by
  intro a ha b hb
  obtain ⟨-, -, hcross⟩ := List.pairwise_append.1 h
  exact le_antisymm (hcross a ha b hb) (hcross b hb a ha)

/-- A sorted word is sorted on every infix. -/
theorem sorted_of_infix {l m : List Sym} (hinf : l <:+: m) (h : m.Pairwise (· ≤ · : Sym → Sym → Prop)) :
    l.Pairwise (· ≤ · : Sym → Sym → Prop) :=
  h.sublist hinf.sublist

theorem count_eq_zero_of_notMem {l : List Sym} {j : Sym} (h : j ∉ l) : l.count j = 0 :=
  List.count_eq_zero.2 h

/-- **No grammar in Chomsky normal form generates `{aⁿbⁿcⁿ}`.** -/
theorem not_cnf_language {N : Type} [Fintype N] [DecidableEq N] (g : Grammar N Sym)
    (hcnf : IsCNF g) : g.language ≠ abc := by
  intro heq
  set k := Fintype.card N with hk
  set n := 2 ^ k with hn
  have hmem : w3 n ∈ g.language := by
    rw [heq]; exact ⟨n, rfl⟩
  have hlen : 2 ^ Fintype.card N ≤ (w3 n).length := by
    rw [length_w3, ← hk, ← hn]; omega
  obtain ⟨u, v, x, y, z, hsplit, hne, -, hpump⟩ := pumping_lemma hcnf hmem hlen
  -- pumping twice keeps the word sorted, so `v` and `y` are constant
  have hp2 : u ++ wpow v 2 ++ x ++ wpow y 2 ++ z ∈ abc := by
    rw [← heq]; exact hpump 2
  have hword2 : u ++ wpow v 2 ++ x ++ wpow y 2 ++ z = u ++ (v ++ v) ++ x ++ (y ++ y) ++ z := by
    simp [wpow]
  rw [hword2] at hp2
  have hs2 := sorted_of_mem_abc hp2
  have hvinf : v ++ v <:+: u ++ (v ++ v) ++ x ++ (y ++ y) ++ z :=
    ⟨u, x ++ (y ++ y) ++ z, by simp [List.append_assoc]⟩
  have hyinf : y ++ y <:+: u ++ (v ++ v) ++ x ++ (y ++ y) ++ z :=
    ⟨u ++ (v ++ v) ++ x, z, by simp [List.append_assoc]⟩
  have hvconst := constant_of_sorted_self (sorted_of_infix hvinf hs2)
  have hyconst := constant_of_sorted_self (sorted_of_infix hyinf hs2)
  -- pumping down to zero shifts all three letter counts by the same amount
  have hp0 : u ++ wpow v 0 ++ x ++ wpow y 0 ++ z ∈ abc := by
    rw [← heq]; exact hpump 0
  have hword0 : u ++ wpow v 0 ++ x ++ wpow y 0 ++ z = u ++ x ++ z := by simp [wpow]
  rw [hword0] at hp0
  have hw : w3 n = u ++ v ++ x ++ y ++ z := hsplit
  have hcount : ∀ j : Sym,
      u.count j + v.count j + x.count j + y.count j + z.count j = n := by
    intro j
    have := count_w3 j n
    rw [hw] at this
    simpa [List.count_append, Nat.add_assoc] using this
  have hcount0 : ∀ i j : Sym,
      u.count i + x.count i + z.count i = u.count j + x.count j + z.count j := by
    intro i j
    have := count_of_mem_abc hp0 i j
    simpa [List.count_append, Nat.add_assoc] using this
  -- a letter missing from both `v` and `y`
  have hzero : ∃ j : Sym, v.count j = 0 ∧ y.count j = 0 := by
    match hv : v, hy : y with
    | [], [] => exact absurd (by simp) hne
    | [], b :: y' =>
      obtain ⟨j, hj⟩ := exists_ne b
      refine ⟨j, by simp, count_eq_zero_of_notMem ?_⟩
      intro hmemj
      exact hj (hyconst j hmemj b (by simp))
    | a :: v', [] =>
      obtain ⟨j, hj⟩ := exists_ne a
      refine ⟨j, count_eq_zero_of_notMem ?_, by simp⟩
      intro hmemj
      exact hj (hvconst j hmemj a (by simp))
    | a :: v', b :: y' =>
      obtain ⟨j, hja, hjb⟩ := exists_ne₂ a b
      refine ⟨j, count_eq_zero_of_notMem ?_, count_eq_zero_of_notMem ?_⟩
      · intro hmemj
        exact hja (hvconst j hmemj a (by simp))
      · intro hmemj
        exact hjb (hyconst j hmemj b (by simp))
  obtain ⟨j₀, hvj, hyj⟩ := hzero
  -- hence every letter count of `v` and `y` vanishes, so both are empty
  have hall : ∀ j : Sym, v.count j + y.count j = 0 := by
    intro j
    have h1 := hcount j
    have h2 := hcount j₀
    have h3 := hcount0 j j₀
    omega
  have hvnil : v = [] := by
    rcases hv : v with _ | ⟨a, v'⟩
    · rfl
    · have : v.count a = 0 := by have := hall a; omega
      rw [hv] at this
      simp at this
  have hynil : y = [] := by
    rcases hy : y with _ | ⟨b, y'⟩
    · rfl
    · have : y.count b = 0 := by have := hall b; omega
      rw [hy] at this
      simp at this
  exact hne (by rw [hvnil, hynil]; rfl)

end UAM.ContextFree.AnBnCn
