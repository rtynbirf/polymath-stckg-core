import RequestProject.Atlas.UAM_NFA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The shuffle of two regular languages

`Interleave x y z` says that `z` is an interleaving of `x` and `y`, and

  `shuffle L₁ L₂ = {z | ∃ x ∈ L₁, ∃ y ∈ L₂, Interleave x y z}`.

The main theorem `isRegular_shuffle` is that the shuffle of two regular
languages is regular.  The automaton is the asynchronous product: its states are
pairs, and on reading a letter it nondeterministically feeds the letter to the
left or to the right component.  `mem_shuffleNFA_evalFrom` is the exact
description of its reachable pairs, from which the language identity follows.
-/

namespace UAM.Shuffle

variable {α : Type} {σ₁ σ₂ : Type}

/-! ## Interleavings -/

/-- `Interleave x y z` : the word `z` is an interleaving of `x` and `y`. -/
inductive Interleave : List α → List α → List α → Prop
  | nil : Interleave [] [] []
  | left {a : α} {x y z : List α} : Interleave x y z → Interleave (a :: x) y (a :: z)
  | right {a : α} {x y z : List α} : Interleave x y z → Interleave x (a :: y) (a :: z)

theorem interleave_nil_iff {x y : List α} : Interleave x y [] ↔ x = [] ∧ y = [] := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact Interleave.nil

theorem interleave_cons_iff {a : α} {x y z : List α} :
    Interleave x y (a :: z) ↔
      (∃ x', x = a :: x' ∧ Interleave x' y z) ∨ (∃ y', y = a :: y' ∧ Interleave x y' z) := by
  constructor
  · intro h
    cases h with
    | left h => exact Or.inl ⟨_, rfl, h⟩
    | right h => exact Or.inr ⟨_, rfl, h⟩
  · rintro (⟨x', rfl, h⟩ | ⟨y', rfl, h⟩)
    · exact Interleave.left h
    · exact Interleave.right h

theorem interleave_nil_left_of {x y z : List α} (h : Interleave x y z) (hx : x = []) : y = z := by
  induction h with
  | nil => rfl
  | left _ _ => exact absurd hx (by simp)
  | right _ ih => rw [ih hx]

theorem interleave_nil_left_self (z : List α) : Interleave [] z z := by
  induction z with
  | nil => exact Interleave.nil
  | cons a z ih => exact Interleave.right ih

@[simp] theorem interleave_nil_left {y z : List α} : Interleave [] y z ↔ y = z :=
  ⟨fun h => interleave_nil_left_of h rfl, fun h => h ▸ interleave_nil_left_self y⟩

/-- The shuffle of two languages. -/
def shuffle (L₁ L₂ : Language α) : Language α :=
  {z | ∃ x ∈ L₁, ∃ y ∈ L₂, Interleave x y z}

theorem mem_shuffle_iff {L₁ L₂ : Language α} {z : List α} :
    z ∈ shuffle L₁ L₂ ↔ ∃ x ∈ L₁, ∃ y ∈ L₂, Interleave x y z := Iff.rfl

/-! ## The asynchronous product automaton -/

/-- The asynchronous product of two deterministic automata: each letter is fed
to one of the two components. -/
def shuffleNFA (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) : NFA α (σ₁ × σ₂) where
  step p a := {(M₁.step p.1 a, p.2), (p.1, M₂.step p.2 a)}
  start := {(M₁.start, M₂.start)}
  accept := {p | p.1 ∈ M₁.accept ∧ p.2 ∈ M₂.accept}

/-- **The reachable pairs of the asynchronous product** are exactly the pairs
reached by splitting the input into an interleaving. -/
theorem mem_shuffleNFA_evalFrom (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) (p : σ₁) (q : σ₂)
    (z : List α) (r : σ₁ × σ₂) :
    r ∈ (shuffleNFA M₁ M₂).evalFrom {(p, q)} z ↔
      ∃ x y, Interleave x y z ∧ M₁.evalFrom p x = r.1 ∧ M₂.evalFrom q y = r.2 := by
  induction z generalizing p q with
  | nil =>
    rw [NFA.evalFrom_nil]
    constructor
    · intro h
      rw [Set.mem_singleton_iff] at h
      exact ⟨[], [], Interleave.nil, by simp [h], by simp [h]⟩
    · rintro ⟨x, y, hs, hx, hy⟩
      obtain ⟨rfl, rfl⟩ := interleave_nil_iff.1 hs
      simp only [DFA.evalFrom_nil] at hx hy
      rw [Set.mem_singleton_iff]
      exact Prod.ext_iff.2 ⟨hx.symm, hy.symm⟩
  | cons a z ih =>
    rw [NFA.evalFrom_cons, NFA.mem_evalFrom_iff_exists]
    constructor
    · rintro ⟨t, ht, hr⟩
      obtain ⟨s, hs, hts⟩ := NFA.mem_stepSet.1 ht
      rw [Set.mem_singleton_iff] at hs
      subst hs
      rcases hts with h | h
      · subst h
        obtain ⟨x, y, hsh, hx, hy⟩ := (ih (M₁.step p a) q).1 hr
        exact ⟨a :: x, y, Interleave.left hsh, by rw [DFA.evalFrom_cons]; exact hx, hy⟩
      · subst h
        obtain ⟨x, y, hsh, hx, hy⟩ := (ih p (M₂.step q a)).1 hr
        exact ⟨x, a :: y, Interleave.right hsh, hx, by rw [DFA.evalFrom_cons]; exact hy⟩
    · rintro ⟨x, y, hsh, hx, hy⟩
      rcases interleave_cons_iff.1 hsh with ⟨x', rfl, hsh'⟩ | ⟨y', rfl, hsh'⟩
      · refine ⟨(M₁.step p a, q), NFA.mem_stepSet.2 ⟨(p, q), rfl, Or.inl rfl⟩, ?_⟩
        refine (ih (M₁.step p a) q).2 ⟨x', y, hsh', ?_, hy⟩
        rw [DFA.evalFrom_cons] at hx
        exact hx
      · refine ⟨(p, M₂.step q a), NFA.mem_stepSet.2 ⟨(p, q), rfl, Or.inr rfl⟩, ?_⟩
        refine (ih p (M₂.step q a)).2 ⟨x, y', hsh', hx, ?_⟩
        rw [DFA.evalFrom_cons] at hy
        exact hy

/-- The asynchronous product accepts the shuffle of the two languages. -/
theorem shuffleNFA_accepts (M₁ : DFA α σ₁) (M₂ : DFA α σ₂) :
    (shuffleNFA M₁ M₂).accepts = shuffle M₁.accepts M₂.accepts := by
  ext z
  rw [NFA.mem_accepts, mem_shuffle_iff]
  constructor
  · rintro ⟨r, hr, hmem⟩
    obtain ⟨x, y, hsh, hx, hy⟩ :=
      (mem_shuffleNFA_evalFrom M₁ M₂ M₁.start M₂.start z r).1 hmem
    refine ⟨x, ?_, y, ?_, hsh⟩
    · rw [DFA.mem_accepts, DFA.eval, hx]; exact hr.1
    · rw [DFA.mem_accepts, DFA.eval, hy]; exact hr.2
  · rintro ⟨x, hx, y, hy, hsh⟩
    refine ⟨(M₁.evalFrom M₁.start x, M₂.evalFrom M₂.start y), ⟨hx, hy⟩, ?_⟩
    exact (mem_shuffleNFA_evalFrom M₁ M₂ M₁.start M₂.start z _).2 ⟨x, y, hsh, rfl, rfl⟩

/-- **The shuffle of two regular languages is regular.** -/
theorem isRegular_shuffle {L₁ L₂ : Language α} (h₁ : L₁.IsRegular) (h₂ : L₂.IsRegular) :
    (shuffle L₁ L₂).IsRegular := by
  obtain ⟨σ₁, hσ₁, M₁, rfl⟩ := h₁
  obtain ⟨σ₂, hσ₂, M₂, rfl⟩ := h₂
  exact UAM.NFA.isRegular_of_isNFARegular
    ⟨σ₁ × σ₂, inferInstance, shuffleNFA M₁ M₂, shuffleNFA_accepts M₁ M₂⟩

/-! ## Elementary properties of the shuffle -/

theorem interleave_comm {x y z : List α} (h : Interleave x y z) : Interleave y x z := by
  induction h with
  | nil => exact Interleave.nil
  | left _ ih => exact Interleave.right ih
  | right _ ih => exact Interleave.left ih

theorem shuffle_comm (L₁ L₂ : Language α) : shuffle L₁ L₂ = shuffle L₂ L₁ := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, hsh⟩
    exact ⟨y, hy, x, hx, interleave_comm hsh⟩
  · rintro ⟨x, hx, y, hy, hsh⟩
    exact ⟨y, hy, x, hx, interleave_comm hsh⟩

theorem length_of_interleave {x y z : List α} (h : Interleave x y z) :
    z.length = x.length + y.length := by
  induction h with
  | nil => rfl
  | left _ ih => simp only [List.length_cons, ih]; omega
  | right _ ih => simp only [List.length_cons, ih]; omega

theorem shuffle_one (L : Language α) : shuffle L {[]} = L := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, hsh⟩
    rw [show y = [] from hy] at hsh
    have hxz : x = z := interleave_nil_left.1 (interleave_comm hsh)
    exact hxz ▸ hx
  · intro hz
    exact ⟨z, hz, [], rfl, interleave_comm (interleave_nil_left.2 rfl)⟩

end UAM.Shuffle
