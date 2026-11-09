import RequestProject.UAM_ContextFreePumping

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deciding membership in a context-free language

For a grammar in Chomsky normal form the derivation trees of a word are built
from the trees of its two nonempty halves, which is the recursion behind the
Cocke–Younger–Kasami algorithm.  This module implements that recursion as a
fuel-driven predicate, proves it sound and complete, and concludes that
membership in the language of such a grammar is decidable.

Main results:

* `UAM.ContextFree.Membership.derivFuel_sound` and `derivFuel_complete` — the
  recursion describes exactly the derivable pairs;
* `UAM.ContextFree.Membership.derivable_iff_derivFuel` — the characterisation
  used to decide derivability, with fuel the length of the word;
* `UAM.ContextFree.Membership.decidableDeriv` — derivability is decidable;
* `UAM.ContextFree.Membership.mem_language_iff_derivFuel` and `decidableMem` —
  membership in the language of a grammar in Chomsky normal form is decidable.
-/

namespace UAM.ContextFree.Membership

open UAM.ContextFree UAM.ContextFree.Pumping

universe u

variable {N T : Type u}

section

variable (g : Grammar N T) [Fintype N]
  [∀ (A : N) (β : List (N ⊕ T)), Decidable (g.rule A β)]

/-- The one-letter case of the recursion. -/
def LeafOk (A : N) (w : List T) : Prop :=
  match w with
  | [a] => g.rule A [Sum.inr a]
  | _ => False

instance decidableLeafOk (A : N) (w : List T) : Decidable (LeafOk g A w) := by
  match w with
  | [] => exact isFalse (fun h => h)
  | [a] => exact inferInstanceAs (Decidable (g.rule A [Sum.inr a]))
  | a :: b :: t => exact isFalse (fun h => h)

/-- The CYK recursion, driven by fuel: is `w` derivable from `A` by a tree using
at most `k` levels of splitting? -/
def DerivFuel : ℕ → N → List T → Prop
  | 0, _, _ => False
  | k + 1, A, w =>
      LeafOk g A w ∨
        ∃ i ∈ Finset.range w.length, 0 < i ∧
          ∃ B C : N, g.rule A [Sum.inl B, Sum.inl C] ∧
            DerivFuel k B (w.take i) ∧ DerivFuel k C (w.drop i)

instance decidableDerivFuel : ∀ (k : ℕ) (A : N) (w : List T), Decidable (DerivFuel g k A w)
  | 0, _, _ => inferInstanceAs (Decidable False)
  | k + 1, A, w =>
      have : ∀ (B : N) (v : List T), Decidable (DerivFuel g k B v) := decidableDerivFuel k
      inferInstanceAs (Decidable (LeafOk g A w ∨
        ∃ i ∈ Finset.range w.length, 0 < i ∧
          ∃ B C : N, g.rule A [Sum.inl B, Sum.inl C] ∧
            DerivFuel g k B (w.take i) ∧ DerivFuel g k C (w.drop i)))

omit [Fintype N] [∀ (A : N) (β : List (N ⊕ T)), Decidable (g.rule A β)] in
/-- Soundness of the recursion. -/
theorem derivFuel_sound :
    ∀ (k : ℕ) (A : N) (w : List T), DerivFuel g k A w → ∃ h, Deriv g h A w := by
  intro k
  induction k with
  | zero => intro A w hk; exact hk.elim
  | succ k ih =>
    intro A w hk
    rcases hk with hleaf | ⟨i, -, -, B, C, hrule, hleft, hright⟩
    · match w, hleaf with
      | [], h => exact h.elim
      | [a], hr => exact ⟨1, Deriv.leaf hr⟩
      | a :: b :: t, h => exact h.elim
    · obtain ⟨h₁, d₁⟩ := ih B (w.take i) hleft
      obtain ⟨h₂, d₂⟩ := ih C (w.drop i) hright
      refine ⟨max h₁ h₂ + 1, ?_⟩
      have := Deriv.node hrule d₁ d₂
      rwa [List.take_append_drop] at this

omit [Fintype N] [∀ (A : N) (β : List (N ⊕ T)), Decidable (g.rule A β)] in
/-- Completeness of the recursion. -/
theorem derivFuel_complete :
    ∀ (k : ℕ) (A : N) (w : List T) (h : ℕ), Deriv g h A w → w.length ≤ k →
      DerivFuel g k A w := by
  intro k
  induction k with
  | zero =>
    intro A w h d hlen
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) d.ne_nil
  | succ k ih =>
    intro A w h d hlen
    cases d with
    | @leaf A a hr => exact Or.inl hr
    | @node A B C h₁ h₂ u v hr d₁ d₂ =>
      have hupos : 0 < u.length := List.length_pos_iff.2 d₁.ne_nil
      have hvpos : 0 < v.length := List.length_pos_iff.2 d₂.ne_nil
      have hlenw : (u ++ v).length = u.length + v.length := by simp
      have htake : (u ++ v).take u.length = u := by simp
      have hdrop : (u ++ v).drop u.length = v := by simp
      refine Or.inr ⟨u.length, Finset.mem_range.2 (by omega), hupos, B, C, hr, ?_, ?_⟩
      · rw [htake]
        exact ih B u h₁ d₁ (by omega)
      · rw [hdrop]
        exact ih C v h₂ d₂ (by omega)

omit [Fintype N] [∀ (A : N) (β : List (N ⊕ T)), Decidable (g.rule A β)] in
/-- Derivability is decided by the recursion run with fuel the length of the
word. -/
theorem derivable_iff_derivFuel (A : N) (w : List T) :
    (∃ h, Deriv g h A w) ↔ DerivFuel g w.length A w :=
  ⟨fun ⟨h, d⟩ => derivFuel_complete g w.length A w h d le_rfl,
    fun hb => derivFuel_sound g w.length A w hb⟩

instance decidableDeriv (A : N) (w : List T) : Decidable (∃ h, Deriv g h A w) :=
  decidable_of_iff _ (derivable_iff_derivFuel g A w).symm

omit [Fintype N] [∀ (A : N) (β : List (N ⊕ T)), Decidable (g.rule A β)] in
/-- For a grammar in Chomsky normal form, membership in the language is decided
by the recursion. -/
theorem mem_language_iff_derivFuel (hcnf : IsCNF g) (w : List T) :
    w ∈ g.language ↔ DerivFuel g w.length g.start w := by
  rw [← derivable_iff_derivFuel]
  exact ⟨fun hw => deriv_of_yields hcnf hw, fun ⟨_, d⟩ => d.yields⟩

/-- **Membership in the language of a grammar in Chomsky normal form is
decidable.** -/
def decidableMem (hcnf : IsCNF g) (w : List T) : Decidable (w ∈ g.language) :=
  decidable_of_iff _ (mem_language_iff_derivFuel g hcnf w).symm

end

end UAM.ContextFree.Membership
