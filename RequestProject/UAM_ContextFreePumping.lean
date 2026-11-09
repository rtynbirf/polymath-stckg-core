import RequestProject.UAM_ContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The pumping lemma for context-free grammars

For a grammar in Chomsky normal form the derivations of a word are binary trees
labelled by nonterminals.  A word long enough forces such a tree to be deep, a
deep tree has a root path visiting some nonterminal twice, and the piece of the
derivation between the two visits can be repeated at will.  This is the
context-free pumping lemma, proved here for grammars in Chomsky normal form.

Main definitions:

* `UAM.ContextFree.Pumping.IsCNF` — every rule is `A → a` or `A → B C`;
* `UAM.ContextFree.Pumping.Deriv` — height-indexed derivation trees;
* `UAM.ContextFree.Pumping.DerivCtx` — derivation trees with a hole, i.e.
  derivations `A ⇒* v B y`;
* `UAM.ContextFree.Pumping.wpow` — repetition of a word.

Main results:

* `UAM.ContextFree.Pumping.Deriv.two_mul_length_le` — a tree of height `h`
  yields a word of length at most `2 ^ h / 2`;
* `UAM.ContextFree.Pumping.deriv_of_yields` — for a grammar in Chomsky normal
  form, every derivation from a nonterminal is a derivation tree;
* `UAM.ContextFree.Pumping.DerivCtx.plug` and `DerivCtx.iterate` — substitution
  into the hole, and its iteration;
* `UAM.ContextFree.Pumping.pumpable_of_card_lt` — a deep tree has a repeated
  nonterminal on a root path;
* `UAM.ContextFree.Pumping.pumping_lemma` — the pumping lemma itself.
-/

namespace UAM.ContextFree.Pumping

universe u

variable {N T : Type u}

/-- A grammar is in Chomsky normal form when every rule produces either a single
terminal or exactly two nonterminals. -/
def IsCNF (g : Grammar N T) : Prop :=
  ∀ A β, g.rule A β → (∃ a : T, β = [Sum.inr a]) ∨ (∃ B C : N, β = [Sum.inl B, Sum.inl C])

/-- Height-indexed derivation trees of a grammar in Chomsky normal form. -/
inductive Deriv (g : Grammar N T) : ℕ → N → List T → Prop
  | leaf {A : N} {a : T} : g.rule A [Sum.inr a] → Deriv g 1 A [a]
  | node {A B C : N} {h₁ h₂ : ℕ} {u v : List T} : g.rule A [Sum.inl B, Sum.inl C] →
      Deriv g h₁ B u → Deriv g h₂ C v → Deriv g (max h₁ h₂ + 1) A (u ++ v)

/-- Derivation trees with a hole: `DerivCtx g A D v y` says that `A` derives
`v ++ (something derived from D) ++ y`. -/
inductive DerivCtx (g : Grammar N T) : N → N → List T → List T → Prop
  | refl (A : N) : DerivCtx g A A [] []
  | left {A B C D : N} {h : ℕ} {v y u : List T} : g.rule A [Sum.inl B, Sum.inl C] →
      DerivCtx g B D v y → Deriv g h C u → DerivCtx g A D v (y ++ u)
  | right {A B C D : N} {h : ℕ} {u v y : List T} : g.rule A [Sum.inl B, Sum.inl C] →
      Deriv g h B u → DerivCtx g C D v y → DerivCtx g A D (u ++ v) y

/-! ## Elementary properties of derivation trees -/

theorem Deriv.ne_nil {g : Grammar N T} {h : ℕ} {A : N} {w : List T} (d : Deriv g h A w) :
    w ≠ [] := by
  induction d with
  | leaf => simp
  | node _ _ _ ih₁ _ =>
    intro hcon
    exact ih₁ (List.append_eq_nil_iff.1 hcon).1

theorem Deriv.pos {g : Grammar N T} {h : ℕ} {A : N} {w : List T} (d : Deriv g h A w) : 1 ≤ h := by
  induction d with
  | leaf => exact le_rfl
  | node => omega

/-- A derivation tree of height `h` yields a word of length at most `2 ^ h / 2`. -/
theorem Deriv.two_mul_length_le {g : Grammar N T} {h : ℕ} {A : N} {w : List T}
    (d : Deriv g h A w) : 2 * w.length ≤ 2 ^ h := by
  induction d with
  | leaf => simp
  | @node A B C h₁ h₂ u v _ _ _ ih₁ ih₂ =>
    have e₁ : (2 : ℕ) ^ h₁ ≤ 2 ^ max h₁ h₂ := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have e₂ : (2 : ℕ) ^ h₂ ≤ 2 ^ max h₁ h₂ := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have : 2 * (u ++ v).length = 2 * u.length + 2 * v.length := by
      simp [List.length_append]; ring
    rw [this, pow_succ]
    omega

/-! ## Derivation trees and the `Yields` relation -/

theorem Deriv.yields {g : Grammar N T} {h : ℕ} {A : N} {w : List T} (d : Deriv g h A w) :
    Yields g [Sum.inl A] w := by
  induction d with
  | @leaf A a hr =>
    have : Yields g [Sum.inr a] [a] := Yields.term Yields.nil
    simpa using Yields.nonterm hr this Yields.nil
  | @node A B C h₁ h₂ u v hr _ _ ih₁ ih₂ =>
    have hcat : Yields g ([Sum.inl B] ++ [Sum.inl C]) (u ++ v) := ih₁.append ih₂
    simpa using Yields.nonterm hr (by simpa using hcat) Yields.nil

/-- For a grammar in Chomsky normal form, a derivation from a list of
nonterminals splits into derivation trees. -/
theorem deriv_of_yields_aux {g : Grammar N T} (hcnf : IsCNF g) {α : List (N ⊕ T)} {w : List T}
    (hy : Yields g α w) :
    ∀ As : List N, α = As.map Sum.inl →
      ∃ ws : List (List T), w = ws.flatten ∧
        List.Forall₂ (fun (A : N) (u : List T) => ∃ h, Deriv g h A u) As ws := by
  induction hy with
  | nil =>
    intro As hAs
    cases As with
    | nil => exact ⟨[], rfl, List.Forall₂.nil⟩
    | cons A As' => simp at hAs
  | term _ _ =>
    intro As hAs
    cases As with
    | nil => simp at hAs
    | cons A As' => simp at hAs
  | @nonterm A₀ β α₀ u w₀ hr hβ _ ihβ ihrest =>
    intro As hAs
    cases As with
    | nil => simp at hAs
    | cons A As' =>
      simp only [List.map_cons, List.cons.injEq, Sum.inl.injEq] at hAs
      obtain ⟨rfl, hα⟩ := hAs
      obtain ⟨ws', hw', hall'⟩ := ihrest As' hα
      rcases hcnf _ _ hr with ⟨a, rfl⟩ | ⟨B, C, rfl⟩
      · -- terminal rule: `u = [a]`
        have hu : u = [a] := by
          cases hβ with
          | term hrest => rw [hrest.eq_nil_of_nil]
        subst hu
        exact ⟨[a] :: ws', by simp [hw'], List.Forall₂.cons ⟨1, Deriv.leaf hr⟩ hall'⟩
      · -- binary rule
        obtain ⟨ws, hws, hall⟩ := ihβ [B, C] (by simp)
        obtain ⟨u₁, u₂, rfl⟩ : ∃ u₁ u₂, ws = [u₁, u₂] := by
          cases hall with
          | cons _ h2 =>
            cases h2 with
            | cons _ h3 => cases h3; exact ⟨_, _, rfl⟩
        rcases hall with _ | ⟨⟨h₁, d₁⟩, hall2⟩
        rcases hall2 with _ | ⟨⟨h₂, d₂⟩, -⟩
        refine ⟨(u₁ ++ u₂) :: ws', ?_, List.Forall₂.cons ⟨_, Deriv.node hr d₁ d₂⟩ hall'⟩
        simp [hws, hw', List.append_assoc]

/-- For a grammar in Chomsky normal form, every derivation from a nonterminal is
witnessed by a derivation tree. -/
theorem deriv_of_yields {g : Grammar N T} (hcnf : IsCNF g) {A : N} {w : List T}
    (hy : Yields g [Sum.inl A] w) : ∃ h, Deriv g h A w := by
  obtain ⟨ws, hw, hall⟩ := deriv_of_yields_aux hcnf hy [A] (by simp)
  rcases hall with _ | ⟨⟨h, d⟩, hall2⟩
  cases hall2
  refine ⟨h, ?_⟩
  simpa [hw] using d

/-! ## Substitution into a hole -/

/-- Filling the hole of a context with a derivation tree. -/
theorem DerivCtx.plug {g : Grammar N T} {A D : N} {v y x : List T} {h : ℕ}
    (c : DerivCtx g A D v y) (d : Deriv g h D x) : ∃ h', Deriv g h' A (v ++ x ++ y) := by
  induction c with
  | refl A => exact ⟨h, by simpa using d⟩
  | @left A B C D h' v y u hr _ dC ih =>
    obtain ⟨hB, dB⟩ := ih d
    refine ⟨max hB h' + 1, ?_⟩
    have := Deriv.node hr dB dC
    simpa [List.append_assoc] using this
  | @right A B C D h' u v y hr dB _ ih =>
    obtain ⟨hC, dC⟩ := ih d
    refine ⟨max h' hC + 1, ?_⟩
    have := Deriv.node hr dB dC
    simpa [List.append_assoc] using this

/-- Contexts compose. -/
theorem DerivCtx.trans {g : Grammar N T} {A D E : N} {v y v' y' : List T}
    (c : DerivCtx g A D v y) (c' : DerivCtx g D E v' y') :
    DerivCtx g A E (v ++ v') (y' ++ y) := by
  induction c with
  | refl A => simpa using c'
  | @left A B C D h v y u hr _ dC ih =>
    have := DerivCtx.left hr (ih c') dC
    simpa [List.append_assoc] using this
  | @right A B C D h u v y hr dB _ ih =>
    have := DerivCtx.right hr dB (ih c')
    simpa [List.append_assoc] using this

/-- Every derivation tree deeper than `k` has a subtree of height exactly
`k + 1`. -/
theorem exists_subtree_of_lt {g : Grammar N T} {h : ℕ} {A : N} {w : List T}
    (d : Deriv g h A w) {k : ℕ} (hk : k < h) :
    ∃ (u z : List T) (D : N) (x : List T),
      DerivCtx g A D u z ∧ Deriv g (k + 1) D x ∧ w = u ++ x ++ z := by
  induction d with
  | @leaf A a hr =>
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨[], [], A, [a], DerivCtx.refl A, Deriv.leaf hr, by simp⟩
  | @node A B C h₁ h₂ u v hr dB dC ihB ihC =>
    by_cases hcase : k + 1 = max h₁ h₂ + 1
    · refine ⟨[], [], A, u ++ v, DerivCtx.refl A, ?_, by simp⟩
      rw [hcase]
      exact Deriv.node hr dB dC
    · have hlt : k < max h₁ h₂ := by omega
      rcases le_total h₂ h₁ with hle | hle
      · have hk1 : k < h₁ := by rwa [max_eq_left hle] at hlt
        obtain ⟨u', z', D, x, c, dx, hxeq⟩ := ihB hk1
        exact ⟨u', z' ++ v, D, x, DerivCtx.left hr c dC, dx, by
          rw [hxeq]; simp [List.append_assoc]⟩
      · have hk2 : k < h₂ := by rwa [max_eq_right hle] at hlt
        obtain ⟨u', z', D, x, c, dx, hxeq⟩ := ihC hk2
        exact ⟨u ++ u', z', D, x, DerivCtx.right hr dB c, dx, by
          rw [hxeq]; simp [List.append_assoc]⟩

/-- Repetition of a word. -/
def wpow (w : List T) : ℕ → List T
  | 0 => []
  | i + 1 => w ++ wpow w i

@[simp] theorem wpow_zero (w : List T) : wpow w 0 = [] := rfl

theorem wpow_succ (w : List T) (i : ℕ) : wpow w (i + 1) = w ++ wpow w i := rfl

theorem wpow_succ' (w : List T) (i : ℕ) : wpow w (i + 1) = wpow w i ++ w := by
  induction i with
  | zero => simp [wpow]
  | succ i ih => rw [wpow_succ w (i + 1), ih, ← List.append_assoc, ← wpow_succ w i, ih]

/-- Iterating a self-referential context pumps the word it surrounds. -/
theorem DerivCtx.iterate {g : Grammar N T} {D : N} {v y x : List T} {h : ℕ}
    (c : DerivCtx g D D v y) (d : Deriv g h D x) :
    ∀ i : ℕ, ∃ h', Deriv g h' D (wpow v i ++ x ++ wpow y i) := by
  intro i
  induction i with
  | zero => exact ⟨h, by simpa using d⟩
  | succ i ih =>
    obtain ⟨h', d'⟩ := ih
    obtain ⟨h'', d''⟩ := c.plug d'
    refine ⟨h'', ?_⟩
    rw [wpow_succ, wpow_succ' y i]
    simpa [List.append_assoc] using d''

/-! ## A deep tree repeats a nonterminal -/

/-- `w` is pumpable at `A`: some nonterminal repeats along a root path of a
derivation of `w` from `A`. -/
def Pumpable (g : Grammar N T) (A : N) (w : List T) : Prop :=
  ∃ (D : N) (u z v y x : List T),
    DerivCtx g A D u z ∧ DerivCtx g D D v y ∧ v ++ y ≠ [] ∧ (∃ h, Deriv g h D x) ∧
      w = u ++ (v ++ x ++ y) ++ z

theorem Pumpable.left_extend {g : Grammar N T} {A B C : N} {u v : List T} {h : ℕ}
    (hr : g.rule A [Sum.inl B, Sum.inl C]) (hp : Pumpable g B u) (dC : Deriv g h C v) :
    Pumpable g A (u ++ v) := by
  obtain ⟨D, u₁, z₁, vc, yc, x, c₁, cloop, hne, hx, rfl⟩ := hp
  exact ⟨D, u₁, z₁ ++ v, vc, yc, x, DerivCtx.left hr c₁ dC, cloop, hne, hx, by
    simp [List.append_assoc]⟩

theorem Pumpable.right_extend {g : Grammar N T} {A B C : N} {u v : List T} {h : ℕ}
    (hr : g.rule A [Sum.inl B, Sum.inl C]) (dB : Deriv g h B u) (hp : Pumpable g C v) :
    Pumpable g A (u ++ v) := by
  obtain ⟨D, u₁, z₁, vc, yc, x, c₁, cloop, hne, hx, rfl⟩ := hp
  exact ⟨D, u ++ u₁, z₁, vc, yc, x, DerivCtx.right hr dB c₁, cloop, hne, hx, by
    simp [List.append_assoc]⟩

/-- Descending a derivation tree: either a nonterminal repeats along a root path,
or the path reaches a nonterminal outside the given set. -/
theorem descend {g : Grammar N T} [DecidableEq N] {h : ℕ} {A : N} {w : List T}
    (d : Deriv g h A w) :
    ∀ S : Finset N, S.card < h →
      Pumpable g A w ∨ ∃ (D : N) (v y x : List T), D ∉ S ∧ DerivCtx g A D v y ∧
        (∃ h', Deriv g h' D x) ∧ w = v ++ x ++ y := by
  induction d with
  | @leaf A a hr =>
    intro S hS
    have hempty : S = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hempty
    exact Or.inr ⟨A, [], [], [a], by simp, DerivCtx.refl A, ⟨1, Deriv.leaf hr⟩, by simp⟩
  | @node A B C h₁ h₂ u v hr dB dC ihB ihC =>
    intro S hS
    by_cases hA : A ∈ S
    · have he : (S.erase A).card = S.card - 1 := Finset.card_erase_of_mem hA
      have hpos : 0 < S.card := Finset.card_pos.2 ⟨A, hA⟩
      have hcard : (S.erase A).card < max h₁ h₂ := by omega
      rcases le_total h₂ h₁ with hle | hle
      · -- the left subtree is at least as deep
        have hlt : (S.erase A).card < h₁ := by
          rw [max_eq_left hle] at hcard; exact hcard
        rcases ihB (S.erase A) hlt with hp | ⟨D, v', y', x, hD, c, hx, rfl⟩
        · exact Or.inl (hp.left_extend hr dC)
        · by_cases hDA : D = A
          · subst hDA
            refine Or.inl ⟨D, [], [], v', y' ++ v, x, DerivCtx.refl D,
              DerivCtx.left hr c dC, ?_, hx, by simp [List.append_assoc]⟩
            intro hcontra
            exact dC.ne_nil (by
              have := List.append_eq_nil_iff.1 hcontra
              have := List.append_eq_nil_iff.1 this.2
              exact this.2)
          · have hDS : D ∉ S := by
              intro hDS
              exact hD (Finset.mem_erase.2 ⟨hDA, hDS⟩)
            exact Or.inr ⟨D, v', y' ++ v, x, hDS, DerivCtx.left hr c dC, hx, by
              simp [List.append_assoc]⟩
      · -- the right subtree is at least as deep
        have hlt : (S.erase A).card < h₂ := by
          rw [max_eq_right hle] at hcard; exact hcard
        rcases ihC (S.erase A) hlt with hp | ⟨D, v', y', x, hD, c, hx, rfl⟩
        · exact Or.inl (hp.right_extend hr dB)
        · by_cases hDA : D = A
          · subst hDA
            refine Or.inl ⟨D, [], [], u ++ v', y', x, DerivCtx.refl D,
              DerivCtx.right hr dB c, ?_, hx, by simp [List.append_assoc]⟩
            intro hcontra
            exact dB.ne_nil (by
              have h1 := List.append_eq_nil_iff.1 hcontra
              have h2 := List.append_eq_nil_iff.1 h1.1
              exact h2.1)
          · have hDS : D ∉ S := by
              intro hDS
              exact hD (Finset.mem_erase.2 ⟨hDA, hDS⟩)
            exact Or.inr ⟨D, u ++ v', y', x, hDS, DerivCtx.right hr dB c, hx, by
              simp [List.append_assoc]⟩
    · exact Or.inr ⟨A, [], [], u ++ v, hA, DerivCtx.refl A, ⟨_, Deriv.node hr dB dC⟩, by simp⟩

/-- A derivation tree deeper than the number of nonterminals repeats a
nonterminal along a root path. -/
theorem pumpable_of_card_lt {g : Grammar N T} [Fintype N] [DecidableEq N] {h : ℕ} {A : N}
    {w : List T} (d : Deriv g h A w) (hcard : Fintype.card N < h) : Pumpable g A w := by
  rcases descend d Finset.univ (by simpa using hcard) with hp | ⟨D, _, _, _, hD, -⟩
  · exact hp
  · exact absurd (Finset.mem_univ D) hD

/-! ## The pumping lemma -/

/-- Pumping inside a shallow subtree: the repeated nonterminal can be found so
that the surrounding derivation yields a word of length at most `2 ^ k`. -/
theorem pumpable_bounded {g : Grammar N T} [Fintype N] [DecidableEq N] {h : ℕ} {A : N}
    {w : List T} (d : Deriv g h A w) (hcard : Fintype.card N < h) :
    ∃ (u z : List T) (D : N) (v y x : List T),
      DerivCtx g A D u z ∧ DerivCtx g D D v y ∧ v ++ y ≠ [] ∧ (∃ h', Deriv g h' D x) ∧
        w = u ++ (v ++ x ++ y) ++ z ∧ (v ++ x ++ y).length ≤ 2 ^ Fintype.card N := by
  obtain ⟨u₀, z₀, D₀, x₀, c₀, d₀, hw⟩ := exists_subtree_of_lt d hcard
  have hbound : 2 * x₀.length ≤ 2 ^ (Fintype.card N + 1) := d₀.two_mul_length_le
  obtain ⟨D, u₁, z₁, v, y, x, c₁, cloop, hne, hx, hx₀⟩ :=
    pumpable_of_card_lt d₀ (Nat.lt_succ_self _)
  refine ⟨u₀ ++ u₁, z₁ ++ z₀, D, v, y, x, c₀.trans c₁, cloop, hne, hx, ?_, ?_⟩
  · rw [hw, hx₀]; simp [List.append_assoc]
  · have hlen : (v ++ x ++ y).length ≤ x₀.length := by
      rw [hx₀]; simp [List.append_assoc]; omega
    have hpow : (2 : ℕ) ^ (Fintype.card N + 1) = 2 * 2 ^ Fintype.card N := by ring
    omega

/-- **Pumping lemma for context-free grammars.**  For a grammar in Chomsky
normal form with `k` nonterminals, every word of the language of length at least
`2 ^ k` splits as `u v x y z` with `v y` nonempty and `v x y` short, so that
`u vⁱ x yⁱ z` belongs to the language for every `i`. -/
theorem pumping_lemma {g : Grammar N T} [Fintype N] [DecidableEq N] (hcnf : IsCNF g)
    {w : List T} (hw : w ∈ g.language) (hlen : 2 ^ Fintype.card N ≤ w.length) :
    ∃ u v x y z : List T, w = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧
      (v ++ x ++ y).length ≤ 2 ^ Fintype.card N ∧
      ∀ i : ℕ, u ++ wpow v i ++ x ++ wpow y i ++ z ∈ g.language := by
  obtain ⟨h, d⟩ := deriv_of_yields hcnf hw
  have hdeep : Fintype.card N < h := by
    by_contra hcon
    push_neg at hcon
    have h1 : 2 * w.length ≤ 2 ^ h := d.two_mul_length_le
    have h2 : (2 : ℕ) ^ h ≤ 2 ^ Fintype.card N := Nat.pow_le_pow_right (by norm_num) hcon
    have h3 : (0 : ℕ) < 2 ^ Fintype.card N := Nat.pow_pos (by norm_num)
    omega
  obtain ⟨u, z, D, v, y, x, cout, cloop, hne, ⟨hx, dx⟩, rfl, hshort⟩ := pumpable_bounded d hdeep
  refine ⟨u, v, x, y, z, by simp [List.append_assoc], hne, hshort, fun i => ?_⟩
  obtain ⟨h', d'⟩ := cloop.iterate dx i
  obtain ⟨h'', d''⟩ := cout.plug d'
  have : Yields g [Sum.inl g.start] (u ++ (wpow v i ++ x ++ wpow y i) ++ z) := d''.yields
  simpa [Grammar.language, List.append_assoc] using this

/-! ## A grammar the lemma applies to -/

/-- A one-nonterminal grammar in Chomsky normal form: `S → a` and `S → S S`. -/
def plusGrammar : Grammar Unit Bool where
  rule := fun _ β => β = [Sum.inr true] ∨ β = [Sum.inl (), Sum.inl ()]
  start := ()

theorem plusGrammar_isCNF : IsCNF plusGrammar := by
  rintro A β (rfl | rfl)
  · exact Or.inl ⟨true, rfl⟩
  · exact Or.inr ⟨(), (), rfl⟩

theorem single_mem_plusGrammar : [true] ∈ plusGrammar.language := by
  have : Yields plusGrammar [Sum.inl ()] ([true] ++ []) :=
    Yields.nonterm (Or.inl rfl) (Yields.term Yields.nil) Yields.nil
  simpa [Grammar.language] using this

theorem pair_mem_plusGrammar : [true, true] ∈ plusGrammar.language := by
  have hsingle : Yields plusGrammar [Sum.inl ()] [true] := single_mem_plusGrammar
  have hpair : Yields plusGrammar ([Sum.inl ()] ++ [Sum.inl ()]) ([true] ++ [true]) :=
    hsingle.append hsingle
  have : Yields plusGrammar [Sum.inl ()] ([true, true] ++ []) :=
    Yields.nonterm (Or.inr rfl) (by simpa using hpair) Yields.nil
  simpa [Grammar.language] using this

/-- The hypotheses of the pumping lemma are satisfiable. -/
theorem pumping_lemma_applies :
    ∃ u v x y z : List Bool, [true, true] = u ++ v ++ x ++ y ++ z ∧ v ++ y ≠ [] ∧
      (v ++ x ++ y).length ≤ 2 ^ Fintype.card Unit ∧
      ∀ i : ℕ, u ++ wpow v i ++ x ++ wpow y i ++ z ∈ plusGrammar.language :=
  pumping_lemma plusGrammar_isCNF pair_mem_plusGrammar (by simp)

end UAM.ContextFree.Pumping
