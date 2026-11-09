import RequestProject.UAM_ContextFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Productive symbols and emptiness of a context-free language

A nonterminal is *productive* when it derives at least one terminal word.  This
module gives that notion an inductive definition — `A` is productive as soon as
some rule `A → β` has all of its nonterminals productive — and proves the
definition correct:

* `UAM.ContextFree.exists_yields_of_productive_symbols` — a sentential form all
  of whose nonterminals are productive derives some word;
* `UAM.ContextFree.productive_of_yields` — conversely, every nonterminal
  occurring in a derivable sentential form is productive;
* `UAM.ContextFree.productive_iff_exists_yields` — the two agree;
* `UAM.ContextFree.language_nonempty_iff_productive_start` — a grammar generates
  a nonempty language exactly when its start symbol is productive.

Because `Productive` is an inductive predicate, its introduction rule is a
*finitary* certificate of nonemptiness, while its eliminator gives the emptiness
argument: if no derivation of productivity exists, the language is empty.
-/

namespace UAM.ContextFree

universe u

variable {N T : Type u}

/-- `Productive g A` : the nonterminal `A` can be rewritten, by a rule all of
whose nonterminals are themselves productive, and hence derives a word. -/
inductive Productive (g : Grammar N T) : N → Prop
  | intro {A : N} {β : List (N ⊕ T)} :
      g.rule A β → (∀ B, Sum.inl B ∈ β → Productive g B) → Productive g A

/-- A sentential form whose nonterminals all derive words itself derives a
word. -/
theorem exists_yields_of_forall_exists {g : Grammar N T} :
    ∀ β : List (N ⊕ T), (∀ B, Sum.inl B ∈ β → ∃ w, Yields g [Sum.inl B] w) →
      ∃ u, Yields g β u := by
  intro β
  induction β with
  | nil => intro _; exact ⟨[], Yields.nil⟩
  | cons x β ih =>
      intro h
      obtain ⟨u, hu⟩ := ih fun B hB => h B (List.mem_cons_of_mem _ hB)
      cases x with
      | inr a => exact ⟨a :: u, Yields.term hu⟩
      | inl B =>
          obtain ⟨v, hv⟩ := h B List.mem_cons_self
          exact ⟨v ++ u, hv.append hu⟩

/-- Every nonterminal of a derivable sentential form is productive. -/
theorem productive_of_yields {g : Grammar N T} {α : List (N ⊕ T)} {w : List T}
    (h : Yields g α w) : ∀ B, Sum.inl B ∈ α → Productive g B := by
  induction h with
  | nil => intro B hB; cases hB
  | term _ ih =>
      intro B hB
      rcases List.mem_cons.1 hB with h' | h'
      · exact absurd h' (by simp)
      · exact ih B h'
  | nonterm hr _ _ ihβ ihα =>
      intro B hB
      rcases List.mem_cons.1 hB with h' | h'
      · have : B = _ := Sum.inl_injective h'
        exact this ▸ Productive.intro hr ihβ
      · exact ihα B h'

/-- A productive nonterminal derives a terminal word. -/
theorem exists_yields_of_productive {g : Grammar N T} {A : N} (h : Productive g A) :
    ∃ w, Yields g [Sum.inl A] w := by
  induction h with
  | @intro A β hr _ ih =>
      obtain ⟨u, hu⟩ := exists_yields_of_forall_exists β ih
      exact ⟨u ++ [], Yields.nonterm hr hu Yields.nil⟩

/-- A sentential form all of whose nonterminals are productive derives a word. -/
theorem exists_yields_of_productive_symbols {g : Grammar N T} {β : List (N ⊕ T)}
    (h : ∀ B, Sum.inl B ∈ β → Productive g B) : ∃ u, Yields g β u :=
  exists_yields_of_forall_exists β fun B hB => exists_yields_of_productive (h B hB)

/-- **Productivity is exactly derivability of a terminal word.** -/
theorem productive_iff_exists_yields {g : Grammar N T} {A : N} :
    Productive g A ↔ ∃ w, Yields g [Sum.inl A] w :=
  ⟨exists_yields_of_productive, fun ⟨_, hw⟩ => productive_of_yields hw A List.mem_cons_self⟩

/-- **Emptiness test.**  A grammar generates a nonempty language exactly when its
start symbol is productive. -/
theorem language_nonempty_iff_productive_start {g : Grammar N T} :
    g.language.Nonempty ↔ Productive g g.start := by
  rw [productive_iff_exists_yields]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw⟩, fun ⟨w, hw⟩ => ⟨w, hw⟩⟩

/-- A grammar generates the empty language exactly when its start symbol is not
productive. -/
theorem language_eq_empty_iff {g : Grammar N T} :
    g.language = ∅ ↔ ¬ Productive g g.start := by
  rw [← language_nonempty_iff_productive_start, Set.not_nonempty_iff_eq_empty]

/-- A nonterminal with no rule at all is not productive. -/
theorem not_productive_of_no_rule {g : Grammar N T} {A : N} (h : ∀ β, ¬ g.rule A β) :
    ¬ Productive g A := by
  intro hA
  cases hA with
  | intro hr _ => exact h _ hr

/-- Deleting all rules of a grammar leaves the empty language. -/
theorem language_empty_of_no_rules {g : Grammar N T} (h : ∀ A β, ¬ g.rule A β) :
    g.language = ∅ :=
  language_eq_empty_iff.2 (not_productive_of_no_rule (h g.start))

end UAM.ContextFree
