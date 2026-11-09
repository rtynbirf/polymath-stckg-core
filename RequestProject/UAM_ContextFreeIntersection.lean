import RequestProject.UAM_ContextFreeClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Context-free ∩ regular is context-free

The intersection of a context-free language with a *regular* language is again
context-free.  This module proves it by the classical triple construction: the
nonterminals of the product grammar are triples `(p, A, q)`, read as "`A`
derives a word driving the automaton from state `p` to state `q`".

* `UAM.ContextFree.Threaded` — the relation that threads automaton states
  through a sentential form;
* `UAM.ContextFree.prodGrammar` — the triple grammar;
* `UAM.ContextFree.prodGrammar_language` — it generates exactly the
  intersection;
* `UAM.ContextFree.IsContextFree.inter_regular` — the closure statement.
-/

namespace UAM.ContextFree

universe u

variable {N T σ : Type u}

/-! ## Threading automaton states through a sentential form -/

/-- `Threaded M p α α' q` says that `α'` is the sentential form `α` with
automaton states threaded through it, starting at `p` and ending at `q`:
terminals advance the state, and each nonterminal `A` is annotated with the
states it is required to run between. -/
inductive Threaded (M : DFA T σ) :
    σ → List (N ⊕ T) → List ((Option (σ × N × σ)) ⊕ T) → σ → Prop
  | nil (p : σ) : Threaded M p [] [] p
  | term {p q : σ} {a : T} {α : List (N ⊕ T)} {α' : List ((Option (σ × N × σ)) ⊕ T)} :
      Threaded M (M.step p a) α α' q →
      Threaded M p (Sum.inr a :: α) (Sum.inr a :: α') q
  | nonterm {p r q : σ} {A : N} {α : List (N ⊕ T)} {α' : List ((Option (σ × N × σ)) ⊕ T)} :
      Threaded M r α α' q →
      Threaded M p (Sum.inl A :: α) (Sum.inl (some (p, A, r)) :: α') q

/-- The triple grammar of a grammar and an automaton.  The fresh start symbol
`none` may launch a derivation from the automaton's start state to any accepting
state. -/
def prodGrammar (g : Grammar N T) (M : DFA T σ) : Grammar (Option (σ × N × σ)) T where
  rule C γ :=
    match C with
    | none => ∃ f ∈ M.accept, γ = [Sum.inl (some (M.start, g.start, f))]
    | some (p, A, q) => ∃ β, g.rule A β ∧ Threaded M p β γ q
  start := none


/-! ## Inversion for the threading relation -/

theorem threaded_nil_inv {M : DFA T σ} {p q : σ} {α : List (N ⊕ T)}
    (h : Threaded M p α [] q) : α = [] ∧ p = q := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

theorem threaded_cons_inr_inv {M : DFA T σ} {p q : σ} {a : T} {α : List (N ⊕ T)}
    {rest : List ((Option (σ × N × σ)) ⊕ T)}
    (h : Threaded M p α (Sum.inr a :: rest) q) :
    ∃ αtail, α = Sum.inr a :: αtail ∧ Threaded M (M.step p a) αtail rest q := by
  cases h with
  | term hrest => exact ⟨_, rfl, hrest⟩

theorem threaded_cons_inl_inv {M : DFA T σ} {p q : σ} {B : Option (σ × N × σ)}
    {α : List (N ⊕ T)} {rest : List ((Option (σ × N × σ)) ⊕ T)}
    (h : Threaded M p α (Sum.inl B :: rest) q) :
    ∃ (A : N) (r : σ) (αtail : List (N ⊕ T)),
      α = Sum.inl A :: αtail ∧ B = some (p, A, r) ∧ Threaded M r αtail rest q := by
  cases h with
  | nonterm hrest => exact ⟨_, _, _, rfl, rfl, hrest⟩

/-! ## The two directions -/

/-- Every derivation of the triple grammar is a derivation of the original
grammar which, in addition, drives the automaton between the annotated
states. -/
theorem yields_of_yields_prod {g : Grammar N T} {M : DFA T σ}
    {α' : List ((Option (σ × N × σ)) ⊕ T)} {w : List T}
    (hy : Yields (prodGrammar g M) α' w) :
    ∀ (p q : σ) (α : List (N ⊕ T)), Threaded M p α α' q →
      Yields g α w ∧ M.evalFrom p w = q := by
  induction hy with
  | nil =>
    intro p q α ht
    obtain ⟨rfl, rfl⟩ := threaded_nil_inv ht
    exact ⟨Yields.nil, rfl⟩
  | @term a α'' w' _ ih =>
    intro p q α ht
    obtain ⟨αtail, rfl, hrest⟩ := threaded_cons_inr_inv ht
    obtain ⟨hy, hev⟩ := ih _ q _ hrest
    exact ⟨Yields.term hy, by rw [DFA.evalFrom_cons]; exact hev⟩
  | @nonterm B γ α'' u w' hr _ _ ihγ ihtail =>
    intro p q α ht
    obtain ⟨A, r, αtail, rfl, rfl, hrest⟩ := threaded_cons_inl_inv ht
    obtain ⟨β, hβ, hthread⟩ := hr
    obtain ⟨hyβ, hevβ⟩ := ihγ p r β hthread
    obtain ⟨hytail, hevtail⟩ := ihtail r q αtail hrest
    refine ⟨Yields.nonterm hβ hyβ hytail, ?_⟩
    rw [DFA.evalFrom_of_append, hevβ, hevtail]

/-- Every derivation of the original grammar can be threaded through the
automaton, giving a derivation of the triple grammar. -/
theorem yields_prod_of_yields {g : Grammar N T} {M : DFA T σ}
    {α : List (N ⊕ T)} {w : List T} (hy : Yields g α w) :
    ∀ p : σ, ∃ α' : List ((Option (σ × N × σ)) ⊕ T),
      Threaded M p α α' (M.evalFrom p w) ∧ Yields (prodGrammar g M) α' w := by
  induction hy with
  | nil => intro p; exact ⟨[], Threaded.nil p, Yields.nil⟩
  | @term a α₀ w₀ _ ih =>
    intro p
    obtain ⟨α', ht, hy'⟩ := ih (M.step p a)
    refine ⟨Sum.inr a :: α', ?_, Yields.term hy'⟩
    rw [DFA.evalFrom_cons]
    exact Threaded.term ht
  | @nonterm A β α₀ u w₀ hr _ _ ihβ ihtail =>
    intro p
    obtain ⟨γ, htβ, hyβ⟩ := ihβ p
    obtain ⟨α', httail, hytail⟩ := ihtail (M.evalFrom p u)
    refine ⟨Sum.inl (some (p, A, M.evalFrom p u)) :: α', ?_, ?_⟩
    · rw [DFA.evalFrom_of_append]
      exact Threaded.nonterm httail
    · exact Yields.nonterm ⟨β, hr, htβ⟩ hyβ hytail

/-! ## The language of the triple grammar -/

/-- **The triple grammar generates the intersection.** -/
theorem prodGrammar_language (g : Grammar N T) (M : DFA T σ) :
    (prodGrammar g M).language = g.language ⊓ M.accepts := by
  ext w
  constructor
  · intro hw
    obtain ⟨γ, hr, hγ⟩ := yields_singleton_inv hw
    obtain ⟨f, hf, rfl⟩ := hr
    have hthread : Threaded M M.start [Sum.inl g.start]
        [Sum.inl (some (M.start, g.start, f))] f :=
      Threaded.nonterm (Threaded.nil f)
    obtain ⟨hy, hev⟩ := yields_of_yields_prod hγ M.start f [Sum.inl g.start] hthread
    exact ⟨hy, (M.mem_accepts).2 (by rw [DFA.eval, hev]; exact hf)⟩
  · rintro ⟨hy, hacc⟩
    obtain ⟨α', ht, hy'⟩ := yields_prod_of_yields (M := M) hy M.start
    have hfin : M.evalFrom M.start w ∈ M.accept := (M.mem_accepts).1 hacc
    cases ht with
    | nonterm hrest =>
      rename_i r _
      cases hrest
      have hrule : (prodGrammar g M).rule none
          [Sum.inl (some (M.start, g.start, M.evalFrom M.start w))] :=
        ⟨M.evalFrom M.start w, hfin, rfl⟩
      have := Yields.nonterm (g := prodGrammar g M) (α := []) hrule hy' Yields.nil
      simpa [Grammar.language] using this

/-- **Context-free ∩ regular is context-free.** -/
theorem IsContextFree.inter_regular {L R : Language T}
    (hL : IsContextFree L) (hR : R.IsRegular) : IsContextFree (L ⊓ R) := by
  obtain ⟨N, g, rfl⟩ := hL
  obtain ⟨τ, -, M, rfl⟩ := hR
  refine ⟨Option (ULift.{u} τ × N × ULift.{u} τ),
    prodGrammar g (DFA.reindex Equiv.ulift.symm M), ?_⟩
  rw [prodGrammar_language, DFA.accepts_reindex]

/-- Context-free languages are closed under intersection with a regular language
on either side. -/
theorem IsContextFree.regular_inter {L R : Language T}
    (hR : R.IsRegular) (hL : IsContextFree L) : IsContextFree (R ⊓ L) := by
  have h := hL.inter_regular hR
  rwa [inf_comm] at h

end UAM.ContextFree
