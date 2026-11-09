import RequestProject.UAM_ContextFreeFinitary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Agreement with Mathlib's context-free grammars

Mathlib models a context-free grammar as a `Finset` of rewrite rules together
with the reflexive transitive closure `ContextFreeGrammar.Derives` of one-step
rewriting, whereas this development uses the inductive derivation relation
`UAM.ContextFree.Yields` on a `Prop`-valued rule relation.  This module proves
that the two agree:

* `UAM.ContextFree.derives_of_yields` and `UAM.ContextFree.yields_of_derives` —
  the derivation relations correspond, for any grammar and rule set matching
  under `UAM.ContextFree.RuleCompat`;
* `UAM.ContextFree.isCFL_iff_isContextFree` — a language is context-free in the
  sense of `IsCFL` (a finitary grammar generates it) exactly when it is
  context-free in the sense of `Language.IsContextFree`.
-/

namespace UAM.ContextFree

variable {N T : Type}

/-! ## Translating symbols -/

/-- Our sentential symbols as Mathlib's. -/
def toSym : N ⊕ T → Symbol T N
  | Sum.inl A => Symbol.nonterminal A
  | Sum.inr a => Symbol.terminal a

/-- Mathlib's sentential symbols as ours. -/
def ofSym : Symbol T N → N ⊕ T
  | Symbol.nonterminal A => Sum.inl A
  | Symbol.terminal a => Sum.inr a

@[simp] theorem ofSym_toSym (x : N ⊕ T) : ofSym (toSym x) = x := by cases x <;> rfl

@[simp] theorem toSym_ofSym (x : Symbol T N) : toSym (ofSym x) = x := by cases x <;> rfl

@[simp] theorem map_ofSym_map_toSym (α : List (N ⊕ T)) : (α.map toSym).map ofSym = α := by
  simp [List.map_map, Function.comp_def]

@[simp] theorem map_toSym_map_ofSym (α : List (Symbol T N)) : (α.map ofSym).map toSym = α := by
  simp [List.map_map, Function.comp_def]

@[simp] theorem map_ofSym_terminals (w : List T) :
    ((w.map Symbol.terminal : List (Symbol T N)).map ofSym) = w.map Sum.inr := by
  simp [List.map_map, Function.comp_def, ofSym]

/-! ## Matching rule sets -/

/-- A `Prop`-valued rule relation and a finite set of Mathlib rules describe the
same productions. -/
def RuleCompat (g : Grammar N T) (rs : Finset (ContextFreeRule T N)) : Prop :=
  ∀ A β, g.rule A β ↔ ∃ r ∈ rs, r.input = A ∧ r.output = β.map toSym

/-- The Mathlib grammar assembled from a rule set and a start symbol. -/
def mlGrammar (rs : Finset (ContextFreeRule T N)) (s : N) : ContextFreeGrammar T :=
  ⟨N, s, rs⟩

@[simp] theorem mlGrammar_rules (rs : Finset (ContextFreeRule T N)) (s : N) :
    (mlGrammar rs s).rules = rs := rfl

@[simp] theorem mlGrammar_initial (rs : Finset (ContextFreeRule T N)) (s : N) :
    (mlGrammar rs s).initial = s := rfl

/-! ## The two derivation relations agree -/

/-- Our derivations are Mathlib derivations. -/
theorem derives_of_yields {g : Grammar N T} {rs : Finset (ContextFreeRule T N)} {s : N}
    (hc : RuleCompat g rs) {α : List (N ⊕ T)} {w : List T} (hy : Yields g α w) :
    (mlGrammar rs s).Derives (α.map toSym) (w.map Symbol.terminal) := by
  induction hy with
  | nil =>
    simp only [List.map_nil]
    exact Relation.ReflTransGen.refl
  | @term a α w _ ih =>
    have := ih.append_left [Symbol.terminal a (N := N)]
    simpa [toSym] using this
  | @nonterm A β α u w hr _ _ ihβ ihα =>
    obtain ⟨r, hmem, hin, hout⟩ := (hc A β).1 hr
    have hstep : (mlGrammar rs s).Produces
        (Symbol.nonterminal A :: α.map toSym) (β.map toSym ++ α.map toSym) := by
      refine ⟨r, hmem, ?_⟩
      have := ContextFreeRule.Rewrites.head (r := r) (α.map toSym)
      rw [hin, hout] at this
      exact this
    have h1 : (mlGrammar rs s).Derives (β.map toSym ++ α.map toSym)
        (u.map Symbol.terminal ++ α.map toSym) := ihβ.append_right _
    have h2 : (mlGrammar rs s).Derives (u.map Symbol.terminal ++ α.map toSym)
        (u.map Symbol.terminal ++ w.map Symbol.terminal) := ihα.append_left _
    have := hstep.trans_derives (h1.trans h2)
    simpa [toSym] using this

/-- One rewriting step may be undone in our derivation relation. -/
theorem yields_of_produces_of_yields {g : Grammar N T} {rs : Finset (ContextFreeRule T N)} {s : N}
    (hc : RuleCompat g rs) {α' β' : List (Symbol T N)} {w : List T}
    (hp : (mlGrammar rs s).Produces α' β') (hy : Yields g (β'.map ofSym) w) :
    Yields g (α'.map ofSym) w := by
  obtain ⟨r, hmem, hrw⟩ := hp
  obtain ⟨p, q, hα, hβ⟩ := ContextFreeRule.Rewrites.exists_parts hrw
  subst hα
  subst hβ
  have hmapβ : ((p ++ r.output ++ q).map ofSym)
      = p.map ofSym ++ (r.output.map ofSym ++ q.map ofSym) := by
    simp [List.append_assoc]
  rw [hmapβ] at hy
  obtain ⟨u₁, v, rfl, hu₁, hv⟩ := Yields.split hy
  obtain ⟨u₂, u₃, rfl, hu₂, hu₃⟩ := Yields.split hv
  have hrule : g.rule r.input (r.output.map ofSym) :=
    (hc r.input (r.output.map ofSym)).2 ⟨r, hmem, rfl, by simp [Function.comp_def]⟩
  have hA : Yields g [Sum.inl r.input] u₂ := by
    have := Yields.nonterm (g := g) (α := []) hrule hu₂ Yields.nil
    simpa using this
  have hmapα : ((p ++ [Symbol.nonterminal r.input] ++ q).map ofSym)
      = p.map ofSym ++ ([Sum.inl r.input] ++ q.map ofSym) := by
    simp [List.append_assoc, ofSym]
  rw [hmapα]
  exact Yields.append hu₁ (Yields.append hA hu₃)

/-- Mathlib derivations are our derivations. -/
theorem yields_of_derives {g : Grammar N T} {rs : Finset (ContextFreeRule T N)} {s : N}
    (hc : RuleCompat g rs) {α' : List (Symbol T N)} {w : List T}
    (hd : (mlGrammar rs s).Derives α' (w.map Symbol.terminal)) :
    Yields g (α'.map ofSym) w := by
  induction hd using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [map_ofSym_terminals]
    exact (yields_map_inr_iff g w w).2 rfl
  | head hstep _ ih => exact yields_of_produces_of_yields hc hstep ih

/-- Matching grammars generate the same language. -/
theorem language_eq_of_ruleCompat {g : Grammar N T} {rs : Finset (ContextFreeRule T N)}
    (hc : RuleCompat g rs) : (mlGrammar rs g.start).language = g.language := by
  ext w
  constructor
  · intro hw
    have hd : (mlGrammar rs g.start).Derives [Symbol.nonterminal g.start]
        (w.map Symbol.terminal) := hw
    have := yields_of_derives hc hd
    simpa [ofSym, Grammar.language] using this
  · intro hw
    have := derives_of_yields (s := g.start) hc (α := [Sum.inl g.start]) hw
    simpa [toSym] using this

/-! ## The two notions of context-freeness agree -/

/-- The Mathlib grammar of a finitary grammar. -/
noncomputable def toCFG (g : Grammar N T) (h : g.Finitary) : ContextFreeGrammar T :=
  mlGrammar
    ((h.image (fun p : N × List (N ⊕ T) => (⟨p.1, p.2.map toSym⟩ : ContextFreeRule T N))).toFinset)
    g.start

theorem ruleCompat_toCFG (g : Grammar N T) (h : g.Finitary) :
    RuleCompat g
      ((h.image (fun p : N × List (N ⊕ T) =>
        (⟨p.1, p.2.map toSym⟩ : ContextFreeRule T N))).toFinset) := by
  intro A β
  constructor
  · intro hr
    refine ⟨⟨A, β.map toSym⟩, ?_, rfl, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨(A, β), hr, rfl⟩
  · rintro ⟨r, hmem, hin, hout⟩
    rw [Set.Finite.mem_toFinset] at hmem
    obtain ⟨⟨A', β'⟩, hrule, rfl⟩ := hmem
    simp only at hin hout
    subst hin
    have hββ' : β' = β := by
      have h2 := congrArg (fun l => List.map ofSym l) hout
      simpa [List.map_map, Function.comp_def] using h2
    rwa [hββ'] at hrule

theorem language_toCFG (g : Grammar N T) (h : g.Finitary) : (toCFG g h).language = g.language :=
  language_eq_of_ruleCompat (ruleCompat_toCFG g h)

/-- The finitary grammar of a Mathlib grammar. -/
def ofCFG (g' : ContextFreeGrammar T) : Grammar g'.NT T where
  rule A β := ∃ r ∈ g'.rules, r.input = A ∧ r.output = β.map toSym
  start := g'.initial

theorem finitary_ofCFG (g' : ContextFreeGrammar T) : (ofCFG g').Finitary := by
  refine Set.Finite.subset
    (g'.rules.finite_toSet.image (fun r => (r.input, r.output.map ofSym))) ?_
  rintro ⟨A, β⟩ ⟨r, hmem, hin, hout⟩
  exact ⟨r, hmem, by simp [hin, hout, Function.comp_def]⟩

theorem ruleCompat_ofCFG (g' : ContextFreeGrammar T) : RuleCompat (ofCFG g') g'.rules :=
  fun _ _ => Iff.rfl

theorem language_ofCFG (g' : ContextFreeGrammar T) : (ofCFG g').language = g'.language := by
  have h := language_eq_of_ruleCompat (ruleCompat_ofCFG g')
  rw [← h]
  rfl

/-- **The two notions of context-freeness agree.** -/
theorem isCFL_iff_isContextFree (L : Language T) : IsCFL L ↔ Language.IsContextFree L := by
  constructor
  · rintro ⟨N, g, hfin, rfl⟩
    exact ⟨toCFG g hfin, language_toCFG g hfin⟩
  · rintro ⟨g', rfl⟩
    exact ⟨g'.NT, ofCFG g', finitary_ofCFG g', language_ofCFG g'⟩

end UAM.ContextFree
