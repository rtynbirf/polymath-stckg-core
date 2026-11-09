import RequestProject.Atlas.UAM_KleeneConverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Closure properties of the regular languages

Building on the Kleene theorems of `RequestProject.Atlas.UAM_Kleene` and
`RequestProject.Atlas.UAM_KleeneConverse`, this module records the remaining
standard closure properties:

* `UAM.Closure.isRegular_leftQuotient` — derivatives of a regular language are
  regular;
* `UAM.Closure.isRegular_reverse` — the reversal of a regular language is regular
  (no finiteness assumption on the alphabet is needed);
* `UAM.Closure.isRegular_comap` — preimages under a letter-renaming are regular;
* `UAM.Closure.isRegular_map` — images under a letter-renaming are regular, over a
  finite alphabet.
-/

namespace UAM.Closure

open scoped Computability

universe u v w

/-! ## Derivatives -/

/-- Every left quotient (Brzozowski derivative) of a regular language is regular. -/
theorem isRegular_leftQuotient {α : Type u} {L : Language α} (h : L.IsRegular) (x : List α) :
    (L.leftQuotient x).IsRegular := by
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  refine Set.Finite.subset h.finite_range_leftQuotient ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨x ++ y, Language.leftQuotient_append L x y⟩

/-! ## Reversal -/

/-- The reversal of a regular language is regular.  The proof exhibits every left
quotient of `L.reverse` as determined by the finite set of automaton states from
which the reversed word is accepted, so no assumption on the alphabet is used. -/
theorem isRegular_reverse {α : Type u} {L : Language α} (h : L.IsRegular) :
    L.reverse.IsRegular := by
  classical
  obtain ⟨σ, hσ, M, rfl⟩ := h
  refine Language.IsRegular.of_finite_range_leftQuotient ?_
  -- the "backwards state set" attached to a word
  set g : List α → Set σ := fun u => {q | M.evalFrom q u.reverse ∈ M.accept} with hg
  set F : Set σ → Language α := fun T => {y | M.evalFrom M.start y.reverse ∈ T} with hF
  have key : ∀ u : List α, (M.accepts.reverse).leftQuotient u = F (g u) := by
    intro u
    apply Set.ext
    intro y
    rw [Language.mem_leftQuotient]
    constructor
    · intro hy
      have hy' : (u ++ y).reverse ∈ M.accepts := hy
      rw [List.reverse_append] at hy'
      have := M.mem_accepts.1 hy'
      simpa [hF, hg, DFA.eval, DFA.evalFrom_of_append] using this
    · intro hy
      have hy' : M.evalFrom (M.evalFrom M.start y.reverse) u.reverse ∈ M.accept := hy
      have : (u ++ y).reverse ∈ M.accepts := by
        rw [List.reverse_append]
        exact M.mem_accepts.2 (by rw [DFA.eval, DFA.evalFrom_of_append]; exact hy')
      exact this
  have hfin : (Set.range F).Finite := Set.finite_range F
  refine Set.Finite.subset hfin ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨g u, (key u).symm⟩

/-! ## Renaming the alphabet -/

/-- Relabelling the transitions of an automaton along `f : β → α`. -/
def comapDFA {α : Type u} {β : Type v} {σ : Type w} (f : β → α) (M : DFA α σ) : DFA β σ where
  step q b := M.step q (f b)
  start := M.start
  accept := M.accept

theorem comapDFA_evalFrom {α : Type u} {β : Type v} {σ : Type w} (f : β → α) (M : DFA α σ)
    (q : σ) (w : List β) : (comapDFA f M).evalFrom q w = M.evalFrom q (w.map f) := by
  induction w generalizing q with
  | nil => rfl
  | cons b t ih =>
    simp only [List.map_cons]
    rw [DFA.evalFrom, DFA.evalFrom, List.foldl_cons, List.foldl_cons]
    exact ih (M.step q (f b))

/-- Preimages of regular languages under a letter-renaming are regular. -/
theorem isRegular_comap {α : Type u} {β : Type u} (f : β → α) {L : Language α}
    (h : L.IsRegular) : Language.IsRegular (T := β) {w | w.map f ∈ L} := by
  obtain ⟨σ, hσ, M, rfl⟩ := h
  refine ⟨σ, hσ, comapDFA f M, ?_⟩
  apply Set.ext
  intro w
  rw [DFA.mem_accepts]
  show (comapDFA f M).evalFrom (comapDFA f M).start w ∈ M.accept ↔ _
  rw [comapDFA_evalFrom]
  exact (M.mem_accepts (x := w.map f))

/-- Images of regular-expression languages under a letter-renaming are again
regular-expression languages. -/
theorem isRegexLang_map {α β : Type} (f : α → β) {L : Language α}
    (h : UAM.Kleene.IsRegexLang L) : UAM.Kleene.IsRegexLang (Language.map f L) := by
  obtain ⟨P, rfl⟩ := h
  induction P with
  | zero =>
    refine UAM.Kleene.IsRegexLang.congr ?_ UAM.Kleene.isRegexLang_zero
    exact (map_zero (Language.map f)).symm
  | epsilon =>
    refine UAM.Kleene.IsRegexLang.congr ?_ UAM.Kleene.isRegexLang_one
    exact (map_one (Language.map f)).symm
  | char a =>
    refine UAM.Kleene.IsRegexLang.congr ?_ (UAM.Kleene.isRegexLang_char (f a))
    apply Set.ext
    intro y
    constructor
    · intro hy
      have hy' : y = [f a] := hy
      exact ⟨[a], rfl, by rw [hy']; rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx' : x = [a] := hx
      rw [hx']
      rfl
  | plus P Q ihP ihQ =>
    refine UAM.Kleene.IsRegexLang.congr ?_ (ihP.add ihQ)
    exact (map_add (Language.map f) _ _).symm
  | comp P Q ihP ihQ =>
    refine UAM.Kleene.IsRegexLang.congr ?_ (ihP.mul ihQ)
    exact (map_mul (Language.map f) _ _).symm
  | star P ihP =>
    refine UAM.Kleene.IsRegexLang.congr ?_ ihP.kstar
    exact (Language.map_kstar f _).symm

/-- Images of regular languages under a letter-renaming are regular, over a
finite alphabet. -/
theorem isRegular_map {α β : Type} [Fintype α] [Fintype β] (f : α → β) {L : Language α}
    (h : L.IsRegular) : (Language.map f L).IsRegular := by
  obtain ⟨P, hP⟩ := isRegexLang_map f (UAM.Kleene.isRegexLang_of_isRegular h)
  rw [← hP]
  exact UAM.Kleene.isRegular_matches' P

end UAM.Closure
