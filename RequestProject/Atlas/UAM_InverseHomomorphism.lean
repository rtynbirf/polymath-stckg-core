import RequestProject.UAM_ContextFreeHomomorphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Inverse homomorphisms and quotients of regular languages

Three constructions on a deterministic automaton, each of which only changes one
field of the automaton and therefore preserves finiteness of the state space:

* reading a whole block `f a` of letters for each input letter `a` gives the
  *inverse homomorphic image* `{w | hom f w ∈ L}` (`invHomDFA`);
* accepting in the states from which some word of `K` reaches an accepting state
  gives the *right quotient* `{w | ∃ v ∈ K, w ++ v ∈ L}` (`rightQuotientDFA`) —
  note that `K` here is an arbitrary language, not necessarily regular;
* starting in the state reached after reading `u` gives the *left quotient*
  `L.leftQuotient u` (`leftQuotientDFA`).

The letter-to-word homomorphism `hom` is the one already used for the
context-free closure results, so images and preimages are taken along the same
notion of morphism.
-/

namespace UAM.InvHom

open UAM.ContextFree

variable {α β σ : Type}

/-! ## Inverse homomorphic image -/

/-- The automaton reading, for each input letter `a`, the whole block `f a`. -/
def invHomDFA (M : DFA β σ) (f : α → List β) : DFA α σ where
  step q a := M.evalFrom q (f a)
  start := M.start
  accept := M.accept

theorem evalFrom_invHomDFA (M : DFA β σ) (f : α → List β) (q : σ) (w : List α) :
    (invHomDFA M f).evalFrom q w = M.evalFrom q (hom f w) := by
  induction w generalizing q with
  | nil => simp
  | cons a w ih =>
      rw [DFA.evalFrom_cons, ih, hom_cons, DFA.evalFrom_of_append]
      rfl

theorem invHomDFA_accepts (M : DFA β σ) (f : α → List β) :
    (invHomDFA M f).accepts = {w | hom f w ∈ M.accepts} := by
  ext w
  simp only [DFA.mem_accepts, DFA.eval, evalFrom_invHomDFA]
  rfl

/-- **Regular languages are closed under inverse homomorphism.** -/
theorem isRegular_preimage_hom {L : Language β} (hL : L.IsRegular) (f : α → List β) :
    Language.IsRegular (T := α) {w | hom f w ∈ L} := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, ‹_›, invHomDFA M f, invHomDFA_accepts M f⟩

/-- A letter-to-letter homomorphism acts by `List.map`. -/
theorem hom_singleton (f : α → β) (w : List α) : hom (fun a => [f a]) w = w.map f := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

/-- Preimage under a renaming of the alphabet is a special case. -/
theorem isRegular_preimage_map {L : Language β} (hL : L.IsRegular) (f : α → β) :
    Language.IsRegular (T := α) {w | w.map f ∈ L} := by
  have hset : {w : List α | hom (fun a => [f a]) w ∈ L} = {w : List α | w.map f ∈ L} := by
    ext w; simp [hom_singleton]
  exact hset ▸ isRegular_preimage_hom hL (fun a => [f a])

/-! ## Right quotient -/

/-- The automaton accepting in every state from which some word of `K` leads to
an accepting state. -/
def rightQuotientDFA (M : DFA β σ) (K : Language β) : DFA β σ where
  step := M.step
  start := M.start
  accept := {q | ∃ v ∈ K, M.evalFrom q v ∈ M.accept}

theorem rightQuotientDFA_accepts (M : DFA β σ) (K : Language β) :
    (rightQuotientDFA M K).accepts = {w | ∃ v ∈ K, w ++ v ∈ M.accepts} := by
  ext w
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
  rfl

/-- **Regular languages are closed under right quotient by an arbitrary
language.** -/
theorem isRegular_rightQuotient {L : Language β} (hL : L.IsRegular) (K : Language β) :
    Language.IsRegular (T := β) {w | ∃ v ∈ K, w ++ v ∈ L} := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, ‹_›, rightQuotientDFA M K, rightQuotientDFA_accepts M K⟩

/-- Right quotient by a single word. -/
theorem isRegular_rightQuotient_word {L : Language β} (hL : L.IsRegular) (v : List β) :
    Language.IsRegular (T := β) {w | w ++ v ∈ L} := by
  have hset : {w : List β | ∃ v' ∈ ({v} : Language β), w ++ v' ∈ L} = {w : List β | w ++ v ∈ L} := by
    ext w
    exact ⟨fun ⟨v', hv', h⟩ => by rw [show v' = v from hv'] at h; exact h, fun h => ⟨v, rfl, h⟩⟩
  exact hset ▸ isRegular_rightQuotient hL {v}

/-! ## Left quotient -/

/-- The automaton started in the state reached after reading `u`. -/
def leftQuotientDFA (M : DFA β σ) (u : List β) : DFA β σ where
  step := M.step
  start := M.eval u
  accept := M.accept

theorem leftQuotientDFA_accepts (M : DFA β σ) (u : List β) :
    (leftQuotientDFA M u).accepts = M.accepts.leftQuotient u := by
  ext w
  simp only [DFA.mem_accepts, DFA.eval, Language.mem_leftQuotient, DFA.evalFrom_of_append]
  rfl

/-- **Regular languages are closed under left quotient by a word.** -/
theorem isRegular_leftQuotient {L : Language β} (hL : L.IsRegular) (u : List β) :
    (L.leftQuotient u).IsRegular := by
  obtain ⟨σ, _, M, rfl⟩ := hL
  exact ⟨σ, ‹_›, leftQuotientDFA M u, leftQuotientDFA_accepts M u⟩

/-- Both quotients at once: `{w | u ++ w ++ v ∈ L}` is regular. -/
theorem isRegular_twoSidedQuotient {L : Language β} (hL : L.IsRegular) (u v : List β) :
    Language.IsRegular (T := β) {w | u ++ (w ++ v) ∈ L} :=
  isRegular_rightQuotient_word (isRegular_leftQuotient hL u) v

end UAM.InvHom
