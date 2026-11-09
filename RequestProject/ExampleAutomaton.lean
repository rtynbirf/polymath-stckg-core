import RequestProject.Atlas.UAM_Emptiness

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A worked example: the parity automaton

Two concrete automata over the alphabet `Bool` are analysed with the tools of
`UAM.Emptiness`:

* `Example.parityDFA` accepts the words containing an even number of `true`s
  (`Example.parityDFA_accepts`);
* `Example.deadDFA` accepts nothing (`Example.deadDFA_accepts_empty`), which the
  bounded emptiness criterion also decides;
* `Example.parity_ne_dead` — the two automata are inequivalent, exhibited by an
  explicit short witness.
-/

namespace Example

open UAM.Emptiness

/-- The parity automaton: one state per parity of the number of `true`s read. -/
def parityDFA : DFA Bool Bool where
  step q a := xor q a
  start := false
  accept := {false}

theorem parityDFA_evalFrom (q : Bool) (w : List Bool) :
    parityDFA.evalFrom q w = xor q (w.count true % 2 == 1) := by
  induction w generalizing q with
  | nil => cases q <;> simp [DFA.evalFrom]
  | cons a t ih =>
    have hstep : parityDFA.evalFrom q (a :: t) = parityDFA.evalFrom (xor q a) t := rfl
    rw [hstep, ih]
    have hmod : t.count true % 2 = 0 ∨ t.count true % 2 = 1 := by omega
    cases a
    · simp
    · have hc : (true :: t).count true = t.count true + 1 := by simp
      rcases hmod with h0 | h1
      · have h1' : (t.count true + 1) % 2 = 1 := by omega
        cases q <;> simp [hc, h0, h1']
      · have h0' : (t.count true + 1) % 2 = 0 := by omega
        cases q <;> simp [hc, h1, h0']

/-- The parity automaton accepts exactly the words with evenly many `true`s. -/
theorem parityDFA_accepts : parityDFA.accepts = {w : List Bool | w.count true % 2 = 0} := by
  ext w
  have h : parityDFA.eval w = ((w.count true % 2 == 1 : Bool)) := by
    simpa [DFA.eval, parityDFA] using parityDFA_evalFrom false w
  have hmem : w ∈ parityDFA.accepts ↔ parityDFA.eval w = false := by
    simp [DFA.mem_accepts, parityDFA]
  have hset : w ∈ {w : List Bool | w.count true % 2 = 0} ↔ w.count true % 2 = 0 := Iff.rfl
  rw [hmem, hset, h]
  have hmod : w.count true % 2 = 0 ∨ w.count true % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · simp [h0]
  · simp [h1]

/-- The empty word is accepted. -/
theorem nil_mem_parity : [] ∈ parityDFA.accepts := by
  rw [parityDFA_accepts]
  show List.count true ([] : List Bool) % 2 = 0
  simp

/-- A single `true` is rejected. -/
theorem singleton_notMem_parity : [true] ∉ parityDFA.accepts := by
  rw [parityDFA_accepts]
  show ¬ (List.count true [true] % 2 = 0)
  simp

/-- An automaton with no accepting state. -/
def deadDFA : DFA Bool Bool where
  step q a := xor q a
  start := false
  accept := ∅

theorem deadDFA_accepts_empty : ∀ w : List Bool, w ∉ deadDFA.accepts := by
  intro w hw
  rw [DFA.mem_accepts] at hw
  exact hw

/-- The bounded criterion agrees: no word of length below the number of states
is accepted, hence none at all. -/
theorem deadDFA_empty_by_bound : ∀ w : List Bool, w ∉ deadDFA.accepts :=
  (accepts_eq_empty_iff deadDFA).2 fun v _ hv => deadDFA_accepts_empty v hv

/-- The two automata are not equivalent: the empty word separates them. -/
theorem parity_ne_dead : parityDFA.accepts ≠ deadDFA.accepts := by
  intro h
  have : [] ∈ deadDFA.accepts := h ▸ nil_mem_parity
  exact deadDFA_accepts_empty [] this

/-- The symmetric difference of the two automata is non-empty, witnessed by the
empty word. -/
theorem nil_mem_symmDiff : [] ∈ (symmDiffDFA parityDFA deadDFA).accepts := by
  rw [mem_symmDiff_accepts]
  intro h
  exact deadDFA_accepts_empty [] (h.1 nil_mem_parity)

end Example
