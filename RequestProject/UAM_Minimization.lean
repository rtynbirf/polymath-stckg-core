import RequestProject.UAM_MyhillNerode

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Minimal automata are unique up to isomorphism

An automaton is *minimal* when every state is reachable from the start state and
distinct states are separated by some continuation.  The main theorem of this
module,

`minimal_unique`,

says that two minimal automata accepting the same language are isomorphic: there
is a bijection of state sets carrying start to start, commuting with the
transition maps, and matching the accepting sets.

The proof is the standard one.  From a reachable automaton to a distinguishable
one accepting the same language there is a canonical homomorphism
(`homOfReachable`); between two minimal automata one gets homomorphisms both
ways, and any endomorphism of a distinguishable automaton is the identity
(`hom_self_eq_id`), so the two homomorphisms are mutually inverse.
-/

namespace UAM.Minimization

universe u v w z

variable {α : Type u} {σ : Type v} {τ : Type w}

/-! ## Reachability, distinguishability, minimality -/

/-- Every state of the automaton is reached by some word. -/
def Reachable (M : DFA α σ) : Prop := ∀ q : σ, ∃ x : List α, M.eval x = q

/-- Distinct states of the automaton are separated by some continuation. -/
def Distinguishable (M : DFA α σ) : Prop :=
  ∀ p q : σ, (∀ x : List α, M.evalFrom p x ∈ M.accept ↔ M.evalFrom q x ∈ M.accept) → p = q

/-- A minimal automaton: reachable and distinguishable. -/
structure Minimal (M : DFA α σ) : Prop where
  /-- Every state is reachable. -/
  reachable : Reachable M
  /-- Distinct states are separated. -/
  distinguishable : Distinguishable M

/-! ## Homomorphisms of automata -/

/-- A homomorphism of automata: a map of states preserving start, transitions and
acceptance. -/
structure Hom (M : DFA α σ) (N : DFA α τ) where
  /-- The underlying map of states. -/
  toFun : σ → τ
  /-- The start state is preserved. -/
  map_start : toFun M.start = N.start
  /-- Transitions are preserved. -/
  map_step : ∀ (q : σ) (a : α), toFun (M.step q a) = N.step (toFun q) a
  /-- Acceptance is preserved and reflected. -/
  map_accept : ∀ q : σ, q ∈ M.accept ↔ toFun q ∈ N.accept

namespace Hom

theorem map_evalFrom {M : DFA α σ} {N : DFA α τ} (h : Hom M N) (q : σ) (x : List α) :
    h.toFun (M.evalFrom q x) = N.evalFrom (h.toFun q) x := by
  induction x generalizing q with
  | nil => rfl
  | cons a t ih => rw [DFA.evalFrom_cons, ih, h.map_step, DFA.evalFrom_cons]

theorem map_eval {M : DFA α σ} {N : DFA α τ} (h : Hom M N) (x : List α) :
    h.toFun (M.eval x) = N.eval x := by
  show h.toFun (M.evalFrom M.start x) = N.evalFrom N.start x
  rw [h.map_evalFrom, h.map_start]

/-- Homomorphic automata accept the same language. -/
theorem accepts_eq {M : DFA α σ} {N : DFA α τ} (h : Hom M N) : M.accepts = N.accepts := by
  ext x
  rw [DFA.mem_accepts, DFA.mem_accepts, ← h.map_eval x]
  exact h.map_accept (M.eval x)

/-- Composition of homomorphisms. -/
def comp {σ₁ : Type v} {σ₂ : Type w} {σ₃ : Type z} {M₁ : DFA α σ₁} {M₂ : DFA α σ₂}
    {M₃ : DFA α σ₃} (g : Hom M₂ M₃) (h : Hom M₁ M₂) : Hom M₁ M₃ where
  toFun q := g.toFun (h.toFun q)
  map_start := by rw [h.map_start, g.map_start]
  map_step := fun q a => by rw [h.map_step, g.map_step]
  map_accept := fun q => (h.map_accept q).trans (g.map_accept (h.toFun q))

/-- The identity homomorphism. -/
def id' (M : DFA α σ) : Hom M M where
  toFun := _root_.id
  map_start := rfl
  map_step := fun _ _ => rfl
  map_accept := fun _ => Iff.rfl

end Hom

/-! ## The canonical homomorphism -/

variable {M : DFA α σ} {N : DFA α τ}

/-- Words reaching the same state of `M` reach the same state of a
distinguishable automaton accepting the same language. -/
theorem eval_eq_of_eval_eq (hL : M.accepts = N.accepts) (hN : Distinguishable N)
    {x y : List α} (h : M.eval x = M.eval y) : N.eval x = N.eval y := by
  refine hN _ _ (fun v => ?_)
  have key : ∀ z : List α,
      (N.evalFrom (N.eval z) v ∈ N.accept) ↔ (M.evalFrom (M.eval z) v ∈ M.accept) := by
    intro z
    have h1 : N.evalFrom (N.eval z) v = N.eval (z ++ v) :=
      (DFA.evalFrom_of_append N N.start z v).symm
    have h2 : M.evalFrom (M.eval z) v = M.eval (z ++ v) :=
      (DFA.evalFrom_of_append M M.start z v).symm
    rw [h1, h2, ← DFA.mem_accepts, ← DFA.mem_accepts, hL]
  rw [key x, key y, h]

/-- The canonical homomorphism from a reachable automaton to a distinguishable
automaton accepting the same language. -/
noncomputable def homOfReachable (hM : Reachable M) (hN : Distinguishable N)
    (hL : M.accepts = N.accepts) : Hom M N where
  toFun q := N.eval (hM q).choose
  map_start := by
    have h : M.eval (hM M.start).choose = M.eval [] := by
      rw [(hM M.start).choose_spec, DFA.eval_nil]
    simpa using eval_eq_of_eval_eq hL hN h
  map_step q a := by
    have hq := (hM q).choose_spec
    have hqa := (hM (M.step q a)).choose_spec
    have h : M.eval (hM (M.step q a)).choose = M.eval ((hM q).choose ++ [a]) := by
      rw [hqa, DFA.eval_append_singleton, hq]
    rw [eval_eq_of_eval_eq hL hN h, DFA.eval_append_singleton]
  map_accept q := by
    have hq := (hM q).choose_spec
    have hmem : (q ∈ M.accept) ↔ ((hM q).choose ∈ M.accepts) := by
      rw [DFA.mem_accepts, hq]
    rw [hmem, hL, DFA.mem_accepts]

/-! ## Uniqueness -/

/-- An endomorphism of a distinguishable automaton is the identity. -/
theorem hom_self_eq_id (hM : Distinguishable M) (h : Hom M M) (q : σ) : h.toFun q = q := by
  refine (hM q (h.toFun q) (fun x => ?_)).symm
  rw [← h.map_evalFrom q x]
  exact h.map_accept (M.evalFrom q x)

/-- **Minimal automata accepting the same language are isomorphic.** -/
theorem minimal_unique (hM : Minimal M) (hN : Minimal N) (hL : M.accepts = N.accepts) :
    ∃ e : σ ≃ τ, e M.start = N.start ∧ (∀ (q : σ) (a : α), e (M.step q a) = N.step (e q) a) ∧
      (∀ q : σ, q ∈ M.accept ↔ e q ∈ N.accept) := by
  classical
  let f : Hom M N := homOfReachable hM.reachable hN.distinguishable hL
  let g : Hom N M := homOfReachable hN.reachable hM.distinguishable hL.symm
  have hgf : ∀ q : σ, g.toFun (f.toFun q) = q := fun q =>
    hom_self_eq_id hM.distinguishable (Hom.comp g f) q
  have hfg : ∀ q : τ, f.toFun (g.toFun q) = q := fun q =>
    hom_self_eq_id hN.distinguishable (Hom.comp f g) q
  exact ⟨⟨f.toFun, g.toFun, hgf, hfg⟩, f.map_start, f.map_step, f.map_accept⟩

/-! ## The Nerode automaton is minimal -/

open UAM.MyhillNerode

theorem evalFrom_nerodeDFA_val {L : Language α} (s : Set.range L.leftQuotient) (x : List α) :
    (L.toDFA.evalFrom s x).val = s.val.leftQuotient x := by
  induction x generalizing s with
  | nil => simp
  | cons a t ih =>
    rw [DFA.evalFrom_cons, ih, Language.step_toDFA, ← Language.leftQuotient_append]
    rfl

theorem eval_nerodeDFA_val (L : Language α) (x : List α) :
    (L.toDFA.eval x).val = L.leftQuotient x := by
  show (L.toDFA.evalFrom L.toDFA.start x).val = L.leftQuotient x
  rw [evalFrom_nerodeDFA_val, Language.start_toDFA]

/-- **The Nerode automaton of a language is minimal.** -/
theorem nerodeDFA_minimal (L : Language α) : Minimal (nerodeDFA L) := by
  constructor
  · rintro ⟨s, y, rfl⟩
    exact ⟨y, Subtype.ext (eval_nerodeDFA_val L y)⟩
  · intro p q h
    refine Subtype.ext (Set.ext fun x => ?_)
    have key : ∀ r : Set.range L.leftQuotient,
        (L.toDFA.evalFrom r x ∈ L.toDFA.accept ↔ x ∈ r.val) := by
      intro r
      rw [Language.mem_accept_toDFA, evalFrom_nerodeDFA_val, Language.mem_leftQuotient,
        List.append_nil]
    exact (key p).symm.trans ((h x).trans (key q))

/-- Every minimal automaton for a language is isomorphic to its Nerode
automaton. -/
theorem minimal_iso_nerode (hM : Minimal M) :
    ∃ e : σ ≃ Set.range (M.accepts).leftQuotient,
      e M.start = (nerodeDFA M.accepts).start ∧
      (∀ (q : σ) (a : α), e (M.step q a) = (nerodeDFA M.accepts).step (e q) a) ∧
      (∀ q : σ, q ∈ M.accept ↔ e q ∈ (nerodeDFA M.accepts).accept) :=
  minimal_unique hM (nerodeDFA_minimal M.accepts) (nerodeDFA_accepts M.accepts).symm

end UAM.Minimization
