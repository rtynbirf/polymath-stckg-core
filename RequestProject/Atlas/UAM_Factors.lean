import RequestProject.Atlas.UAM_NFA
import RequestProject.Atlas.UAM_InverseHomomorphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Prefixes, suffixes and factors of a regular language

Quotienting a regular language by a *single* word keeps it regular
(`UAM.InvHom.isRegular_leftQuotient`).  This module removes the restriction on
the left: quotienting by an arbitrary language `K`,

  `K \ L = {w | ∃ u ∈ K, u ++ w ∈ L}`,

is again regular.  Determinism is lost — the automaton must guess where the
prefix from `K` ended — so the construction runs the deterministic automaton of
`L` from the *set* of states reachable by reading a word of `K`.

As corollaries the sets of prefixes, suffixes and factors (contiguous
subwords) of a regular language are regular.
-/

namespace UAM.Factors

variable {α : Type} {σ : Type}

/-! ## Running a deterministic automaton from a set of start states -/

/-- The deterministic automaton `M` viewed as a nondeterministic automaton with
start states `S`. -/
def startSetNFA (M : DFA α σ) (S : Set σ) : NFA α σ where
  step q a := {M.step q a}
  start := S
  accept := M.accept

@[simp] theorem startSetNFA_stepSet (M : DFA α σ) (S S' : Set σ) (a : α) :
    (startSetNFA M S).stepSet S' a = (fun q => M.step q a) '' S' := by
  ext q
  simp [NFA.stepSet, startSetNFA, eq_comm]

theorem startSetNFA_evalFrom (M : DFA α σ) (S : Set σ) (S' : Set σ) (w : List α) :
    (startSetNFA M S).evalFrom S' w = (fun q => M.evalFrom q w) '' S' := by
  induction w generalizing S' with
  | nil => simp
  | cons a w ih =>
    rw [NFA.evalFrom_cons, startSetNFA_stepSet, ih]
    ext q
    simp [DFA.evalFrom_cons, Set.image_image]

theorem mem_startSetNFA_accepts (M : DFA α σ) (S : Set σ) (w : List α) :
    w ∈ (startSetNFA M S).accepts ↔ ∃ q ∈ S, M.evalFrom q w ∈ M.accept := by
  rw [NFA.mem_accepts]
  simp only [startSetNFA_evalFrom, Set.mem_image]
  constructor
  · rintro ⟨s, hs, q, hq, rfl⟩
    exact ⟨q, hq, hs⟩
  · rintro ⟨q, hq, hacc⟩
    exact ⟨M.evalFrom q w, hacc, q, hq, rfl⟩

/-! ## Left quotient by an arbitrary language -/

/-- The states of `M` reachable by reading a word of `K`. -/
def reachSet (M : DFA α σ) (K : Language α) : Set σ := {q | ∃ u ∈ K, M.evalFrom M.start u = q}

theorem leftQuotientNFA_accepts (M : DFA α σ) (K : Language α) :
    (startSetNFA M (reachSet M K)).accepts = {w | ∃ u ∈ K, u ++ w ∈ M.accepts} := by
  ext w
  rw [mem_startSetNFA_accepts]
  constructor
  · rintro ⟨q, ⟨u, hu, rfl⟩, hacc⟩
    refine ⟨u, hu, ?_⟩
    rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append]
    exact hacc
  · rintro ⟨u, hu, hacc⟩
    refine ⟨M.evalFrom M.start u, ⟨u, hu, rfl⟩, ?_⟩
    rw [DFA.mem_accepts, DFA.eval, DFA.evalFrom_of_append] at hacc
    exact hacc

/-- **The left quotient of a regular language by an arbitrary language is
regular.** -/
theorem isRegular_leftQuotient_lang {L : Language α} (hL : L.IsRegular) (K : Language α) :
    Language.IsRegular (T := α) {w | ∃ u ∈ K, u ++ w ∈ L} := by
  obtain ⟨σ, hσ, M, rfl⟩ := hL
  exact UAM.NFA.isRegular_of_isNFARegular
    ⟨σ, hσ, startSetNFA M (reachSet M K), leftQuotientNFA_accepts M K⟩

/-! ## Prefixes, suffixes and factors -/

/-- The prefixes of a language. -/
def prefixes (L : Language α) : Language α := {w | ∃ v, w ++ v ∈ L}

/-- The suffixes of a language. -/
def suffixes (L : Language α) : Language α := {w | ∃ u, u ++ w ∈ L}

/-- The factors — contiguous subwords — of a language. -/
def factors (L : Language α) : Language α := {w | ∃ u v, u ++ (w ++ v) ∈ L}

theorem mem_prefixes_iff {L : Language α} {w : List α} :
    w ∈ prefixes L ↔ ∃ v, w ++ v ∈ L := Iff.rfl

theorem mem_factors_iff {L : Language α} {w : List α} :
    w ∈ factors L ↔ ∃ u v, u ++ (w ++ v) ∈ L := Iff.rfl

/-- **The prefixes of a regular language form a regular language.** -/
theorem isRegular_prefixes {L : Language α} (hL : L.IsRegular) :
    (prefixes L).IsRegular := by
  have h := UAM.InvHom.isRegular_rightQuotient hL (Set.univ : Language α)
  have hset : {w : List α | ∃ v ∈ (Set.univ : Language α), w ++ v ∈ L} = prefixes L := by
    ext w
    constructor
    · rintro ⟨v, -, hv⟩
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, Set.mem_univ v, hv⟩
  rwa [hset] at h

/-- **The suffixes of a regular language form a regular language.** -/
theorem isRegular_suffixes {L : Language α} (hL : L.IsRegular) :
    (suffixes L).IsRegular := by
  have h := isRegular_leftQuotient_lang hL (Set.univ : Language α)
  have hset : {w : List α | ∃ u ∈ (Set.univ : Language α), u ++ w ∈ L} = suffixes L := by
    ext w
    constructor
    · rintro ⟨u, -, hu⟩
      exact ⟨u, hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, Set.mem_univ u, hu⟩
  rwa [hset] at h

/-- **The factors of a regular language form a regular language.** -/
theorem isRegular_factors {L : Language α} (hL : L.IsRegular) :
    (factors L).IsRegular := by
  have h := isRegular_prefixes (isRegular_suffixes hL)
  have hset : prefixes (suffixes L) = factors L := by
    ext w
    constructor
    · rintro ⟨v, u, h⟩
      exact ⟨u, v, by simpa [List.append_assoc] using h⟩
    · rintro ⟨u, v, h⟩
      exact ⟨v, u, by simpa [List.append_assoc] using h⟩
  rwa [hset] at h

end UAM.Factors
