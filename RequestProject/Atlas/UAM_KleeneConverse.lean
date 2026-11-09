import RequestProject.Atlas.UAM_Kleene

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Kleene's theorem: every regular language is denoted by a regular expression

`RequestProject.Atlas.UAM_Kleene` proves the easy direction of Kleene's theorem
(the language of a regular expression is regular).  This module proves the
converse — the Kleene/McNaughton–Yamada state-elimination construction — for a
deterministic automaton over a finite alphabet:

* `UAM.Kleene.pathLang M S i j` is the set of words that drive `M` from state `i`
  to state `j` while every *intermediate* state stays inside the finite set `S`;
* `UAM.Kleene.pathLang_insert` is the state-elimination recursion
  `R(S ∪ {k}) = R(S) + R(S)·R(S)*·R(S)`;
* `UAM.Kleene.isRegexLang_pathLang` derives, by induction on `S`, a regular
  expression for every path language;
* `UAM.Kleene.isRegexLang_of_isRegular` and `UAM.Kleene.isRegular_iff_isRegexLang`
  assemble these into Kleene's theorem:
  a language over a finite alphabet is regular iff it is denoted by a regular
  expression.
-/

namespace UAM.Kleene

open scoped Computability

/-! ## Languages denoted by a regular expression -/

variable {α : Type}

/-- `L` is denoted by some regular expression. -/
def IsRegexLang (L : Language α) : Prop := ∃ P : RegularExpression α, P.matches' = L

theorem isRegexLang_zero : IsRegexLang (0 : Language α) := ⟨RegularExpression.zero, rfl⟩

theorem isRegexLang_one : IsRegexLang (1 : Language α) := ⟨RegularExpression.epsilon, rfl⟩

theorem isRegexLang_char (a : α) : IsRegexLang ({[a]} : Language α) :=
  ⟨RegularExpression.char a, rfl⟩

theorem IsRegexLang.congr {L M : Language α} (h : L = M) (hL : IsRegexLang L) : IsRegexLang M :=
  h ▸ hL

theorem IsRegexLang.add {L M : Language α} (hL : IsRegexLang L) (hM : IsRegexLang M) :
    IsRegexLang (L + M) := by
  obtain ⟨P, rfl⟩ := hL
  obtain ⟨Q, rfl⟩ := hM
  exact ⟨P.plus Q, rfl⟩

theorem IsRegexLang.mul {L M : Language α} (hL : IsRegexLang L) (hM : IsRegexLang M) :
    IsRegexLang (L * M) := by
  obtain ⟨P, rfl⟩ := hL
  obtain ⟨Q, rfl⟩ := hM
  exact ⟨P.comp Q, rfl⟩

theorem IsRegexLang.kstar {L : Language α} (hL : IsRegexLang L) : IsRegexLang (L∗) := by
  obtain ⟨P, rfl⟩ := hL
  exact ⟨P.star, rfl⟩

theorem isRegexLang_singletonWord (w : List α) : IsRegexLang ({w} : Language α) := by
  induction w with
  | nil => exact isRegexLang_one
  | cons a t ih =>
    refine IsRegexLang.congr ?_ ((isRegexLang_char a).mul ih)
    apply Set.ext
    intro y
    constructor
    · rintro ⟨b, hb, c, hc, rfl⟩
      have hb' : b = [a] := hb
      have hc' : c = t := hc
      subst hb'
      subst hc'
      rfl
    · intro hy
      have hy' : y = a :: t := hy
      exact ⟨[a], rfl, t, rfl, hy'.symm⟩

theorem isRegexLang_finsetLang [DecidableEq (List α)] (F : Finset (List α)) :
    IsRegexLang {y | y ∈ F} := by
  induction F using Finset.induction with
  | empty =>
    refine IsRegexLang.congr ?_ isRegexLang_zero
    apply Set.ext
    intro y
    simp [Language.zero_def]
  | insert w F _ ih =>
    refine IsRegexLang.congr ?_ ((isRegexLang_singletonWord w).add ih)
    apply Set.ext
    intro y
    simp [Finset.mem_insert]
    rfl

/-- Every finite language is denoted by a regular expression. -/
theorem isRegexLang_of_finite {L : Language α} (h : (L : Set (List α)).Finite) :
    IsRegexLang L := by
  classical
  refine IsRegexLang.congr ?_ (isRegexLang_finsetLang h.toFinset)
  apply Set.ext
  intro y
  simp

/-- Finite unions of regular-expression languages are regular-expression languages. -/
theorem isRegexLang_finsetSup {ι : Type} [DecidableEq ι] (F : Finset ι) (f : ι → Language α)
    (h : ∀ i ∈ F, IsRegexLang (f i)) : IsRegexLang {y | ∃ i ∈ F, y ∈ f i} := by
  induction F using Finset.induction with
  | empty =>
    refine IsRegexLang.congr ?_ isRegexLang_zero
    apply Set.ext
    intro y
    simp [Language.zero_def]
  | @insert a F _ ih =>
    have hA : IsRegexLang (f a) := h a (Finset.mem_insert_self a F)
    have hrest : IsRegexLang {y | ∃ i ∈ F, y ∈ f i} :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine IsRegexLang.congr ?_ (hA.add hrest)
    apply Set.ext
    intro y
    constructor
    · rintro (hy | ⟨i, hi, hy⟩)
      · exact ⟨a, Finset.mem_insert_self a F, hy⟩
      · exact ⟨i, Finset.mem_insert_of_mem hi, hy⟩
    · rintro ⟨i, hi, hy⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Or.inl hy
      · exact Or.inr ⟨i, hi, hy⟩

/-! ## Path languages of a deterministic automaton -/

variable {σ : Type} [DecidableEq σ]

/-- The words driving `M` from `i` to `j` all of whose *intermediate* states lie
in the finite set `S`. -/
def pathLang (M : DFA α σ) (S : Finset σ) (i j : σ) : Language α :=
  {w | M.evalFrom i w = j ∧ ∀ n, 0 < n → n < w.length → M.evalFrom i (w.take n) ∈ S}

omit [DecidableEq σ] in
/-- Reformulation of the intermediate-state condition in terms of splittings. -/
theorem mem_pathLang_iff (M : DFA α σ) (S : Finset σ) (i j : σ) (w : List α) :
    w ∈ pathLang M S i j ↔
      M.evalFrom i w = j ∧ ∀ u v : List α, u ++ v = w → u ≠ [] → v ≠ [] → M.evalFrom i u ∈ S := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro u v rfl hu hv
    have hlen : (u ++ v).take u.length = u := by simp
    have h := h2 u.length (List.length_pos_iff.2 hu) (by
      simp only [List.length_append]
      have : 0 < v.length := List.length_pos_iff.2 hv
      omega)
    rwa [hlen] at h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro n hn hnw
    refine h2 (w.take n) (w.drop n) (List.take_append_drop n w) ?_ ?_
    · intro h
      have h0 : (w.take n).length = 0 := by rw [h]; rfl
      rw [List.length_take] at h0
      omega
    · intro h
      have h0 : (w.drop n).length = 0 := by rw [h]; rfl
      rw [List.length_drop] at h0
      omega

omit [DecidableEq σ] in
theorem nil_mem_pathLang (M : DFA α σ) (S : Finset σ) (i : σ) : [] ∈ pathLang M S i i :=
  ⟨rfl, by intro n _ h; simp at h⟩

omit [DecidableEq σ] in
theorem pathLang_mono (M : DFA α σ) {S T : Finset σ} (h : S ⊆ T) (i j : σ) {w : List α}
    (hw : w ∈ pathLang M S i j) : w ∈ pathLang M T i j :=
  ⟨hw.1, fun n hn hnw => h (hw.2 n hn hnw)⟩

/-- Concatenating a path `i → k` with a path `k → j` gives a path `i → j` whose
intermediate states additionally may visit `k`. -/
theorem pathLang_append (M : DFA α σ) (S : Finset σ) (k i j : σ) {w₁ w₂ : List α}
    (h₁ : w₁ ∈ pathLang M S i k) (h₂ : w₂ ∈ pathLang M S k j) :
    w₁ ++ w₂ ∈ pathLang M (insert k S) i j := by
  rw [mem_pathLang_iff] at h₁ h₂ ⊢
  obtain ⟨e₁, p₁⟩ := h₁
  obtain ⟨e₂, p₂⟩ := h₂
  refine ⟨by rw [DFA.evalFrom_of_append, e₁, e₂], ?_⟩
  rintro u v huv hu hv
  rcases List.append_eq_append_iff.1 huv.symm with ⟨c, hu', hv'⟩ | ⟨c, hw', hv'⟩
  · have hev : M.evalFrom i u = M.evalFrom k c := by rw [hu', DFA.evalFrom_of_append, e₁]
    rcases eq_or_ne c [] with rfl | hc
    · rw [hev]
      exact Finset.mem_insert_self k S
    · rw [hev]
      exact Finset.mem_insert_of_mem (p₂ c v hv'.symm hc hv)
  · rcases eq_or_ne c [] with rfl | hc
    · have hu2 : u = w₁ := by simpa using hw'.symm
      rw [hu2, e₁]
      exact Finset.mem_insert_self k S
    · exact Finset.mem_insert_of_mem (p₁ u c hw'.symm hu hc)

theorem pathLang_append_insert (M : DFA α σ) (S : Finset σ) (k i j : σ) {w₁ w₂ : List α}
    (h₁ : w₁ ∈ pathLang M (insert k S) i k) (h₂ : w₂ ∈ pathLang M (insert k S) k j) :
    w₁ ++ w₂ ∈ pathLang M (insert k S) i j := by
  have h := pathLang_append M (insert k S) k i j h₁ h₂
  rwa [Finset.insert_idem] at h

/-- Iterating loops at `k` with intermediate states in `S` gives a loop at `k`
with intermediate states in `S ∪ {k}`. -/
theorem kstar_pathLang_subset (M : DFA α σ) (S : Finset σ) (k : σ) {w : List α}
    (hw : w ∈ (pathLang M S k k)∗) : w ∈ pathLang M (insert k S) k k := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hw
  induction L with
  | nil => exact nil_mem_pathLang M _ k
  | cons f T ih =>
    have hf : f ∈ pathLang M S k k := hL f (List.mem_cons_self ..)
    have hT : ∀ z ∈ T, z ∈ pathLang M S k k := fun z hz => hL z (List.mem_cons_of_mem _ hz)
    have hrest : T.flatten ∈ pathLang M (insert k S) k k :=
      ih hT (Language.mem_kstar.2 ⟨T, rfl, hT⟩)
    have h := pathLang_append_insert M S k k k
      (pathLang_mono M (Finset.subset_insert k S) k k hf) hrest
    simpa using h

/-- First-visit decomposition: a path with intermediate states in `S ∪ {k}` either
avoids `k` entirely, or splits at its first visit to `k`. -/
theorem pathLang_first_visit (M : DFA α σ) (S : Finset σ) (k i j : σ) {w : List α}
    (hw : w ∈ pathLang M (insert k S) i j) :
    w ∈ pathLang M S i j ∨
      ∃ u v : List α, w = u ++ v ∧ u ≠ [] ∧ u ∈ pathLang M S i k ∧
        v ∈ pathLang M (insert k S) k j := by
  classical
  obtain ⟨he, hp⟩ := hw
  by_cases hex : ∃ n, 0 < n ∧ n < w.length ∧ M.evalFrom i (w.take n) = k
  · right
    set m := Nat.find hex with hm
    obtain ⟨hm0, hmlen, hmk⟩ := Nat.find_spec hex
    have hk : M.evalFrom i (w.take m) = k := hmk
    refine ⟨w.take m, w.drop m, (List.take_append_drop m w).symm, ?_, ⟨hmk, ?_⟩, ⟨?_, ?_⟩⟩
    · intro h
      have h0 : (w.take m).length = 0 := by rw [h]; rfl
      rw [List.length_take] at h0
      omega
    · intro n hn hnm
      rw [List.length_take] at hnm
      have hnm' : n < m := by omega
      have h1 : (w.take m).take n = w.take n := by
        rw [List.take_take]
        congr 1
        omega
      rw [h1]
      rcases Finset.mem_insert.1 (hp n hn (by omega)) with h | h
      · exact absurd ⟨hn, by omega, h⟩ (Nat.find_min hex hnm')
      · exact h
    · have h2 := DFA.evalFrom_of_append M i (w.take m) (w.drop m)
      rw [List.take_append_drop, hk] at h2
      rw [← h2, he]
    · intro n hn hnlen
      rw [List.length_drop] at hnlen
      have hsplit : w.take (m + n) = w.take m ++ (w.drop m).take n := List.take_add
      have h3 : M.evalFrom i (w.take (m + n)) = M.evalFrom k ((w.drop m).take n) := by
        rw [hsplit, DFA.evalFrom_of_append, hk]
      rw [← h3]
      exact hp (m + n) (by omega) (by omega)
  · left
    refine ⟨he, ?_⟩
    intro n hn hnlen
    rcases Finset.mem_insert.1 (hp n hn hnlen) with h | h
    · exact absurd ⟨n, hn, hnlen, h⟩ hex
    · exact h

/-- A path starting at `k` with intermediate states in `S ∪ {k}` is a sequence of
`S`-internal loops at `k` followed by an `S`-internal path to `j`. -/
theorem pathLang_loop_decomp (M : DFA α σ) (S : Finset σ) (k j : σ) :
    ∀ (N : ℕ) (w : List α), w.length ≤ N → w ∈ pathLang M (insert k S) k j →
      w ∈ (pathLang M S k k)∗ * pathLang M S k j := by
  intro N
  induction N with
  | zero =>
    intro w hlen hw
    have hw0 : w = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    subst hw0
    refine ⟨[], Language.nil_mem_kstar _, [], ?_, rfl⟩
    rcases pathLang_first_visit M S k k j hw with h | ⟨u, v, huv, hu, -, -⟩
    · exact h
    · exact absurd (List.eq_nil_of_append_eq_nil huv.symm).1 hu
  | succ N ih =>
    intro w hlen hw
    rcases pathLang_first_visit M S k k j hw with h | ⟨u, v, huv, hu, hu2, hv⟩
    · exact ⟨[], Language.nil_mem_kstar _, w, h, rfl⟩
    · have hulen : 0 < u.length := List.length_pos_iff.2 hu
      have hvlen : v.length ≤ N := by
        have : w.length = u.length + v.length := by rw [huv, List.length_append]
        omega
      obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := ih v hvlen hv
      refine ⟨u ++ z₁, cons_mem_kstar hu2 hz₁, z₂, hz₂, ?_⟩
      show u ++ z₁ ++ z₂ = w
      have hz' : z₁ ++ z₂ = v := hz
      rw [List.append_assoc, hz', huv]

/-- **State elimination.**  Allowing one more intermediate state `k` adds exactly
the paths that pass through `k`. -/
theorem pathLang_insert (M : DFA α σ) (S : Finset σ) (k i j : σ) :
    pathLang M (insert k S) i j =
      pathLang M S i j +
        pathLang M S i k * ((pathLang M S k k)∗ * pathLang M S k j) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    rcases pathLang_first_visit M S k i j hw with h | ⟨u, v, huv, -, hu, hv⟩
    · exact Or.inl h
    · obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ :=
        pathLang_loop_decomp M S k j v.length v le_rfl hv
      exact Or.inr ⟨u, hu, v, ⟨z₁, hz₁, z₂, hz₂, hz⟩, huv.symm⟩
  · rintro (h | ⟨u, hu, v, ⟨z₁, hz₁, z₂, hz₂, rfl⟩, rfl⟩)
    · exact pathLang_mono M (Finset.subset_insert k S) i j h
    · have h₁ : u ∈ pathLang M (insert k S) i k :=
        pathLang_mono M (Finset.subset_insert k S) i k hu
      have h₂ : z₁ ∈ pathLang M (insert k S) k k := kstar_pathLang_subset M S k hz₁
      have h₃ : z₂ ∈ pathLang M (insert k S) k j :=
        pathLang_mono M (Finset.subset_insert k S) k j hz₂
      exact pathLang_append_insert M S k i j h₁ (pathLang_append_insert M S k k j h₂ h₃)

/-! ## Every path language is denoted by a regular expression -/

variable [Fintype α]

omit [DecidableEq σ] in
/-- With no intermediate states allowed, only words of length at most one remain. -/
theorem pathLang_empty_finite (M : DFA α σ) (i j : σ) :
    (pathLang M (∅ : Finset σ) i j : Set (List α)).Finite := by
  refine Set.Finite.subset (List.finite_length_le α 1) ?_
  rintro w ⟨-, hw⟩
  by_contra hlen
  simp only [Set.mem_setOf_eq, not_le] at hlen
  exact absurd (hw 1 (by omega) (by omega)) (Finset.notMem_empty _)

theorem isRegexLang_pathLang (M : DFA α σ) (S : Finset σ) (i j : σ) :
    IsRegexLang (pathLang M S i j) := by
  classical
  induction S using Finset.induction generalizing i j with
  | empty => exact isRegexLang_of_finite (pathLang_empty_finite M i j)
  | @insert k S _ ih =>
    refine IsRegexLang.congr (pathLang_insert M S k i j).symm ?_
    exact (ih i j).add ((ih i k).mul (((ih k k).kstar).mul (ih k j)))

/-! ## Kleene's theorem -/

omit [DecidableEq σ] [Fintype α] in
open scoped Classical in
theorem accepts_eq_pathLang_union (M : DFA α σ) [Fintype σ] :
    M.accepts = {w | ∃ j ∈ (Finset.univ.filter (fun j => j ∈ M.accept) :
      Finset σ), w ∈ pathLang M Finset.univ M.start j} := by
  classical
  apply Set.ext
  intro w
  constructor
  · intro hw
    refine ⟨M.eval w, ?_, ⟨rfl, fun n _ _ => Finset.mem_univ _⟩⟩
    simpa using (M.mem_accepts.1 hw)
  · rintro ⟨j, hj, he, -⟩
    have hj' : j ∈ M.accept := by simpa using hj
    exact M.mem_accepts.2 (by rw [show M.eval w = j from he]; exact hj')

/-- **Kleene's theorem, hard direction.**  Every language accepted by a finite
deterministic automaton over a finite alphabet is denoted by a regular
expression. -/
theorem isRegexLang_accepts (M : DFA α σ) [Fintype σ] : IsRegexLang M.accepts := by
  classical
  refine IsRegexLang.congr (accepts_eq_pathLang_union M).symm ?_
  exact isRegexLang_finsetSup _ _ fun j _ => isRegexLang_pathLang M Finset.univ M.start j

/-- **Kleene's theorem, hard direction**, stated for regular languages. -/
theorem isRegexLang_of_isRegular {L : Language α} (h : L.IsRegular) : IsRegexLang L := by
  obtain ⟨σ', _, M, rfl⟩ := h
  classical
  have : Fintype σ' := Fintype.ofFinite σ'
  exact isRegexLang_accepts M

/-- **Kleene's theorem.**  Over a finite alphabet, a language is regular if and
only if it is denoted by a regular expression. -/
theorem isRegular_iff_isRegexLang {L : Language α} :
    L.IsRegular ↔ ∃ P : RegularExpression α, P.matches' = L := by
  constructor
  · exact isRegexLang_of_isRegular
  · rintro ⟨P, rfl⟩
    exact isRegular_matches' P

end UAM.Kleene
