import RequestProject.Certificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Curricula: staging a knowledge graph for learning

In an acyclic graph the dependency count `depCount` of `RequestProject.Certificate`
is a level function.  Grouping identifiers by level gives a *curriculum*: a
finite sequence of stages such that everything an object depends on is taught in
an earlier stage.

* `stage` — the identifiers at a given level, with `mem_stage_iff`;
* `stage_disjoint` — the stages partition the identifiers;
* `stage_lt_of_depends` — dependencies always live in strictly earlier stages;
* `level_lt_card` and `stage_eq_empty_of_card_le` — a graph with `n` objects has
  at most `n` nonempty stages.
-/

namespace Polymath.Curriculum

open Polymath Polymath.Dependency Polymath.Certificates

/-- The level of an identifier: the number of objects it depends on. -/
noncomputable def level (g : KnowledgeGraph) (a : ℕ) : ℕ := depCount g a

/-- The `k`-th stage of the curriculum. -/
noncomputable def stage (g : KnowledgeGraph) (k : ℕ) : Finset ℕ :=
  open Classical in g.ids.filter (fun a => level g a = k)

theorem mem_stage_iff {g : KnowledgeGraph} {k a : ℕ} :
    a ∈ stage g k ↔ a ∈ g.ids ∧ level g a = k := by
  classical
  simp [stage, Finset.mem_filter]

/-- Every identifier of the graph is scheduled, in exactly one stage. -/
theorem mem_stage_level {g : KnowledgeGraph} {a : ℕ} (ha : a ∈ g.ids) :
    a ∈ stage g (level g a) := mem_stage_iff.2 ⟨ha, rfl⟩

theorem stage_disjoint {g : KnowledgeGraph} {k k' : ℕ} (h : k ≠ k') {a : ℕ}
    (hk : a ∈ stage g k) (hk' : a ∈ stage g k') : False :=
  h ((mem_stage_iff.1 hk).2.symm.trans (mem_stage_iff.1 hk').2)

theorem stage_subset_ids (g : KnowledgeGraph) (k : ℕ) : stage g k ⊆ g.ids := by
  classical
  exact Finset.filter_subset _ _

/-- In an acyclic graph, dependencies are scheduled strictly earlier. -/
theorem level_lt_of_depends {g : KnowledgeGraph} (hg : Acyclic g) {a b : ℕ}
    (h : Depends g a b) : level g b < level g a := depCount_lt_of_depends hg h

theorem stage_lt_of_depends {g : KnowledgeGraph} (hg : Acyclic g) {a b : ℕ} {k l : ℕ}
    (h : Depends g a b) (ha : a ∈ stage g k) (hb : b ∈ stage g l) : l < k := by
  have := level_lt_of_depends hg h
  rw [(mem_stage_iff.1 ha).2, (mem_stage_iff.1 hb).2] at this
  exact this

/-- The level of an object of an acyclic graph is smaller than the number of
objects: the curriculum is finite. -/
theorem level_lt_card {g : KnowledgeGraph} (hg : Acyclic g) {a : ℕ} (ha : a ∈ g.ids) :
    level g a < g.ids.card := by
  classical
  have hsub : g.ids.filter (fun b => Depends g a b) ⊆ g.ids := Finset.filter_subset _ _
  have hne : a ∉ g.ids.filter (fun b => Depends g a b) := by
    intro hmem
    exact hg a (Finset.mem_filter.1 hmem).2
  have : g.ids.filter (fun b => Depends g a b) ⊂ g.ids :=
    ⟨hsub, fun hcon => hne (hcon ha)⟩
  simpa [level, depCount] using Finset.card_lt_card this

/-- There is nothing left to teach beyond stage `|ids|`. -/
theorem stage_eq_empty_of_card_le {g : KnowledgeGraph} (hg : Acyclic g) {k : ℕ}
    (hk : g.ids.card ≤ k) : stage g k = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro a ha
  obtain ⟨hmem, hlev⟩ := mem_stage_iff.1 ha
  have := level_lt_card hg hmem
  omega

/-- The whole graph is covered by the stages below `|ids|`. -/
theorem exists_stage_lt_card {g : KnowledgeGraph} (hg : Acyclic g) {a : ℕ} (ha : a ∈ g.ids) :
    ∃ k < g.ids.card, a ∈ stage g k :=
  ⟨level g a, level_lt_card hg ha, mem_stage_level ha⟩

end Polymath.Curriculum
