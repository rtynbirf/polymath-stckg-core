import RequestProject.Retraction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deduplication

Two distinct objects with the same kind and label are duplicates: they record
the same piece of knowledge twice.  A graph is `Normalized` exactly when it has
no duplicates (`normalized_iff_no_duplicate`).

The main result is `exists_normalized_retraction`: repeatedly retracting one
member of a duplicate pair terminates in a normalized subgraph which still
records every `(kind, label)` present in the original.
-/

namespace Polymath.Dedup

open Polymath Polymath.Verification Polymath.Retraction Polymath.Evolution

/-- `a` and `b` are duplicates: distinct objects recording the same content. -/
def Duplicate (g : KnowledgeGraph) (a b : KnowledgeObject) : Prop :=
  a ∈ g.objects ∧ b ∈ g.objects ∧ a ≠ b ∧ a.kind = b.kind ∧ a.label = b.label

/-- Normalization is exactly the absence of duplicates. -/
theorem normalized_iff_no_duplicate (g : KnowledgeGraph) :
    g.Normalized ↔ ¬ ∃ a b, Duplicate g a b := by
  constructor
  · rintro hg ⟨a, b, ha, hb, hne, hk, hl⟩
    exact hne (hg a ha b hb hk hl)
  · intro hg a ha b hb hk hl
    by_contra hne
    exact hg ⟨a, b, ha, hb, hne, hk, hl⟩

/-- Retracting one member of a duplicate pair keeps a representative of its
content. -/
theorem retract_duplicate_keeps_content {g : KnowledgeGraph} {a b : KnowledgeObject}
    (h : Duplicate g a b) : b ∈ (retract g a).objects :=
  Finset.mem_erase.2 ⟨fun hba => h.2.2.1 hba.symm, h.2.1⟩

/-- The deduplication statement, as a predicate on graphs. -/
def HasNormalForm (g : KnowledgeGraph) : Prop :=
  ∃ h : KnowledgeGraph, h.Normalized ∧ Extends h g ∧
    ∀ o ∈ g.objects, ∃ p ∈ h.objects, p.kind = o.kind ∧ p.label = o.label

/-- Every knowledge graph can be deduplicated: some sequence of retractions
leads to a normalized subgraph that still records every `(kind, label)` of the
original. -/
theorem exists_normalized_retraction (g : KnowledgeGraph) : HasNormalForm g := by
  classical
  suffices H : ∀ n (g : KnowledgeGraph), g.objects.card ≤ n → HasNormalForm g from
    H g.objects.card g le_rfl
  intro n
  induction n with
  | zero =>
      intro g hg
      have hempty : g.objects = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hg)
      refine ⟨g, ?_, Extends.refl g, fun o ho => ⟨o, ho, rfl, rfl⟩⟩
      intro a ha
      simp [hempty] at ha
  | succ n ih =>
      intro g hg
      by_cases hnorm : g.Normalized
      · exact ⟨g, hnorm, Extends.refl g, fun o ho => ⟨o, ho, rfl, rfl⟩⟩
      · obtain ⟨a, b, hab⟩ : ∃ a b, Duplicate g a b := by
          by_contra hcon
          exact hnorm ((normalized_iff_no_duplicate g).2 hcon)
        have hlt : (retract g a).objects.card < g.objects.card := retract_card_lt hab.1
        have hcard : (retract g a).objects.card ≤ n := by omega
        obtain ⟨h, hnorm', hext, hcov⟩ := ih (retract g a) hcard
        refine ⟨h, hnorm', hext.trans (retract_extends g a), ?_⟩
        intro o ho
        by_cases hoa : o = a
        · subst hoa
          obtain ⟨p, hp, hk, hl⟩ := hcov b (retract_duplicate_keeps_content hab)
          exact ⟨p, hp, hk.trans hab.2.2.2.1.symm, hl.trans hab.2.2.2.2.symm⟩
        · exact hcov o (Finset.mem_erase.2 ⟨hoa, ho⟩)

/-- A normalized graph is its own normal form. -/
theorem hasNormalForm_of_normalized {g : KnowledgeGraph} (hg : g.Normalized) :
    HasNormalForm g := ⟨g, hg, Extends.refl g, fun o ho => ⟨o, ho, rfl, rfl⟩⟩

end Polymath.Dedup
