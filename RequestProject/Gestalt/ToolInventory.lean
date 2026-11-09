import RequestProject.Gestalt.MetaSkills

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Tool inventories

An inventory assigns to each tool the finite set of capabilities it provides.

* `provided` — the capabilities an inventory provides;
* `Covers` and `covers_iff` — when an inventory covers a requirement;
* `card_le_of_covers` — a covering inventory has at least as many capability
  slots as the requirement has entries, so a requirement larger than the total
  capability count cannot be covered (`not_covers_of_card_lt`);
* `covers_union` and `covers_mono` — coverage is monotone and combines.
-/

namespace PolymathAtlas.Gestalt.Tools

universe u v

variable {Tool : Type u} {Cap : Type v} [DecidableEq Cap]

/-- The capabilities provided by an inventory of tools. -/
def provided (cap : Tool → Finset Cap) (inv : Finset Tool) : Finset Cap :=
  inv.biUnion cap

theorem mem_provided_iff {cap : Tool → Finset Cap} {inv : Finset Tool} {c : Cap} :
    c ∈ provided cap inv ↔ ∃ t ∈ inv, c ∈ cap t := by
  simp [provided]

/-- An inventory covers a requirement when it provides every capability in it. -/
def Covers (cap : Tool → Finset Cap) (inv : Finset Tool) (req : Finset Cap) : Prop :=
  req ⊆ provided cap inv

theorem covers_iff (cap : Tool → Finset Cap) (inv : Finset Tool) (req : Finset Cap) :
    Covers cap inv req ↔ ∀ c ∈ req, ∃ t ∈ inv, c ∈ cap t := by
  constructor
  · intro h c hc
    exact mem_provided_iff.1 (h hc)
  · intro h c hc
    exact mem_provided_iff.2 (h c hc)

/-- Adding tools never loses coverage. -/
theorem covers_mono {cap : Tool → Finset Cap} {inv inv' : Finset Tool} (hsub : inv ⊆ inv')
    {req : Finset Cap} (h : Covers cap inv req) : Covers cap inv' req :=
  h.trans (Finset.biUnion_subset_biUnion_of_subset_left cap hsub)

/-- Coverage of a union is coverage of both parts. -/
theorem covers_union {cap : Tool → Finset Cap} {inv : Finset Tool} {req₁ req₂ : Finset Cap} :
    Covers cap inv (req₁ ∪ req₂) ↔ Covers cap inv req₁ ∧ Covers cap inv req₂ := by
  constructor
  · intro h
    exact ⟨Finset.Subset.trans Finset.subset_union_left h,
      Finset.Subset.trans Finset.subset_union_right h⟩
  · rintro ⟨h₁, h₂⟩
    exact Finset.union_subset h₁ h₂

/-- A covering inventory has at least as many capability slots as the
requirement has entries. -/
theorem card_le_of_covers {cap : Tool → Finset Cap} {inv : Finset Tool} {req : Finset Cap}
    (h : Covers cap inv req) : req.card ≤ ∑ t ∈ inv, (cap t).card :=
  le_trans (Finset.card_le_card h) (Finset.card_biUnion_le)

/-- A requirement bigger than the total capability count cannot be covered. -/
theorem not_covers_of_card_lt {cap : Tool → Finset Cap} {inv : Finset Tool} {req : Finset Cap}
    (h : ∑ t ∈ inv, (cap t).card < req.card) : ¬ Covers cap inv req :=
  fun hcov => absurd (card_le_of_covers hcov) (by omega)

/-- An inventory of single-capability tools covers a requirement only if it has
at least as many tools as the requirement has capabilities. -/
theorem card_inv_le_of_covers_of_single {cap : Tool → Finset Cap} {inv : Finset Tool}
    {req : Finset Cap} (hsingle : ∀ t ∈ inv, (cap t).card ≤ 1) (h : Covers cap inv req) :
    req.card ≤ inv.card := by
  refine le_trans (card_le_of_covers h) ?_
  calc ∑ t ∈ inv, (cap t).card ≤ ∑ _t ∈ inv, 1 := Finset.sum_le_sum hsingle
    _ = inv.card := by simp

end PolymathAtlas.Gestalt.Tools
