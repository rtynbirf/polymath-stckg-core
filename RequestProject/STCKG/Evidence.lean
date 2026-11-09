import RequestProject.STCKG.Core
import RequestProject.OSA4.Epistemic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ST-CKG evidence profiles and their bridge to the existing `Belief` algebra

This file answers the evidence part of the audit (§6, and H7's evidence
component).  The existing epistemic layer of the project is the four-valued
`Polymath.OSA4.Belief = PT` with its join-semilattice structure.  The directive
asks for an `EvidenceProfile` record with separate, non-aggregated fields.  The
question the audit must settle is: *does the profile replace `Belief`, is it
subsumed by `Belief`, or is it a genuine extension?*

Result (both directions fail, so **neither subsumes the other**):

* `toBelief_not_injective` — different profiles collapse to the same belief, so
  `Belief` cannot replace the profile;
* `toBelief_not_surjective` — the profile fields listed in the directive cannot
  express `FALSE_KNOWN`, so the profile cannot replace `Belief`.

ORIGINAL: `EvidenceProfile` (directive §6) with the ten listed fields.
FORMALIZED: `EvidenceProfile` below, exactly those fields.
DIFFERENCE: an *extended* profile `RefutableProfile` adds a `refutation`
level.
WHY: without it the bridge to `Belief` cannot reach `FALSE_KNOWN`
(`toBelief_not_surjective`); with it the bridge becomes surjective
(`toBelief'_surjective`).  Both versions are kept, and the gap is a formal
statement rather than a remark.

Finally `no_single_threshold` shows that the four `fitFor…` flags cannot be
recovered from any scalar score with a threshold: this is the formal content of
the directive's "do not aggregate evidence into one number".
-/

namespace Polymath.STCKG

open Polymath.OSA4

/-! ## Evidence levels -/

/-- Strength of one kind of evidence. -/
inductive EvidenceLevel
  | absent | weak | moderate | strong
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numerical rank used only to order evidence levels. -/
def EvidenceLevel.rank : EvidenceLevel → ℕ
  | .absent => 0
  | .weak => 1
  | .moderate => 2
  | .strong => 3

theorem EvidenceLevel.rank_injective : Function.Injective EvidenceLevel.rank := by
  intro a b h
  cases a <;> cases b <;> simp [EvidenceLevel.rank] at h ⊢

instance : LinearOrder EvidenceLevel :=
  LinearOrder.lift' EvidenceLevel.rank EvidenceLevel.rank_injective

/-- Formal status of a claim (§3.1), independent of its epistemic status. -/
inductive FormalStatus
  | noFormalization | skeleton | formalized | partialVerified | verified
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Level of conflict recorded for a claim. -/
inductive ConflictLevel
  | none | minor | major | contradiction
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- An evidence profile, exactly the fields required by the directive.
No field is aggregated into any other. -/
structure EvidenceProfile where
  /-- Support from logical/derivational grounds. -/
  logicalSupport : EvidenceLevel
  /-- Support from empirical observation. -/
  empiricalSupport : EvidenceLevel
  /-- Reliability of the sources. -/
  sourceReliability : EvidenceLevel
  /-- Independence of the sources. -/
  independence : EvidenceLevel
  /-- Formal (Lean) status. -/
  formalStatus : FormalStatus
  /-- Recorded conflicts. -/
  conflictLevel : ConflictLevel
  /-- Scope in which the evidence applies. -/
  scope : String
  /-- Fit for use in derivations. -/
  fitForDerivation : Bool
  /-- Fit for use in teaching. -/
  fitForTeaching : Bool
  /-- Fit for use in prediction. -/
  fitForPrediction : Bool
  /-- Fit for use in engineering. -/
  fitForEngineering : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The empty profile: nothing is known and nothing is claimed. -/
def EvidenceProfile.blank : EvidenceProfile :=
  ⟨.absent, .absent, .absent, .absent, .noFormalization, .none, "", false, false, false, false⟩

/-- A profile of a Lean-verified statement. -/
def EvidenceProfile.leanVerified (scope : String) : EvidenceProfile :=
  ⟨.strong, .absent, .strong, .weak, .verified, .none, scope, true, true, false, true⟩

/-- A profile with real support but no formalization at all. -/
def supportedButUnverified : EvidenceProfile :=
  ⟨.strong, .strong, .moderate, .moderate, .noFormalization, .none, "audit", false, true, false,
    false⟩

/-! ## Bridge to the existing four-valued `Belief` -/

/-- Interpretation of an evidence profile as a belief of the existing
`Polymath.OSA4` epistemic layer.  A recorded contradiction becomes `CONFLICT`;
only a Lean-verified statement becomes `TRUE_KNOWN`; everything else stays
`UNKNOWN`, in accordance with §3.2 (formalization ≠ truth). -/
def EvidenceProfile.toBelief (p : EvidenceProfile) : Belief :=
  match p.conflictLevel with
  | .contradiction => PT.CONFLICT
  | _ => match p.formalStatus with
      | .verified => PT.TRUE_KNOWN
      | _ => PT.UNKNOWN

/-- Only Lean-verified, conflict-free profiles are read as `TRUE_KNOWN`
(no overclaim). -/
theorem toBelief_true_iff (p : EvidenceProfile) :
    p.toBelief = PT.TRUE_KNOWN ↔
      p.formalStatus = .verified ∧ p.conflictLevel ≠ .contradiction := by
  cases hc : p.conflictLevel <;> cases hf : p.formalStatus <;>
    simp [EvidenceProfile.toBelief, hc, hf]

/-- **The profile cannot be replaced by a belief.**  Two profiles that differ in
every evidence field can map to the same belief, so the four-valued algebra
loses information. -/
theorem toBelief_not_injective : ¬ Function.Injective EvidenceProfile.toBelief := by
  intro h
  have hb : EvidenceProfile.blank = supportedButUnverified :=
    h (a₁ := EvidenceProfile.blank) (a₂ := supportedButUnverified) rfl
  simp [EvidenceProfile.blank, supportedButUnverified] at hb

/-- **The belief algebra cannot be replaced by the profile either.**  With the
field list given in the directive, `FALSE_KNOWN` is unreachable: there is no way
to record "known to be false". -/
theorem toBelief_not_surjective : ¬ Function.Surjective EvidenceProfile.toBelief := by
  intro h
  obtain ⟨p, hp⟩ := h PT.FALSE_KNOWN
  cases hc : p.conflictLevel <;> cases hf : p.formalStatus <;>
    simp [EvidenceProfile.toBelief, hc, hf] at hp

/-! ### The repaired profile

Adding one field — the strength of evidence *against* the claim — repairs the
gap found above. -/

/-- An evidence profile together with the strength of refuting evidence. -/
structure RefutableProfile where
  /-- The evidence in favour, as specified by the directive. -/
  base : EvidenceProfile
  /-- The strength of evidence against the claim. -/
  refutation : EvidenceLevel
  deriving DecidableEq, Repr, Inhabited

/-- Bridge from the repaired profile to the existing belief algebra. -/
def RefutableProfile.toBelief (p : RefutableProfile) : Belief :=
  match p.base.conflictLevel with
  | .contradiction => PT.CONFLICT
  | _ =>
    match p.refutation with
    | .strong => PT.FALSE_KNOWN
    | _ => p.base.toBelief

/-- The repaired bridge reaches every belief value. -/
theorem toBelief'_surjective : Function.Surjective RefutableProfile.toBelief := by
  intro b
  cases b with
  | TRUE_KNOWN =>
    exact ⟨⟨{ EvidenceProfile.blank with formalStatus := .verified }, .absent⟩, rfl⟩
  | FALSE_KNOWN => exact ⟨⟨EvidenceProfile.blank, .strong⟩, rfl⟩
  | UNKNOWN => exact ⟨⟨EvidenceProfile.blank, .absent⟩, rfl⟩
  | CONFLICT =>
    exact ⟨⟨{ EvidenceProfile.blank with conflictLevel := .contradiction }, .absent⟩, rfl⟩

/-- A claim can be simultaneously Lean-verified and strongly refuted
empirically; the bridge then reports the refutation, and the profile keeps both
facts separately.  This is `FORMALIZATION ≠ TRUTH` made concrete. -/
theorem verified_and_refuted_distinguished :
    ∃ p : RefutableProfile,
      p.base.formalStatus = .verified ∧ p.refutation = .strong ∧
      p.toBelief = PT.FALSE_KNOWN ∧ p.base.toBelief = PT.TRUE_KNOWN :=
  ⟨⟨{ EvidenceProfile.blank with formalStatus := .verified }, .strong⟩, rfl, rfl, rfl, rfl⟩

/-! ## No scalar aggregation -/

/-- The four fitness flags are logically independent: every combination occurs. -/
theorem fitness_flags_independent (b₁ b₂ b₃ b₄ : Bool) :
    ∃ p : EvidenceProfile, p.fitForDerivation = b₁ ∧ p.fitForTeaching = b₂ ∧
      p.fitForPrediction = b₃ ∧ p.fitForEngineering = b₄ :=
  ⟨{ EvidenceProfile.blank with fitForDerivation := b₁, fitForTeaching := b₂, fitForPrediction := b₃, fitForEngineering := b₄ }, rfl, rfl, rfl, rfl⟩

/-- **No single confidence number.**  There is no scalar score together with a
threshold that decides two different fitness dimensions at once, because a
profile may be fit for derivation and unfit for teaching. -/
theorem no_single_threshold (f : EvidenceProfile → ℤ) (t : ℤ) :
    ¬ ((∀ p, p.fitForDerivation = true ↔ t ≤ f p) ∧
       (∀ p, p.fitForTeaching = true ↔ t ≤ f p)) := by
  rintro ⟨h₁, h₂⟩
  set p : EvidenceProfile := { EvidenceProfile.blank with fitForDerivation := true } with hp
  have hd : p.fitForDerivation = true := rfl
  have ht : p.fitForTeaching = false := rfl
  have : t ≤ f p := (h₁ p).1 hd
  have := (h₂ p).2 this
  simp [ht] at this

/-- Confidence is not truth (§6): the existing integer `confidence` field of a
`KnowledgeObject` is independent of the belief attached to a profile — the same
confidence value coexists with `TRUE_KNOWN` and with `CONFLICT`. -/
theorem confidence_not_truth :
    ∃ (o : Polymath.KnowledgeObject) (p q : EvidenceProfile),
      p.toBelief = PT.TRUE_KNOWN ∧ q.toBelief = PT.CONFLICT ∧
      o.confidence = 100 :=
  ⟨⟨0, .concept, "x", .hypothesis, 100⟩,
   { EvidenceProfile.blank with formalStatus := .verified },
   { EvidenceProfile.blank with conflictLevel := .contradiction }, rfl, rfl, rfl⟩

/-- `RefutableProfile.toBelief` is still not injective: two refutable
profiles that differ only in `logicalSupport` (a field not examined by
`toBelief'`) map to the same belief value `PT.UNKNOWN`.

**Witness:** Two `RefutableProfile` values with `base.logicalSupport`
set to `.strong` and `.moderate` respectively, all other fields
identical (blank). Both have `conflictLevel = .none`, `refutation = .absent`,
`formalStatus = .noFormalization`, so both evaluate to `PT.UNKNOWN`. -/
theorem toBelief'_not_injective : ¬ Function.Injective RefutableProfile.toBelief := by
  intro h
  -- CONCRETE WITNESS: two profiles, same belief-relevant fields, different logicalSupport
  have h_eq : RefutableProfile.toBelief
      ⟨{ EvidenceProfile.blank with logicalSupport := .strong }, .absent⟩ =
    RefutableProfile.toBelief
      ⟨{ EvidenceProfile.blank with logicalSupport := .moderate }, .absent⟩ := by
    simp [RefutableProfile.toBelief, EvidenceProfile.toBelief, EvidenceProfile.blank]
  -- COMPUTABLE DISTINCTION: the witness profiles are not equal
  have h_ne : (⟨{ EvidenceProfile.blank with logicalSupport := .strong }, .absent⟩ :
        RefutableProfile) ≠
      ⟨{ EvidenceProfile.blank with logicalSupport := .moderate }, .absent⟩ := by
    simp [EvidenceProfile.blank]
  -- CONCLUSION: injectivity would force equal profiles from equal beliefs
  exact h_ne (h h_eq)


end Polymath.STCKG
