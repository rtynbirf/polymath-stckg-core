import RequestProject.Atlas.UAM_Syntactic
import RequestProject.Atlas.UAM_Aperiodic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Noncounting languages and aperiodic syntactic monoids

A language is *`n`-noncounting* when no context can distinguish `n` from `n + 1`
repetitions of a factor.  This is the language-level shadow of aperiodicity:

* `UAM.Syntactic.noncounting_iff_aperiodic` — a regular language is noncounting
  for some `n` exactly when its syntactic monoid is aperiodic, equivalently
  (by `UAM.Green.aperiodic_iff_hTrivial`) exactly when that monoid is
  `H`-trivial.

The right-to-left direction needs no finiteness; the other direction turns the
element-wise stable exponents of an aperiodic finite monoid into a single
uniform exponent (`UAM.Green.exists_uniform_stable_pow`).
-/

namespace UAM.Syntactic

open UAM.Green

variable {α : Type}

/-! ## A uniform stable exponent -/

/-- In a finite aperiodic monoid one exponent works for every element. -/
theorem _root_.UAM.Green.exists_uniform_stable_pow {M : Type*} [Monoid M] [Finite M]
    (h : Aperiodic M) : ∃ n : ℕ, ∀ m : M, m ^ (n + 1) = m ^ n := by
  classical
  haveI := Fintype.ofFinite M
  choose f hf using h
  refine ⟨Finset.univ.sup f, fun m => ?_⟩
  have hle : f m ≤ Finset.univ.sup f := Finset.le_sup (Finset.mem_univ m)
  have h1 : m ^ (Finset.univ.sup f) = m ^ f m := by
    have hsplit : Finset.univ.sup f = f m + (Finset.univ.sup f - f m) := by omega
    rw [hsplit, pow_eq_of_pow_succ_eq (hf m)]
  have h2 : m ^ (Finset.univ.sup f + 1) = m ^ f m := by
    have hsplit : Finset.univ.sup f + 1 = f m + (Finset.univ.sup f + 1 - f m) := by omega
    rw [hsplit, pow_eq_of_pow_succ_eq (hf m)]
  rw [h1, h2]

/-! ## Noncounting languages -/

/-- `L` is `n`-noncounting when `n` and `n + 1` copies of a factor are
interchangeable in every context. -/
def Noncounting (L : Language α) (n : ℕ) : Prop :=
  ∀ u x y : FreeMonoid α, (x * u ^ n * y).toList ∈ L ↔ (x * u ^ (n + 1) * y).toList ∈ L

theorem syntacticHom_pow (L : Language α) (u : FreeMonoid α) (n : ℕ) :
    syntacticHom L (u ^ n) = (syntacticHom L u) ^ n := map_pow _ _ _

/-- Noncounting at exponent `n` says exactly that every element of the syntactic
monoid has `n` as a stable exponent. -/
theorem noncounting_iff_pow_eq (L : Language α) (n : ℕ) :
    Noncounting L n ↔ ∀ s : SyntacticMonoid L, s ^ (n + 1) = s ^ n := by
  constructor
  · intro h s
    obtain ⟨u, rfl⟩ := syntacticHom_surjective L s
    rw [← syntacticHom_pow, ← syntacticHom_pow, syntacticHom_eq_iff]
    intro x y
    exact (h u x y).symm
  · intro h u x y
    have hs : syntacticHom L (u ^ n) = syntacticHom L (u ^ (n + 1)) := by
      rw [syntacticHom_pow, syntacticHom_pow, h (syntacticHom L u)]
    exact (syntacticHom_eq_iff L _ _).1 hs x y

/-- **A language is noncounting exactly when its syntactic monoid is
aperiodic** (finiteness of the syntactic monoid, i.e. regularity of the
language, is used only for the forward direction). -/
theorem noncounting_iff_aperiodic (L : Language α) [Finite (SyntacticMonoid L)] :
    (∃ n, Noncounting L n) ↔ Aperiodic (SyntacticMonoid L) := by
  constructor
  · rintro ⟨n, hn⟩ s
    exact ⟨n, (noncounting_iff_pow_eq L n).1 hn s⟩
  · intro h
    obtain ⟨n, hn⟩ := UAM.Green.exists_uniform_stable_pow h
    exact ⟨n, (noncounting_iff_pow_eq L n).2 hn⟩

/-- An aperiodic syntactic monoid always yields a noncounting language, with no
finiteness assumption in this direction. -/
theorem noncounting_of_pow_eq {L : Language α} {n : ℕ}
    (h : ∀ s : SyntacticMonoid L, s ^ (n + 1) = s ^ n) : Noncounting L n :=
  (noncounting_iff_pow_eq L n).2 h

/-- **For a regular language, noncounting, aperiodic and `H`-trivial agree.** -/
theorem regular_noncounting_iff (L : Language α) (hL : L.IsRegular) :
    (∃ n, Noncounting L n) ↔ HTrivial (SyntacticMonoid L) := by
  haveI : Finite (SyntacticMonoid L) := (isRegular_iff_finite_syntacticMonoid L).1 hL
  rw [noncounting_iff_aperiodic L]
  exact aperiodic_iff_hTrivial

end UAM.Syntactic
