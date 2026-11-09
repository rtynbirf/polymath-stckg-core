import RequestProject.OSA4.Kernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Meta-schema of the OSA-4.0 predicate language

Structural measures of the predicate language and their behaviour under the
weakest-precondition transformer.  The key structural fact is that `wp` is a
*shape-preserving* rewrite: it replaces atoms by atoms and leaves the
connective skeleton untouched, so the depth of a predicate is invariant and its
size never grows.

* `Polymath.OSA4.Pred.depth`, `Polymath.OSA4.Pred.size` — structural measures;
* `Polymath.OSA4.depth_wp` — `wp` preserves depth;
* `Polymath.OSA4.size_wp_le` — `wp` never increases size;
* `Polymath.OSA4.depth_wpChain` — the same for whole chains;
* `Polymath.OSA4.Pred.IsAtom` and `Polymath.OSA4.isAtom_wp_of_isAtom` — atoms go
  to atoms.
-/

namespace Polymath.OSA4

namespace Pred

/-- Nesting depth of a predicate. -/
def depth : Pred → ℕ
  | .factExists _ => 1
  | .pnot p => p.depth + 1
  | .pand p q => max p.depth q.depth + 1
  | .por p q => max p.depth q.depth + 1
  | .pimp p q => max p.depth q.depth + 1
  | .gte _ _ => 1
  | .peq _ _ => 1
  | .ctrue => 1
  | .cfalse => 1
  | .cunknown => 1

/-- Number of nodes of a predicate. -/
def size : Pred → ℕ
  | .factExists _ => 1
  | .pnot p => p.size + 1
  | .pand p q => p.size + q.size + 1
  | .por p q => p.size + q.size + 1
  | .pimp p q => p.size + q.size + 1
  | .gte _ _ => 1
  | .peq _ _ => 1
  | .ctrue => 1
  | .cfalse => 1
  | .cunknown => 1

theorem depth_pos (p : Pred) : 0 < p.depth := by
  cases p <;> simp [depth]

theorem size_pos (p : Pred) : 0 < p.size := by
  cases p <;> simp [size]

theorem depth_le_size (p : Pred) : p.depth ≤ p.size := by
  induction p with
  | factExists _ => simp [depth, size]
  | pnot p ih => simp [depth, size]; omega
  | pand p q ihp ihq =>
    have := size_pos p
    have := size_pos q
    simp [depth, size]; omega
  | por p q ihp ihq =>
    have := size_pos p
    have := size_pos q
    simp [depth, size]; omega
  | pimp p q ihp ihq =>
    have := size_pos p
    have := size_pos q
    simp [depth, size]; omega
  | gte _ _ => simp [depth, size]
  | peq _ _ => simp [depth, size]
  | ctrue => simp [depth, size]
  | cfalse => simp [depth, size]
  | cunknown => simp [depth, size]

/-- Atomic predicates: no connectives. -/
def IsAtom : Pred → Prop
  | .factExists _ => True
  | .gte _ _ => True
  | .peq _ _ => True
  | .ctrue => True
  | .cfalse => True
  | .cunknown => True
  | _ => False

theorem isAtom_iff_depth_eq_one (p : Pred) : p.IsAtom ↔ p.depth = 1 := by
  cases p with
  | factExists _ => simp [IsAtom, depth]
  | gte _ _ => simp [IsAtom, depth]
  | peq _ _ => simp [IsAtom, depth]
  | ctrue => simp [IsAtom, depth]
  | cfalse => simp [IsAtom, depth]
  | cunknown => simp [IsAtom, depth]
  | pnot p =>
    simp only [IsAtom, depth, false_iff]
    have := depth_pos p
    omega
  | pand p q =>
    simp only [IsAtom, depth, false_iff]
    have := depth_pos p
    omega
  | por p q =>
    simp only [IsAtom, depth, false_iff]
    have := depth_pos p
    omega
  | pimp p q =>
    simp only [IsAtom, depth, false_iff]
    have := depth_pos p
    omega

end Pred

/-! ## Behaviour of the weakest precondition -/

/-- `wp` sends atoms to atoms. -/
theorem isAtom_wp_of_isAtom (o : Op) {p : Pred} (h : p.IsAtom) : (o.wp p).IsAtom := by
  cases p with
  | factExists f =>
    by_cases hp : f ∈ o.produces
    · simp [Op.wp, hp, Pred.IsAtom]
    · by_cases hk : f ∈ o.kill <;> simp [Op.wp, hp, hk, Pred.IsAtom]
  | gte v n => by_cases hv : v ∈ o.modifies <;> simp [Op.wp, hv, Pred.IsAtom]
  | peq v n => by_cases hv : v ∈ o.modifies <;> simp [Op.wp, hv, Pred.IsAtom]
  | ctrue => simpa [Op.wp] using h
  | cfalse => simpa [Op.wp] using h
  | cunknown => simpa [Op.wp] using h
  | pnot p => exact absurd h (by simp [Pred.IsAtom])
  | pand p q => exact absurd h (by simp [Pred.IsAtom])
  | por p q => exact absurd h (by simp [Pred.IsAtom])
  | pimp p q => exact absurd h (by simp [Pred.IsAtom])

/-- The weakest precondition has exactly the depth of its goal. -/
theorem depth_wp (o : Op) (p : Pred) : (o.wp p).depth = p.depth := by
  induction p with
  | factExists f =>
    by_cases hp : f ∈ o.produces
    · simp [Op.wp, hp, Pred.depth]
    · by_cases hk : f ∈ o.kill <;> simp [Op.wp, hp, hk, Pred.depth]
  | pnot p ih => simp [Op.wp, Pred.depth, ih]
  | pand p q ihp ihq => simp [Op.wp, Pred.depth, ihp, ihq]
  | por p q ihp ihq => simp [Op.wp, Pred.depth, ihp, ihq]
  | pimp p q ihp ihq => simp [Op.wp, Pred.depth, ihp, ihq]
  | gte v n => by_cases hv : v ∈ o.modifies <;> simp [Op.wp, hv, Pred.depth]
  | peq v n => by_cases hv : v ∈ o.modifies <;> simp [Op.wp, hv, Pred.depth]
  | ctrue => rfl
  | cfalse => rfl
  | cunknown => rfl

/-- The weakest precondition never grows the goal. -/
theorem size_wp_le (o : Op) (p : Pred) : (o.wp p).size ≤ p.size := by
  induction p with
  | factExists f =>
    by_cases hp : f ∈ o.produces
    · simp [Op.wp, hp, Pred.size]
    · by_cases hk : f ∈ o.kill <;> simp [Op.wp, hp, hk, Pred.size]
  | pnot p ih => simp [Op.wp, Pred.size]; omega
  | pand p q ihp ihq => simp [Op.wp, Pred.size]; omega
  | por p q ihp ihq => simp [Op.wp, Pred.size]; omega
  | pimp p q ihp ihq => simp [Op.wp, Pred.size]; omega
  | gte v n => by_cases hv : v ∈ o.modifies <;> simp [Op.wp, hv, Pred.size]
  | peq v n => by_cases hv : v ∈ o.modifies <;> simp [Op.wp, hv, Pred.size]
  | ctrue => simp [Op.wp]
  | cfalse => simp [Op.wp]
  | cunknown => simp [Op.wp]

/-- Chains of operators also preserve depth. -/
theorem depth_wpChain (ops : List Op) (p : Pred) : (wpChain ops p).depth = p.depth := by
  induction ops generalizing p with
  | nil => rfl
  | cons o t ih => rw [wpChain_cons, depth_wp, ih]

/-- Chains of operators never grow the goal. -/
theorem size_wpChain_le (ops : List Op) (p : Pred) : (wpChain ops p).size ≤ p.size := by
  induction ops generalizing p with
  | nil => exact le_rfl
  | cons o t ih => exact le_trans (size_wp_le o (wpChain t p)) (ih p)

end Polymath.OSA4
