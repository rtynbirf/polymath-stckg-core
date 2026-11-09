import RequestProject.OSA4.TortureSet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8000

/-!
# OSA-4.0 Registry: named operator tables

A `Registry` is a list of operators whose names identify them uniquely.  Lookup
by name is then unambiguous (`lookup_eq_some_iff`) and agrees with the name test
the compiler performs (`lookup_isSome_iff`).

The concrete seventeen-operator table of `TortureSet` is shown to be a legal
registry in this sense (`stdRegistry`).
-/

namespace Polymath.OSA4

/-- A table of operators in which the name determines the operator. -/
structure Registry where
  /-- The operators of the table. -/
  ops : List Op
  /-- Names identify operators. -/
  unique_names : ∀ a ∈ ops, ∀ b ∈ ops, a.name = b.name → a = b

namespace Registry

variable (r : Registry)

/-- Look an operator up by name. -/
def lookup (n : String) : Option Op := r.ops.find? (fun o => o.name = n)

variable {r}

/-- Lookup is correct and unambiguous. -/
theorem lookup_eq_some_iff {n : String} {o : Op} :
    r.lookup n = some o ↔ o ∈ r.ops ∧ o.name = n := by
  constructor
  · intro h
    have hmem : o ∈ r.ops := List.mem_of_find?_eq_some h
    have hname : (o.name = n) := by
      have := List.find?_some h
      simpa using this
    exact ⟨hmem, hname⟩
  · rintro ⟨hmem, hname⟩
    cases hfind : r.lookup n with
    | none =>
      rw [lookup, List.find?_eq_none] at hfind
      exact absurd (by simpa using hname) (hfind o hmem)
    | some p =>
      have hp : p ∈ r.ops := List.mem_of_find?_eq_some hfind
      have hpn : p.name = n := by
        have := List.find?_some hfind
        simpa using this
      rw [r.unique_names p hp o hmem (by rw [hpn, hname])]

/-- The compiler's name test is exactly successful lookup. -/
theorem lookup_isSome_iff {n : String} :
    (r.lookup n).isSome ↔ n ∈ r.ops.map (·.name) := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hmem, hname⟩ := lookup_eq_some_iff.1 ho
    exact hname ▸ List.mem_map_of_mem hmem
  · intro h
    obtain ⟨o, hmem, hname⟩ := List.mem_map.1 h
    rw [lookup_eq_some_iff.2 ⟨hmem, hname⟩]
    rfl

/-- Every operator of the table is found under its own name. -/
theorem lookup_name {o : Op} (ho : o ∈ r.ops) : r.lookup o.name = some o :=
  lookup_eq_some_iff.2 ⟨ho, rfl⟩

/-- A chain drawn from the table passes the compiler's registry check. -/
theorem name_mem_of_mem {ops : List Op} (h : ∀ o ∈ ops, o ∈ r.ops) :
    ∀ o ∈ ops, o.name ∈ r.ops.map (·.name) :=
  fun o ho => List.mem_map_of_mem (h o ho)

end Registry

/-- The seventeen operators of the torture set form a legal registry. -/
def stdRegistry : Registry where
  ops := registry
  unique_names := by decide

@[simp] theorem stdRegistry_ops : stdRegistry.ops = registry := rfl

theorem stdRegistry_lookup_measure : stdRegistry.lookup "MEASURE" = some opMEASURE := by decide

theorem stdRegistry_lookup_teleport : stdRegistry.lookup "TELEPORT" = none := by decide

end Polymath.OSA4
