import RequestProject.STCKG.CategoryGate
import RequestProject.Evolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Evolution and invariants, audited

Audit questions H8 (what kind of thing is evolution?) and H9 (what is an
invariant?).

## H8

The existing `Polymath.Evolution.Extends` is a preorder on graphs.  Here it is
sharpened to a **partial order** (`extends_antisymm`, via the extensionality
lemma `knowledgeGraph_ext`), which makes the associated thin category
`extendsThinCat` completely determined — it carries no information beyond the
order, so no functorial structure is introduced.

The directive's `Evolution = Functor` is *not* adopted, and more importantly
`Extends` alone is **not** an adequate model of evolution:
`promote_not_extends` shows that promoting the maturity of an object is a legal
evolution step which is *not* an extension.  The repair is `EvolveStep` /
`Evolves`: the reflexive–transitive closure of "grow or promote", for which
identifiers really are monotone (`evolves_ids_subset`) and acyclicity really is
preserved (`evolves_preserves_acyclic`).

## H9

An invariant is a **preservation property of a specified transformation**
(`Preserves`), never a morphism.  The typing matters:

* `promote_preserves_acyclic` — promotion preserves acyclicity;
* `extends_not_preserves_acyclic` — plain growth does **not**: adding one
  relation can create a cycle;
* `promote_not_preserves_certified` — promotion preserves certification only
  when the target level is high enough (the existing `certified_promote`
  hypothesis is necessary, not decorative).
-/

namespace Polymath.STCKG

open Polymath Polymath.Dependency Polymath.Verification Polymath.Evolution

/-! ## Extensionality and the order structure of `Extends` -/

/-- Two knowledge graphs with the same objects and relations are equal: the
integrity fields are propositions and carry no data. -/
theorem knowledgeGraph_ext {g h : KnowledgeGraph} (ho : g.objects = h.objects)
    (hr : g.relations = h.relations) : g = h := by
  cases g; cases h; cases ho; cases hr; rfl

/-- **H8.** `Extends` is antisymmetric, hence a partial order and not merely a
preorder. -/
theorem extends_antisymm {g h : KnowledgeGraph} (h₁ : Extends g h) (h₂ : Extends h g) : g = h :=
  knowledgeGraph_ext (Finset.Subset.antisymm h₁.1 h₂.1) (Finset.Subset.antisymm h₁.2 h₂.2)

/-- The thin category of graph growth.  It passes the Category Gate, and that is
all: being thin, it adds nothing to the partial order. -/
def extendsThinCat : ThinCat KnowledgeGraph where
  hom := Extends
  id' := Extends.refl
  comp' := fun h k => h.trans k

/-! ## Concrete graphs used by the counterexamples -/

/-- A single concept object. -/
def objX : KnowledgeObject := ⟨0, .concept, "x", .hypothesis, 0⟩

/-- The graph with one object and no relations. -/
def graphX : KnowledgeGraph where
  objects := {objX}
  relations := ∅
  unique_id := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  src_closed := by intro r hr; simp at hr
  tgt_closed := by intro r hr; simp at hr

/-- A structural self-loop on the identifier `0`. -/
def loopRel : KnowledgeRelation := ⟨0, 0, .dependsOn, 0⟩

/-- The same graph with a self-dependency added. -/
def graphLoop : KnowledgeGraph where
  objects := {objX}
  relations := {loopRel}
  unique_id := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  src_closed := by
    intro r hr
    rw [Finset.mem_singleton] at hr
    exact ⟨objX, Finset.mem_singleton_self _, by rw [hr]; rfl⟩
  tgt_closed := by
    intro r hr
    rw [Finset.mem_singleton] at hr
    exact ⟨objX, Finset.mem_singleton_self _, by rw [hr]; rfl⟩

theorem graphX_acyclic : Acyclic graphX := by
  have hno : ∀ x y : ℕ, ¬ DependsDirect graphX x y := by
    rintro x y ⟨r, hr, -⟩
    simp [graphX] at hr
  have hgen : ∀ x y : ℕ, ¬ Depends graphX x y := by
    intro x y h
    induction h with
    | single hd => exact hno _ _ hd
    | tail _ hd _ => exact hno _ _ hd
  exact fun a => hgen a a

theorem graphLoop_not_acyclic : ¬ Acyclic graphLoop := by
  intro h
  exact h 0 (depends_of_direct ⟨loopRel, Finset.mem_singleton_self _, rfl, rfl, rfl⟩)

theorem extends_graphX_graphLoop : Extends graphX graphLoop :=
  ⟨Finset.Subset.refl _, by simp [graphX, graphLoop]⟩

/-! ## H9 — invariants are preservation properties -/

/-- An invariant of a transformation: a property preserved by every step of the
given relation.  Invariants are typed by the transformation they survive. -/
def Preserves (R : KnowledgeGraph → KnowledgeGraph → Prop)
    (P : KnowledgeGraph → Prop) : Prop :=
  ∀ g h, R g h → P g → P h

/-- Promotion, as a one-step transformation relation. -/
def PromoteStepRel (g h : KnowledgeGraph) : Prop :=
  ∃ (o : KnowledgeObject) (ho : o ∈ g.objects) (m : Maturity), h = promote g ho m

/-- Promotion preserves acyclicity. -/
theorem promote_preserves_acyclic : Preserves PromoteStepRel Acyclic := by
  rintro g h ⟨o, ho, m, rfl⟩ hg
  exact promote_acyclic hg ho m

/-- Promotion preserves the set of identifiers. -/
theorem promote_preserves_ids (g h : KnowledgeGraph) (hgh : PromoteStepRel g h) :
    h.ids = g.ids := by
  obtain ⟨o, ho, m, rfl⟩ := hgh
  exact promote_ids ho m

/-- **H9, counterexample.**  Acyclicity is *not* an invariant of graph growth:
adding a single structural relation can create a cycle.  So "invariant" is
meaningless without naming the transformation. -/
theorem extends_not_preserves_acyclic : ¬ Preserves Extends Acyclic := by
  intro h
  exact graphLoop_not_acyclic (h graphX graphLoop extends_graphX_graphLoop graphX_acyclic)

/-- A canonical object. -/
def objY : KnowledgeObject := ⟨0, .concept, "y", .canonical, 0⟩

/-- A graph certified at the `validated` level. -/
def graphY : KnowledgeGraph where
  objects := {objY}
  relations := ∅
  unique_id := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  src_closed := by intro r hr; simp at hr
  tgt_closed := by intro r hr; simp at hr

theorem objY_mem : objY ∈ graphY.objects := Finset.mem_singleton_self _

theorem graphY_certified : Certified graphY Maturity.validated := by
  intro a ha
  rw [KnowledgeGraph.mem_ids_iff] at ha
  obtain ⟨o, ho, rfl⟩ := ha
  rw [show o = objY from Finset.mem_singleton.1 ho]
  exact ⟨objY, ⟨objY_mem, rfl⟩, by decide⟩

/-- **H9, counterexample.**  Certification is preserved by promotion only when
the new maturity level is at least the certified one: promoting *downwards*
destroys it.  The hypothesis of the existing `certified_promote` is therefore
load-bearing. -/
theorem promote_not_preserves_certified :
    ¬ Preserves PromoteStepRel (fun g => Certified g Maturity.validated) := by
  intro h
  have hc : Certified (promote graphY objY_mem Maturity.hypothesis) Maturity.validated :=
    h graphY _ ⟨objY, objY_mem, Maturity.hypothesis, rfl⟩ graphY_certified
  have hid : (0 : ℕ) ∈ (promote graphY objY_mem Maturity.hypothesis).ids := by
    rw [promote_ids objY_mem]
    exact (KnowledgeGraph.mem_ids_iff _ _).2 ⟨objY, objY_mem, rfl⟩
  obtain ⟨p, hp, hpm⟩ := hc 0 hid
  have hpe : p = promoteObj objY Maturity.hypothesis :=
    hasObject_unique hp (hasObject_promote graphY objY_mem Maturity.hypothesis)
  rw [hpe] at hpm
  exact absurd hpm (by decide)

/-! ## H8 — evolution needs more than extension -/

/-- **H8, counterexample.**  Promotion is a legitimate evolution step that is
*not* an extension: the promoted object replaces the old one, so the old objects
are no longer a subset. -/
theorem promote_not_extends :
    ∃ (g : KnowledgeGraph) (o : KnowledgeObject) (ho : o ∈ g.objects) (m : Maturity),
      ¬ Extends g (promote g ho m) := by
  have ho : objX ∈ graphX.objects := Finset.mem_singleton_self _
  refine ⟨graphX, objX, ho, Maturity.validated, ?_⟩
  rintro ⟨hobj, -⟩
  have h1 : objX ∈ (promote graphX ho Maturity.validated).objects :=
    hobj (Finset.mem_singleton_self _)
  simp only [promote, Finset.mem_insert, Finset.mem_erase] at h1
  rcases h1 with h1 | ⟨hne, -⟩
  · exact absurd (congrArg KnowledgeObject.maturity h1) (by decide)
  · exact hne rfl

/-- One step of evolution: either the graph grows, or one object is promoted. -/
inductive EvolveStep : KnowledgeGraph → KnowledgeGraph → Prop
  | grow {g h : KnowledgeGraph} : Extends g h → EvolveStep g h
  | promoteObject {g : KnowledgeGraph} {o : KnowledgeObject} (ho : o ∈ g.objects)
      (m : Maturity) : EvolveStep g (promote g ho m)

/-- Evolution: any finite sequence of growth and promotion steps. -/
def Evolves : KnowledgeGraph → KnowledgeGraph → Prop := Relation.ReflTransGen EvolveStep

theorem evolves_refl (g : KnowledgeGraph) : Evolves g g := Relation.ReflTransGen.refl

theorem evolves_trans {g h k : KnowledgeGraph} (h₁ : Evolves g h) (h₂ : Evolves h k) :
    Evolves g k := h₁.trans h₂

theorem evolves_of_extends {g h : KnowledgeGraph} (hgh : Extends g h) : Evolves g h :=
  Relation.ReflTransGen.single (EvolveStep.grow hgh)

theorem evolves_promote (g : KnowledgeGraph) {o : KnowledgeObject} (ho : o ∈ g.objects)
    (m : Maturity) : Evolves g (promote g ho m) :=
  Relation.ReflTransGen.single (EvolveStep.promoteObject ho m)

/-- **H8, repaired model.**  Identifiers never disappear along evolution. -/
theorem evolves_ids_subset {g h : KnowledgeGraph} (hgh : Evolves g h) : g.ids ⊆ h.ids := by
  induction hgh with
  | refl => exact Finset.Subset.refl _
  | tail _ hstep ih =>
    cases hstep with
    | grow hext => exact ih.trans hext.ids_subset
    | promoteObject ho m => exact ih.trans (by rw [promote_ids ho m])

/-- Acyclicity is an invariant of promotion, but only of promotion; along a
general evolution it survives exactly when every growth step keeps it. -/
theorem evolveStep_promote_preserves_acyclic {g h : KnowledgeGraph}
    (hstep : EvolveStep g h) (hgrow : Extends g h → Acyclic h) (hg : Acyclic g) : Acyclic h := by
  cases hstep with
  | grow hext => exact hgrow hext
  | promoteObject ho m => exact promote_acyclic hg ho m

/-- If every growth step used along the way keeps the graph acyclic, so does the
whole evolution. -/
theorem evolves_preserves_acyclic {g h : KnowledgeGraph} (hgh : Evolves g h)
    (hgrow : ∀ a b : KnowledgeGraph, Extends a b → Acyclic a → Acyclic b)
    (hg : Acyclic g) : Acyclic h := by
  induction hgh with
  | refl => exact hg
  | tail _ hstep ih =>
    cases hstep with
    | grow hext => exact hgrow _ _ hext ih
    | promoteObject ho m => exact promote_acyclic ih ho m

end Polymath.STCKG
