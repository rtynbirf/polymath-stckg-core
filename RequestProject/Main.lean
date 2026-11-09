import RequestProject.Core
import RequestProject.Dependency
import RequestProject.ProofGraph
import RequestProject.OSA4.Kernel
import RequestProject.OSA4.Compiler
import RequestProject.OSA4.TortureSet
import RequestProject.OSA4.Identity
import RequestProject.OSA4.Epistemic
import RequestProject.OSA4.Repair
import RequestProject.OSA4.Lawbook
import RequestProject.OSA4.Invariants
import RequestProject.OSA4.Registry
import RequestProject.OSA4.Audit.Torture20
import RequestProject.OSA5.Repair
import RequestProject.OSA4.Audit.Integration
import RequestProject.OSA5.Torture25
import RequestProject.OSA5.Index
import RequestProject.Gestalt.UCC
import RequestProject.Gestalt.SelfReference
import RequestProject.AdaptiveAgent
import RequestProject.UAM_ContextFree
import RequestProject.UAM_MyhillNerode
import RequestProject.UAM_Minimization
import RequestProject.Atlas.UAM_Free
import RequestProject.Atlas.UAM_Morphism
import RequestProject.Atlas.UAM_Syntactic
import RequestProject.Atlas.UAM_Idempotent
import RequestProject.Atlas.UAM_AlgebraicPumping
import RequestProject.Atlas.UAM_Green
import RequestProject.Atlas.UAM_Kleene
import RequestProject.Atlas.UAM_KleeneConverse
import RequestProject.Atlas.UAM_Closure
import RequestProject.UAM_Separation
import RequestProject.Bridges.RegularContextFree
import RequestProject.Bridges.OSA_UAM
import RequestProject.Bridges.GestaltUAM
import RequestProject.Bridges.GestaltAdaptiveAgent
import RequestProject.UAM_Ring
import RequestProject.UAM_ContextFreeClosure
import RequestProject.UAM_ContextFreeIntersection
import RequestProject.UAM_ContextFreeHomomorphism
import RequestProject.Atlas.UAM_NFA
import RequestProject.Atlas.UAM_Cayley
import RequestProject.Atlas.UAM_Reachability
import RequestProject.Atlas.UAM_StateComplexity
import RequestProject.OSA5.Pipeline
import RequestProject.Gestalt.AristotleCanon
import RequestProject.Atlas.UAM_Pumping
import RequestProject.Atlas.UAM_InverseHomomorphism
import RequestProject.UAM_ContextFreeEmptiness
import RequestProject.Atlas.UAM_Directionality
import RequestProject.Atlas.UAM_Submonoid
import RequestProject.Atlas.UAM_Semilattice
import RequestProject.Atlas.UAM_MonoidAction
import RequestProject.Atlas.UAM_Congruence
import RequestProject.Atlas.UAM_Emptiness
import RequestProject.OSA4.Basis
import RequestProject.OSA4.BasisWitnesses
import RequestProject.OSA4.Index
import RequestProject.UAM_Dyck
import RequestProject.Atlas.UAM_Unary
import RequestProject.UAM_ContextFreePumping
import RequestProject.UAM_ContextFreeAnBnCn
import RequestProject.OSA.Synthesis
import RequestProject.ExampleAutomaton
import RequestProject.Bridges.RightLinear
import RequestProject.UAM_ContextFreeFinitary
import RequestProject.Atlas.UAM_Factors
import RequestProject.Atlas.UAM_Shuffle
import RequestProject.Atlas.UAM_GreenFinite
import RequestProject.Atlas.UAM_Aperiodic
import RequestProject.Atlas.UAM_GreenLemma
import RequestProject.Atlas.UAM_Noncounting
import RequestProject.Atlas.UAM_StarFree
import RequestProject.UAM_ContextFreeFinitaryClosure
import RequestProject.UAM_SeparationFinitary
import RequestProject.UAM_ContextFreeCountable
import RequestProject.UAM_ContextFreeMathlib
import RequestProject.UAM_ContextFreeMathlibClosure
import RequestProject.Atlas.UAM_StarFreeClosure
import RequestProject.Atlas.UAM_StarFreeUnary
import RequestProject.Atlas.UAM_StarFreeLength
import RequestProject.Atlas.UAM_StarFreeMorphism
import RequestProject.Atlas.UAM_StarFreeSubword
import RequestProject.STCKG.Index

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# POLYMATH-ATLAS — top-level aggregation

This module imports every module of the project and checks the axiom footprint
of its headline theorems.  Every `#print axioms` below reports only the three
axioms of Lean's core logic (`propext`, `Classical.choice`, `Quot.sound`): the
development contains no `sorry` and declares no axioms of its own.

## Contents

* `Core`, `Dependency`, `ProofGraph` — the knowledge-graph ontology, its
  dependency structure, and forward chaining on proof graphs.
* `OSA4.Kernel` — the four-valued operational-semantics kernel, weakest
  preconditions, and the frame laws.
* `OSA4.Compiler` — the static checker, with `compile_verdict_pass_iff`
  characterising a `PASS` verdict exactly.
* `OSA4.TortureSet`, `OSA4.Audit.Torture20`, `OSA5.Torture25` — the torture
  suites T01–T25, all discharged by kernel computation.
* `OSA4.Identity`, `OSA4.Epistemic`, `OSA4.Repair`, `OSA4.Lawbook` — the type
  lattice, the belief algebra, one-step repair, and the eighteen laws.
* `OSA5.Repair` — bounded multistep repair search, sound and complete.
* `Gestalt.UCC`, `AdaptiveAgent` — the cognitive-system theorems T1–T5 and the
  active-inference agent layer.
* `UAM_ContextFree` — grammars, pushdown automata, and their equivalence.
* `UAM_MyhillNerode`, `UAM_Minimization` — the Myhill–Nerode relation, its
  quotient, and uniqueness of minimal automata up to isomorphism.
* `Atlas.UAM_Free`, `Atlas.UAM_Morphism`, `Atlas.UAM_Syntactic` — the free monoid
  of words, recognizability by finite monoids, and the syntactic monoid.
* `Atlas.UAM_Idempotent`, `Atlas.UAM_AlgebraicPumping` — idempotent powers in a
  finite monoid and the resulting algebraic pumping principle.
* `Gestalt.SelfReference` — Lawvere's fixed-point theorem and the self-model
  barrier.
* `UAM_Separation` — `aⁿbⁿ` is context-free but not regular.
* `Bridges.*` — the four convergence bridges.
* `UAM_Ring` — the regular languages as a Boolean Kleene subalgebra of the
  algebra of all languages.
* `UAM_ContextFreeClosure` — closure of the context-free languages under union,
  concatenation, Kleene star and reversal.
* `UAM_ContextFreeIntersection` — the triple construction: the intersection of a
  context-free language with a regular language is context-free.
* `UAM_ContextFreeHomomorphism` — context-free languages are closed under
  homomorphic images and under renaming of the alphabet.
* `Atlas.UAM_NFA` — nondeterministic and ε-automata accept exactly the regular
  languages, with the exponential bound on determinization.
* `Atlas.UAM_Cayley` — Cayley's theorem for monoids and the automaton of a
  monoid.
* `Atlas.UAM_Reachability` — trimming an automaton to its reachable states.
* `Atlas.UAM_StateComplexity` — state complexity of the boolean operations, with
  the Nerode lower bound.
* `OSA5.Pipeline` — the compile / repair / recheck pipeline and its exactness.
* `Atlas.UAM_Pumping` — the pumping lemma for regular languages, the resulting
  non-regularity criterion, and the unary language of square lengths.
* `Atlas.UAM_InverseHomomorphism` — closure of the regular languages under
  inverse homomorphism and under left and right quotients.
* `UAM_ContextFreeEmptiness` — productive nonterminals and the emptiness test
  for context-free grammars.
* `Atlas.UAM_Directionality`, `Atlas.UAM_Submonoid`, `Atlas.UAM_Semilattice`,
  `Atlas.UAM_MonoidAction`, `Atlas.UAM_Congruence` — word combinatorics, star
  closure, idempotent commutative monoids, transition monoids and saturating
  congruences.
* `Atlas.UAM_Emptiness` — the small-witness property, decidable emptiness and
  decidable equivalence of automata.
* `Atlas.UAM_Unary` — a language over a one-letter alphabet is regular exactly
  when its set of lengths is ultimately periodic; the prime lengths are not.
* `UAM_Dyck` — the Dyck language is context-free but not regular.
* `UAM_ContextFreePumping` — derivation trees for grammars in Chomsky normal
  form and the context-free pumping lemma.
* `UAM_ContextFreeAnBnCn` — no grammar in Chomsky normal form generates
  `aⁿbⁿcⁿ`.
* `OSA4.Basis`, `OSA4.BasisWitnesses`, `OSA4.Spaces`, `OSA4.MetaSchema`,
  `OSA4.Axes` — the ninety basis claims with their witnesses, observational
  agreement, structural measures and operator classification.
* `OSA.Synthesis` — budget-aware synthesis of plans conforming to a
  specification, sound, complete and minimal.
* `ExampleAutomaton` — a worked example: the parity automaton and an empty one.
* `Gestalt.AristotleCanon` — the self-description of the development, with each
  recorded count tied back to a theorem.
-/

namespace PolymathAtlas.Main

/-! ## Knowledge graph -/

#print axioms Polymath.Maturity.lifecycle_chain
#print axioms Polymath.RelationKind.structural_ne_causal
#print axioms Polymath.KnowledgeGraph.relation_resolves
#print axioms Polymath.chainConfidence_le

/-! ## OSA-4.0 kernel and compiler -/

#print axioms Polymath.OSA4.Op.eval_wp
#print axioms Polymath.OSA4.Op.law012_wp_sound
#print axioms Polymath.OSA4.Op.law012_wp_complete
#print axioms Polymath.OSA4.Op.factStatus_exec_untouched
#print axioms Polymath.OSA4.Op.law006_kill_live_fact
#print axioms Polymath.OSA4.Op.law017_invalidate_not_refute
#print axioms Polymath.OSA4.Op.law010_composition_sound
#print axioms Polymath.OSA4.eval_execChain_eq_eval_wpChain
#print axioms Polymath.OSA4.compile_verdict_pass_iff
#print axioms Polymath.OSA4.law007_pass_chainEnabled
#print axioms Polymath.OSA4.law005_consume_safety

/-! ## OSA-4.0 laws, repair and torture suites -/

#print axioms Polymath.OSA4.lawbook_holds
#print axioms Polymath.OSA4.lawbook_card
#print axioms Polymath.OSA4.law018_repair_sound
#print axioms Polymath.OSA4.law009_no_overclaim
#print axioms Polymath.OSA4.torture_all_pass
#print axioms Polymath.OSA4.torture_card
#print axioms Polymath.OSA4.torture20_all_pass
#print axioms Polymath.OSA4.torture20_card
#print axioms Polymath.OSA4.integration_all_pass
#print axioms Polymath.OSA4.integration_card

/-! ## OSA-5.0 multistep repair -/

#print axioms Polymath.OSA5.chainPred_eq_true_iff
#print axioms Polymath.OSA5.searchRepair_sound
#print axioms Polymath.OSA5.searchRepair_complete
#print axioms Polymath.OSA5.searchRepair_isSome_iff
#print axioms Polymath.OSA5.minRepair_length_le
#print axioms Polymath.OSA5.repaired_chain_compiles_pass
#print axioms Polymath.OSA5.torture25_all_pass
#print axioms Polymath.OSA5.torture25_card
#print axioms Polymath.OSA5.osa5_audit_report
#print axioms Polymath.OSA5.osa5_audit_cardinalities

/-! ## Gestalt UCC and the adaptive agent -/

#print axioms PolymathAtlas.Gestalt.UCC.t1_no_distinction_iff_constant
#print axioms PolymathAtlas.Gestalt.UCC.t2_informationGain_nonneg
#print axioms PolymathAtlas.Gestalt.UCC.t2_informationGain_eq_zero_iff
#print axioms PolymathAtlas.Gestalt.UCC.CognitiveSystem.t3_perfect_learningRate_zero
#print axioms PolymathAtlas.Gestalt.UCC.ErrorDriven.t4_perfect_step_id
#print axioms PolymathAtlas.Gestalt.UCC.t5_trajectory_revisits
#print axioms PolymathAtlas.AdaptiveAgent.klDiv_nonneg
#print axioms PolymathAtlas.AdaptiveAgent.ActivePolicyAgent.efe_nonneg

/-! ## Context-free languages -/

#print axioms UAM.ContextFree.yields_iff_reach
#print axioms UAM.ContextFree.grammar_language_toGrammar
#print axioms UAM.ContextFree.contextFree_iff_pda

/-! ## Myhill–Nerode and the regular / context-free separation -/

#print axioms UAM.MyhillNerode.myhill_nerode_finite_iff_regular
#print axioms UAM.MyhillNerode.nerodeDFA_accepts
#print axioms UAM.MyhillNerode.card_nerodeClasses_le_card_states
#print axioms UAM.Separation.anbnGrammar_language
#print axioms UAM.Separation.anbn_not_regular
#print axioms UAM.Separation.regular_lt_contextFree

/-! ## Bridges -/

#print axioms UAM.ContextFree.dfa_language_eq_grammar_language
#print axioms UAM.ContextFree.regular_subset_contextFree
#print axioms UAM.ContextFree.regular_subset_pda
#print axioms Polymath.Bridges.execAction_hom
#print axioms Polymath.Bridges.mem_opLanguage_iff_pass
#print axioms Polymath.Bridges.chainEquiv_right_congruence
#print axioms Polymath.Bridges.chainEquiv_refines_nerode
#print axioms PolymathAtlas.Bridges.trajectory_eq_evalFrom
#print axioms PolymathAtlas.Bridges.dfa_revisits
#print axioms PolymathAtlas.Bridges.no_distinction_language_trivial
#print axioms PolymathAtlas.Bridges.returnLanguage_contextFree
#print axioms PolymathAtlas.Bridges.bridge2_two_sided
#print axioms PolymathAtlas.Bridges.uccOfReflexive_drawsDistinction
#print axioms PolymathAtlas.Bridges.uccOfReflexive_revisits

/-! ## Knowledge-graph dependencies and proof graphs -/

#print axioms Polymath.Dependency.acyclic_of_layering
#print axioms Polymath.Dependency.exists_leaf
#print axioms Polymath.Dependency.exists_root
#print axioms Polymath.ProofGraph.mem_saturate_derivable
#print axioms Polymath.ProofGraph.exists_mem_saturate_of_derivable
#print axioms Polymath.ProofGraph.derivable_iff_mem_of_fixpoint

/-! ## OSA-4.0 chain invariants and registries -/

#print axioms Polymath.OSA4.factStatus_execChain_untouched
#print axioms Polymath.OSA4.factStatus_execChain_established
#print axioms Polymath.OSA4.invariant_execChain
#print axioms Polymath.OSA4.Registry.lookup_eq_some_iff

/-! ## Monoid recognizability, syntactic monoids and pumping -/

#print axioms UAM.Free.exists_unique_wordExtension
#print axioms UAM.Morphism.isRegular_iff_isRecognizable
#print axioms UAM.Syntactic.syntacticMonoid_recognizes
#print axioms UAM.Syntactic.isRegular_iff_finite_syntacticMonoid
#print axioms UAM.Idempotent.exists_pow_isIdempotentElem
#print axioms UAM.Pumping.regular_pumping_word

/-! ## Minimal automata -/

#print axioms UAM.Minimization.minimal_unique
#print axioms UAM.Minimization.nerodeDFA_minimal
#print axioms UAM.Minimization.minimal_iso_nerode

/-! ## Green's relations -/

#print axioms UAM.Green.exists_of_LEquiv_REquiv
#print axioms UAM.Green.dEquiv_iff_comm
#print axioms UAM.Green.jEquiv_of_dEquiv

/-! ## Kleene closure properties -/

#print axioms UAM.Kleene.isRegular_mul
#print axioms UAM.Kleene.isRegular_kstar
#print axioms UAM.Kleene.isRegular_matches'
#print axioms UAM.Kleene.pathLang_insert
#print axioms UAM.Kleene.isRegexLang_of_isRegular
#print axioms UAM.Kleene.isRegular_iff_isRegexLang
#print axioms UAM.Closure.isRegular_leftQuotient
#print axioms UAM.Closure.isRegular_reverse
#print axioms UAM.Closure.isRegular_comap
#print axioms UAM.Closure.isRegular_map

/-! ## Self-reference -/

#print axioms PolymathAtlas.Gestalt.SelfReference.lawvere_fixedPoint
#print axioms PolymathAtlas.Gestalt.SelfReference.no_surjective_to_predicates
#print axioms PolymathAtlas.Gestalt.SelfReference.no_complete_selfModel

/-! ## The regular languages as a Kleene subalgebra -/

#print axioms UAM.Ring.regular_kleene_closed
#print axioms UAM.Ring.mem_regularSubsemiring_iff_isRegexLang

/-! ## Closure properties of the context-free languages -/

#print axioms UAM.ContextFree.yields_relabel_iff
#print axioms UAM.ContextFree.unionGrammar_language
#print axioms UAM.ContextFree.concatGrammar_language
#print axioms UAM.ContextFree.starGrammar_language
#print axioms UAM.ContextFree.IsContextFree.union
#print axioms UAM.ContextFree.IsContextFree.mul
#print axioms UAM.ContextFree.IsContextFree.kstar
#print axioms UAM.ContextFree.contextFree_kleene_closed
#print axioms UAM.ContextFree.revGrammar_language
#print axioms UAM.ContextFree.IsContextFree.reverse
#print axioms UAM.ContextFree.prodGrammar_language
#print axioms UAM.ContextFree.IsContextFree.inter_regular
#print axioms UAM.ContextFree.homGrammar_language
#print axioms UAM.ContextFree.IsContextFree.hom
#print axioms UAM.ContextFree.IsContextFree.map

/-! ## Nondeterministic automata -/

#print axioms UAM.NFA.isRegular_iff_isNFARegular
#print axioms UAM.NFA.isRegular_iff_isEpsilonRegular
#print axioms UAM.NFA.regular_nfa_epsilon_equiv
#print axioms UAM.NFA.exists_dfa_card_le_two_pow

/-! ## Cayley's theorem and reachability -/

#print axioms UAM.Cayley.leftMul_injective
#print axioms UAM.Cayley.card_le_card_end
#print axioms UAM.Reachability.trim_accepts
#print axioms UAM.Reachability.trim_all_reachable
#print axioms UAM.Reachability.card_trim_le
#print axioms UAM.StateComplexity.AcceptedBy.inf
#print axioms UAM.StateComplexity.AcceptedBy.sup
#print axioms UAM.StateComplexity.AcceptedBy.compl
#print axioms UAM.StateComplexity.nerode_le_of_acceptedBy
#print axioms UAM.StateComplexity.acceptedBy_nerode

/-! ## The OSA-5.0 pipeline -/

#print axioms Polymath.OSA5.pipeline_verified_pass
#print axioms Polymath.OSA5.pipeline_repaired_pass
#print axioms Polymath.OSA5.pipeline_irreparable_iff
#print axioms Polymath.OSA5.pipeline_complete
#print axioms Polymath.OSA5.pipeline_mono
#print axioms Polymath.OSA5.pipeline_modelScenario
#print axioms Polymath.OSA5.pipeline_modelScenario_pass

/-! ## The pumping lemma -/

#print axioms UAM.PumpingLemma.regular_pumping
#print axioms UAM.PumpingLemma.not_isRegular_of_pumping_fails
#print axioms UAM.PumpingLemma.not_isRegular_unary_of_gaps
#print axioms UAM.PumpingLemma.squareLengths_not_isRegular

/-! ## Inverse homomorphisms and quotients -/

#print axioms UAM.InvHom.invHomDFA_accepts
#print axioms UAM.InvHom.isRegular_preimage_hom
#print axioms UAM.InvHom.isRegular_preimage_map
#print axioms UAM.InvHom.isRegular_rightQuotient
#print axioms UAM.InvHom.isRegular_leftQuotient
#print axioms UAM.InvHom.isRegular_twoSidedQuotient

/-! ## Emptiness of context-free languages -/

#print axioms UAM.ContextFree.productive_iff_exists_yields
#print axioms UAM.ContextFree.language_nonempty_iff_productive_start
#print axioms UAM.ContextFree.language_eq_empty_iff
#print axioms UAM.ContextFree.language_empty_of_no_rules

/-! ## Word combinatorics, star closure and monoid actions -/

#print axioms UAM.Directionality.commute_iff_wpow
#print axioms UAM.Directionality.conjugate_equivalence
#print axioms UAM.Submonoid.kstar_kstar
#print axioms UAM.Submonoid.mem_kstar_iff_mem_closure
#print axioms UAM.Semilattice.mul_isGLB
#print axioms UAM.MonoidAction.mem_transitionMonoid_iff
#print axioms UAM.Congruence.isRegular_iff_exists_finite_saturating_con

/-! ## Emptiness and equivalence of automata -/

#print axioms UAM.Emptiness.exists_short_of_accepts
#print axioms UAM.Emptiness.accepts_eq_empty_iff
#print axioms UAM.Emptiness.accepts_eq_iff_symmDiff_empty

/-! ## The Dyck language -/

#print axioms UAM.Dyck.dyckGrammar_language
#print axioms UAM.Dyck.dyck_contextFree
#print axioms UAM.Dyck.dyck_not_regular
#print axioms UAM.Dyck.dyck_contextFree_not_regular

/-! ## The OSA-4.0 basis -/

#print axioms Polymath.OSA4.basis_all_covered
#print axioms Polymath.OSA4.basis_card
#print axioms Polymath.OSA4.witness_all_hold
#print axioms Polymath.OSA4.osa4_summary

/-! ## Specification-driven plan synthesis -/

#print axioms Polymath.OSA.Spec.synthesize_sound
#print axioms Polymath.OSA.Spec.synthesize_isSome_iff
#print axioms Polymath.OSA.Spec.synthesize_shortest
#print axioms Polymath.OSA.Spec.synthesize_modelSpec

/-! ## The context-free pumping lemma -/

#print axioms UAM.ContextFree.Pumping.deriv_of_yields
#print axioms UAM.ContextFree.Pumping.pumpable_of_card_lt
#print axioms UAM.ContextFree.Pumping.pumping_lemma
#print axioms UAM.ContextFree.Pumping.pumping_lemma_applies
#print axioms UAM.ContextFree.AnBnCn.not_cnf_language

/-! ## Unary languages -/

#print axioms UAM.Unary.isRegular_iff_ultimatelyPeriodic
#print axioms UAM.Unary.isRegular_unaryLang_iff
#print axioms UAM.Unary.primeLengths_not_isRegular

/-! ## Worked automaton example -/

#print axioms Example.parityDFA_accepts
#print axioms Example.deadDFA_empty_by_bound
#print axioms Example.parity_ne_dead

/-! ## Right-linear grammars -/

#print axioms UAM.ContextFree.yields_iff_acceptsFrom
#print axioms UAM.ContextFree.nfaOf_accepts
#print axioms UAM.ContextFree.isRegular_of_rightLinear
#print axioms UAM.ContextFree.isRegular_iff_exists_rightLinear

/-! ## Finitary grammars -/

#print axioms UAM.ContextFree.isContextFree_trivial
#print axioms UAM.ContextFree.IsCFL.union
#print axioms UAM.ContextFree.IsCFL.mul
#print axioms UAM.ContextFree.IsCFL.kstar
#print axioms UAM.ContextFree.IsCFL.reverse
#print axioms UAM.ContextFree.isCFL_of_isRegular
#print axioms UAM.ContextFree.isCFL_kleene_closed

/-! ## Prefixes, suffixes and factors -/

#print axioms UAM.Factors.isRegular_leftQuotient_lang
#print axioms UAM.Factors.isRegular_prefixes
#print axioms UAM.Factors.isRegular_suffixes
#print axioms UAM.Factors.isRegular_factors

/-! ## Shuffle -/

#print axioms UAM.Shuffle.mem_shuffleNFA_evalFrom
#print axioms UAM.Shuffle.shuffleNFA_accepts
#print axioms UAM.Shuffle.isRegular_shuffle
#print axioms UAM.Shuffle.shuffle_comm

/-! ## Green's relations in a finite monoid -/

#print axioms UAM.Green.rEquiv_of_jEquiv_mul
#print axioms UAM.Green.lEquiv_of_jEquiv_mul
#print axioms UAM.Green.dEquiv_of_jEquiv
#print axioms UAM.Green.jEquiv_iff_dEquiv

/-! ## Closure and separation for finitary grammars -/

#print axioms UAM.ContextFree.IsCFL.hom
#print axioms UAM.ContextFree.IsCFL.inter_regular
#print axioms UAM.ContextFree.finite_threaded
#print axioms UAM.Separation.anbn_isCFL
#print axioms UAM.Separation.regular_lt_isCFL

/-! ## Agreement with Mathlib's context-free grammars -/

#print axioms UAM.ContextFree.derives_of_yields
#print axioms UAM.ContextFree.yields_of_derives
#print axioms UAM.ContextFree.isCFL_iff_isContextFree
#print axioms UAM.ContextFree.isContextFree_add
#print axioms UAM.ContextFree.isContextFree_mul
#print axioms UAM.ContextFree.isContextFree_kstar
#print axioms UAM.ContextFree.isContextFree_inter_regular
#print axioms UAM.ContextFree.isContextFree_hom

/-! ## Aperiodicity -/

#print axioms UAM.Green.aperiodic_of_hTrivial
#print axioms UAM.Green.hTrivial_of_aperiodic
#print axioms UAM.Green.aperiodic_iff_hTrivial

/-! ## Counting context-free languages -/

#print axioms UAM.ContextFree.exists_natGrammar_of_isCFL
#print axioms UAM.ContextFree.isCFL_iff_exists_natGrammar
#print axioms UAM.ContextFree.countable_setOf_isCFL
#print axioms UAM.ContextFree.exists_not_isCFL

/-! ## Green's lemma and maximal subgroups -/

#print axioms UAM.Green.green_lemma_R
#print axioms UAM.Green.green_lemma_L
#print axioms UAM.Green.exists_hEquiv_inverse
#print axioms UAM.Green.hEquiv_mul
#print axioms UAM.Green.maximalSubgroup
#print axioms UAM.Green.aperiodic_iff_subgroups_trivial

/-! ## Noncounting languages -/

#print axioms UAM.Green.exists_uniform_stable_pow
#print axioms UAM.Syntactic.noncounting_iff_pow_eq
#print axioms UAM.Syntactic.noncounting_iff_aperiodic
#print axioms UAM.Syntactic.regular_noncounting_iff

/-! ## Star-free languages -/

#print axioms UAM.StarFree.pow_split
#print axioms UAM.StarFree.noncounting_mul
#print axioms UAM.StarFree.IsStarFree.isRegular
#print axioms UAM.StarFree.IsStarFree.noncounting
#print axioms UAM.StarFree.IsStarFree.aperiodic
#print axioms UAM.StarFree.parityLang_isRegular
#print axioms UAM.StarFree.parityLang_not_starFree
#print axioms UAM.StarFree.exists_regular_not_starFree

/-! ## Closure properties of the star-free languages -/

#print axioms UAM.StarFree.isStarFree_univ
#print axioms UAM.StarFree.isStarFree_inter
#print axioms UAM.StarFree.isStarFree_sdiff
#print axioms UAM.StarFree.isStarFree_of_finite
#print axioms UAM.StarFree.isStarFree_reverse
#print axioms UAM.StarFree.isStarFree_leftQuotient
#print axioms UAM.StarFree.isStarFree_rightQuotient
#print axioms UAM.StarFree.isStarFree_sum
#print axioms UAM.StarFree.alphabetLang_pow
#print axioms UAM.StarFree.isStarFree_lengthEq
#print axioms UAM.StarFree.isStarFree_lengthGe
#print axioms UAM.StarFree.isStarFree_lengthLt
#print axioms UAM.StarFree.isStarFree_containsFactor
#print axioms UAM.StarFree.isStarFree_avoidsFactor
#print axioms UAM.StarFree.comap_mul
#print axioms UAM.StarFree.comap_char
#print axioms UAM.StarFree.isStarFree_comap
#print axioms UAM.StarFree.isStarFree_map_equiv
#print axioms UAM.StarFree.mem_subseqLang
#print axioms UAM.StarFree.isStarFree_containsSubword
#print axioms UAM.StarFree.isStarFree_avoidsSubword
#print axioms UAM.StarFree.isStarFree_containsAllSubwords

/-! ## Schützenberger's theorem over a one-letter alphabet -/

#print axioms UAM.StarFree.finite_or_cofinite_of_noncounting
#print axioms UAM.StarFree.isStarFree_of_finite_or_cofinite
#print axioms UAM.StarFree.starFree_iff_noncounting_unary
#print axioms UAM.StarFree.starFree_iff_finite_or_cofinite_unary
#print axioms UAM.StarFree.starFree_iff_aperiodic_unary
#print axioms UAM.StarFree.starFree_iff_hTrivial_unary

/-! ## ST-CKG semantic layer: the Foundational Audit -/

#print axioms Polymath.STCKG.coRefers_equivalence
#print axioms Polymath.STCKG.coRefers_not_same_representation
#print axioms Polymath.STCKG.same_representation_not_coRefers
#print axioms Polymath.STCKG.avatar_not_determined_by_referent_view
#print axioms Polymath.STCKG.avatar_to_core_injective
#print axioms Polymath.STCKG.toBelief_true_iff
#print axioms Polymath.STCKG.toBelief_not_injective
#print axioms Polymath.STCKG.toBelief_not_surjective
#print axioms Polymath.STCKG.toBelief'_surjective
#print axioms Polymath.STCKG.no_single_threshold
#print axioms Polymath.STCKG.axes_surjective
#print axioms Polymath.STCKG.correspondence_not_determined_by_endpoints
#print axioms Polymath.STCKG.realization_tag_does_not_entail_relation
#print axioms Polymath.STCKG.claim_not_correspondence
#print axioms Polymath.STCKG.settled_not_true
#print axioms Polymath.STCKG.derivable_of_assumptions_derivable
#print axioms Polymath.STCKG.derivable_does_not_imply_established
#print axioms Polymath.STCKG.precedes_trans
#print axioms Polymath.STCKG.overlaps_not_transitive
#print axioms Polymath.STCKG.causes_transitivity_not_automatic
#print axioms Polymath.STCKG.two_distinct_concept_paths
#print axioms Polymath.STCKG.hasLifts_iff_viewComplete
#print axioms Polymath.STCKG.avatarStore_not_hasLifts
#print axioms Polymath.STCKG.completedStore_hasLifts
#print axioms Polymath.STCKG.knowledgeGraph_ext
#print axioms Polymath.STCKG.extends_antisymm
#print axioms Polymath.STCKG.promote_not_extends
#print axioms Polymath.STCKG.evolves_ids_subset
#print axioms Polymath.STCKG.promote_preserves_acyclic
#print axioms Polymath.STCKG.extends_not_preserves_acyclic
#print axioms Polymath.STCKG.promote_not_preserves_certified
#print axioms Polymath.STCKG.transGen_idempotent
#print axioms Polymath.STCKG.confidence_does_not_determine_derivability
#print axioms Polymath.STCKG.storeFamily_disjoint
#print axioms Polymath.STCKG.viewComplete_iff_family_nonempty
#print axioms Polymath.STCKG.patchComp_assoc
#print axioms Polymath.STCKG.patch_not_invertible
#print axioms Polymath.STCKG.bumpVersion_injective
#print axioms Polymath.STCKG.foundational_audit_holds
#print axioms Polymath.STCKG.kernel_justified

/-! ## Canon -/

#print axioms PolymathAtlas.Gestalt.Canon.canon_selfConsistent
#print axioms PolymathAtlas.Gestalt.Canon.canon_pipeline

end PolymathAtlas.Main
