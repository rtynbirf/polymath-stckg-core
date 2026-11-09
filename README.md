# POLYMATH ST-CKG Core — RELEASE-0.2

> **Spatio-Temporal Categorial Knowledge Graph — machine-verified bridge contract.**
> Every claim in this repository is either proved in Lean 4, marked as a hypothesis,
> or marked as a structural audit result. Nothing in between.

[![GATE 7R](https://raw.githubusercontent.com/rtynbirf/polymath-stckg-core/badges/badges/gate7r.svg)](https://github.com/rtynbirf/polymath-stckg-core/actions/workflows/verify.yml)
[![GATE 7R as CI](https://github.com/rtynbirf/polymath-stckg-core/actions/workflows/verify.yml/badge.svg)](https://github.com/rtynbirf/polymath-stckg-core/actions/workflows/verify.yml)
[![NIGHTLY deep battery](https://github.com/rtynbirf/polymath-stckg-core/actions/workflows/nightly-deep.yml/badge.svg)](https://github.com/rtynbirf/polymath-stckg-core/actions/workflows/nightly-deep.yml)
![Theorems](https://img.shields.io/badge/bridge_theorems-11_verified-blue)
![Axioms](https://img.shields.io/badge/custom_axioms-0-success)
![sorry](https://img.shields.io/badge/sorry%2Fadmit-0-success)

---

## What is verified here

RELEASE-0.2 answers one question with machine-checked precision: **what exactly is
preserved and what is lost when the ST-CKG semantic layer maps onto the existing
Lean core** (`Polymath.Core`, `ProofGraph`, `OSA4.PT`).

| Bridge | Classification | Theorem-level evidence |
|--------|---------------|------------------------|
| `Avatar ↔ KnowledgeObject × AvatarExtra` | **LOSSLESS ON RESTRICTED IMAGE** | injective split, explicit image characterization |
| `Claim → ProofGraph.Step` | **LOSSY PROJECTION** | non-injectivity with explicit counterexample witness |
| `EvidenceProfile → PT` | **LOSSY PROJECTION** | non-injective AND non-surjective (FALSE_KNOWN unreachable) |
| `RefutableProfile → PT` | **LOSSY PROJECTION, SURJECTIVE** | surjective (repair) yet still non-injective (explicit witness) |
| `Referent → KnowledgeObject` | **NO NATURAL BRIDGE** | GATE 2 structural audit: no function exists |

Full evidence tables: [`docs/BRIDGE_STATUS.md`](docs/BRIDGE_STATUS.md) — the single
source of truth for every non-collapse obligation.

## Verification methodology: COUNTEREXAMPLE FIRST

For every negative property (non-injectivity, non-surjectivity) the repository
follows a fixed pipeline — the witness is a **primary object**, not a tactical
artifact:

```
NEGATIVE CLAIM → CONCRETE WITNESS → COMPUTABLE EQUALITY → COMPUTABLE DISTINCTION → CONTRADICTION
```

Example — `Claim.toStep` reads only `id` and `assumptions` out of 10 fields,
so two claims differing in `predicate` collapse to one `Step`
([`RequestProject/STCKG/Claim.lean`](RequestProject/STCKG/Claim.lean)):

```lean
have h_eq : Claim.toStep { claimA with predicate := "X" } =
    Claim.toStep { claimA with predicate := "Y" } := by simp [Claim.toStep, claimA]
have h_ne : { claimA with predicate := "X" } ≠ { claimA with predicate := "Y" } := by
  simp [claimA]
exact h_ne (h h_eq)
```

This methodology was born from a real failure: GATE 7 v1 failed the naive proofs
(implicit-argument parsing), GATE 7R rebuilt them witness-first and passed
independently. The failure analysis is preserved in
[`docs/GATE7R_RESULT.md`](docs/GATE7R_RESULT.md).

## GATE 7R as CI — a contract that defends itself

The independent verification pass is not a one-off event — **it runs on every push**.
[`.github/workflows/verify.yml`](.github/workflows/verify.yml) replays the full
GATE 7R protocol as a gate matrix:

1. **G7R-0 Specification** — static contracts in seconds: forbidden constructs,
   theorem manifest, toolchain pinning, secret scan;
2. **G7R-1+2 Baseline & Elaboration** — `lake build --wfail` via official
   [`leanprover/lean-action`](https://github.com/leanprover/lean-action) with
   Mathlib cache: zero warnings tolerance, a hidden `sorry` fails the build;
3. **G7R-3a Kernel axiom audit** — `axiom-audit` walks the *compiled kernel
   environment*: `sorryAx`, `Lean.ofReduceBool` and home-rolled axioms fail
   even when they reach in through imports;
4. **G7R-3b Axiom precision** — `#print axioms` policy: the 3 new bridge
   theorems (A4, B2, E4) depend on nothing but `propext`;
5. **G7R-3c Parity** — the same bash checks a human runs locally.

And once a day ([`nightly-deep.yml`](.github/workflows/nightly-deep.yml)) the
contract is re-verified by **independent implementations**: `nanoda` (a Lean 4
type checker written from scratch in Rust), `leanchecker` (kernel re-check of
every module) and the full axiom battery — with an automatic issue on failure.

All third-party actions are **pinned to commit SHAs**; Dependabot keeps them
fresh. Full design rationale: [`docs/PIPELINE.md`](docs/PIPELINE.md).

If anyone weakens a theorem, adds an axiom, or hides a `sorry`, the badge goes red —
and there is no single point of bypass.

## Reproduce locally

```bash
git clone https://github.com/rtynbirf/polymath-stckg-core
cd polymath-stckg-core
lake build          # 8158 jobs, expected: exit 0, 0 errors, 0 warnings
python3 scripts/gate_spec.py     # G7R-0 static contracts
python3 scripts/axiom_gate.py    # G7R-3b axiom precision (after lake build)
./scripts/verify_theorems.sh   # 11/11 theorems found
./scripts/check_integrity.sh   # 0 forbidden constructs in STCKG/
```

Requirements: [elan](https://leanprover.github.io/lean4/doc/setup.html)
(toolchain pinned in `lean-toolchain`: `leanprover/lean4:v4.28.0`).

## Repository map

```
├── RequestProject/
│   ├── STCKG/            ← the 9-file verified semantic layer (105+ theorems)
│   │   ├── Core.lean         Referent / View / Avatar / split (+ A4)
│   │   ├── Evidence.lean     EvidenceProfile / RefutableProfile → PT (+ E4)
│   │   ├── Claim.lean        Claim → ProofGraph bridge (+ B2)
│   │   ├── Correspondence.lean   two independent axes (32 combos)
│   │   ├── CategoryGate.lean     category applicability, fibration REJECTED
│   │   ├── EvolutionAudit.lean   evolution ≠ extension
│   │   ├── Composition.lean      confidence ≠ truth
│   │   ├── IndexedFamily.lean    fibres, non-invertible patches
│   │   └── Index.lean            capstone: H1–H10, 7 kernel elements
│   ├── ProofGraph.lean   existing proof-graph layer (bridge target)
│   └── Main.lean         40 #print axioms transparency checks
├── docs/                 ← bridge contract, GATE 7R record, PIPELINE design
├── scripts/              ← verification scripts (same as CI)
├── SECURITY.md           ← disclosure + credential hygiene policy
└── .github/workflows/    ← GATE 7R on push + NIGHTLY deep battery
```

## Engineering layer (separate)

The Python/Neo4j projection layer (`STCKG_Core_v1.0.py`, `STCKG_Schema_v1.0.cypher`)
is **not** part of this verified contract. The Lean → Neo4j projection contract
(GATE 8) is planned next and will classify every mapping as DIRECT / BRIDGE /
DERIVED / DEFERRED — projections stay projections; nothing will be rebranded as
an embedding.

## Honest status

| Status | Meaning |
|--------|---------|
| VERIFIED | proved in Lean AND independently re-verified (GATE 7R) |
| HYPOTHESIS | conjectured, not proved |
| DISPROVED | refuted, counterexample recorded |
| DEFERRED | no natural bridge; deliberately not constructed |

No projection is called an isomorphism. No PROVED is called VERIFIED. Epistemic
truth and formal derivability are never conflated — `settled_not_true` and
`derivable_does_not_imply_established` are theorems here, not slogans.

## License

MIT — see [LICENSE](LICENSE).

## Version history

| Tag | Event |
|-----|-------|
| `v0.2.0` | RELEASE-0.2: bridge contract verified (GATE 7R PASS, independent) |
