# The GATE 7R Pipeline

This repository does not merely *contain* a proof — it **continuously defends**
it. The pipeline is a two-tier design: fast kernel-adjacent gates on every
push, and a battery of **independent** verifiers once a day.

## Why two tiers

Mathlib itself separates CI (fast, on push) from deep verification
(`lean4checker` in a cron job) because full kernel re-checks of a
Mathlib-sized environment are expensive. We adopt the same discipline and go
one step further: the nightly tier adds an **independent type checker
implemented from scratch in Rust** (nanoda), so the contract is never validated
by a single codebase alone.

## Tier 1 — `verify.yml` on every push

| Gate | Stage | Mechanism | What it catches |
|------|-------|-----------|-----------------|
| **G7R-0** | Specification | `scripts/gate_spec.py` (static, seconds) | forbidden constructs (`sorry`, `admit`, `axiom`, `unsafe`, `@[implemented_by]`, `native_decide`) in STCKG; theorem manifest drift (11 theorems, exactly once each); toolchain pinning mismatches (`lean-toolchain` vs `lakefile.toml` vs `lake-manifest.json`); leaked credentials |
| **G7R-1** | Baseline | `leanprover/lean-action@v1` (SHA-pinned) | toolchain / Mathlib cache failures |
| **G7R-2** | Elaboration | `lake build --wfail` | **zero warnings tolerance**: a hidden `sorry` emits a warning → build fails; also catches any elaboration regression across all 8158 jobs |
| **G7R-3a** | Kernel axiom audit | `axiom-audit` over the **compiled kernel environment** | `sorryAx`, `Lean.ofReduceBool`, home-rolled axioms — including ones reaching in through imports (a grep can never see these) |
| **G7R-3b** | Axiom precision | `scripts/axiom_gate.py` via `#print axioms` | axiom-policy violations: the 3 new bridge theorems (A4, B2, E4) must depend on **nothing but `propext`**; legacy 8 ⊆ Mathlib defaults |
| **G7R-3c** | Parity | `check_integrity.sh` + `verify_theorems.sh` | drift between what CI checks and what a human can reproduce locally |

The **GATE REPORT** job consolidates results into an artifact
(`GATE_REPORT.md`) and pushes a **dynamic badge** (`gate7r.svg`) to the
`badges` branch — the badge is generated from the actual gate matrix, not a
hand-edited image.

## Tier 2 — `nightly-deep.yml` (daily 03:00 UTC)

| Checker | Implementation | Role |
|---------|---------------|------|
| `nanoda` | independent Lean 4 type checker in **Rust** | re-verifies well-typedness of every declaration with a codebase that shares nothing with the Lean kernel; `sorry` forbidden |
| `leanchecker` | bundled kernel checker | re-checks every module of project + Mathlib (memory-capped via `LEAN_NUM_THREADS`) |
| `axiom-audit` | kernel environment walker | axiom surface allowlist |
| `axiom_gate.py` | `#print axioms` policy | bridge-theorem precision contract |

On failure a labeled issue is filed automatically with run/commit links.

## Defense in depth: why a cheat cannot pass

To sneak a false theorem through this pipeline an attacker would have to
simultaneously defeat:

1. static source scans (G7R-0, G7R-3c),
2. `--wfail` elaboration warnings (G7R-2),
3. the compiled-environment axiom audit (G7R-3a) — `sorryAx` and
   `Lean.ofReduceBool` are axiom *dependencies*, invisible to greps but not to
   the audit,
4. the `#print axioms` policy (G7R-3b),
5. an independent Rust type checker that never heard of our toolchain
   (nightly `nanoda`).

There is no single point of bypass.

## Engineering practices in use

- **SHA-pinned third-party actions** (not mutable tags) — supply-chain safety;
- **Dependabot daily** updates for the action versions;
- **concurrency groups** — superseded pushes cancel stale runs;
- **timeouts on every job** — a hung build cannot eat the runner quota;
- **squash-only merges** (repo settings) — history stays a chain of verified
  states;
- **orphan-branch badges** — branch history is never polluted by CI artifacts.

## Reproduce locally

```bash
lake build                       # G7R-1+2: exit 0, 0 errors, 0 warnings
python3 scripts/gate_spec.py     # G7R-0: static contracts
python3 scripts/axiom_gate.py    # G7R-3b: after lake build
./scripts/check_integrity.sh     # G7R-3c
./scripts/verify_theorems.sh     # G7R-3c
```
