# Security Policy

## Scope

This repository carries a **machine-verified bridge contract** (11 Lean 4
theorems, kernel-audited axiom surface). The security-relevant assets are:

1. the formal contract itself (`RequestProject/STCKG/`) — integrity is enforced
   by the GATE 7R pipeline; please do not edit those files by hand;
2. the CI pipelines (`.github/workflows/`) — all third-party actions are pinned
   to commit SHAs, not mutable tags.

## Reporting a vulnerability

Open a GitHub issue **only if it does not disclose a working exploit path**.
For sensitive reports, contact the repository owner directly first.

Do NOT open public issues about:

- a contract regression that CI already flags (the badge turns red — that is
  the pipeline working as intended, not a secret);
- CI infrastructure flakiness (Mathlib cache outages, runner capacity).

## Credential hygiene (for contributors)

- Never paste access tokens into issues, PRs, chats, or commit messages.
- Prefer `gh auth login` (no PAT at all) or a **fine-grained PAT** scoped to
  this single repository with `Contents: read and write` only, and a short
  expiry (7–30 days).
- Tokens found in the wild must be revoked immediately
  (GitHub → Settings → Developer settings → Personal access tokens).
- CI never needs your PAT: workflows authenticate with the built-in
  `${{ github.token }}`, which is scoped to this repository and expires with
  the job.

## Verification of releases

Every release tag (`v0.2.0` and later) corresponds to a green GATE 7R run on
that exact commit. To reproduce the verification independently:

```bash
lake build        # expected: exit 0, 0 errors, 0 warnings
python3 scripts/axiom_gate.py
python3 scripts/gate_spec.py
./scripts/verify_theorems.sh
```
