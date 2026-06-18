---
name: Proof status & revenue overclaim hazard
description: How to answer "what have we proven?" and monetization questions honestly — the corpus overclaims in places; lead with defensible facts.
---

# Math proof status

Authoritative source: `papers/MATHEMATICAL_PROOF_STATUS_AUDIT_2026-05-15.md` — **cite Appendix A** (comprehensive corrected sweep), NOT the file's narrower §1 ("zero new theorems", later retracted).

Durable rules (the *counts/paths live in the audit*, don't re-memorize them):
- The only genuinely proven Lean theorems are **elementary identities** (golden ratio, Euler identity, toy energy decay, L×E bounds). **No Millennium Prize problem is closed.**
- **"0 sorry" ≠ proved.** A file can be sorry-free yet *axiomatize the hard claim* (e.g. `lean4/BSD.lean` self-declares "not a proof of BSD" despite 0 sorry). Always also check `axiom`/`admit`/`native_decide` and, when possible, `#print axioms`.
- "Machine-verified" requires a full `lake build` + `#print axioms`. Most clean files are only **source-inspection audit-verified** — state which when asked.
- The `*CONVENTIONAL_PROOF*` / `conventional_proofs/*` markdowns are **sketches with disclosed gaps**, not closures.

**Why:** users repeatedly ask "what have we proven in conventional axioms?"; the honest answer (elementary theorems + a pre-registered record of disconfirming our own conjectures) is a credibility ASSET; the overclaims are a liability.

# Revenue / business-doc overclaim hazard

The older business docs (`BUSINESS_EXECUTIVE_SUMMARY.md`, `INVESTOR_MONETIZATION_GUIDE.md`) lead with hype — "99.2% accuracy / +629% backtest / 14 undefeatable proofs / proved binary logic impossible." Treat as marketing, NOT fact. The GSA trading number is **backtest-only** = classic overfit signature; the corpus's own CRD-1b + #69 say in-sample numbers carry ~no truth-signal without live forward results.

**How to apply:** anchor monetization answers to `REVENUE_ROADMAP_2026-06-18.md`. Lead with paths judged on objective merit that need no belief in the metaphysics (paid content; the AIMO Kaggle competition). Gate the GSA/trading pitch behind a real *live* paper-trading track record before any allocator contact. Never re-cite the AIMO "beat Claude" win without reproducing the benchmark first.
