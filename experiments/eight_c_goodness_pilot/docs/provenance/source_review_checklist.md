# Source Review Checklist

Use this checklist after each source import and hashing pass.

## File identity

- [ ] Filename matches manifest expectation.
- [ ] Destination path matches inbox manifest destination.
- [ ] Source hash recorded.

## Completeness

- [ ] Export appears complete (no obvious truncation).
- [ ] Attachments or linked fragments noted if missing.

## Date ordering

- [ ] Conversation date captured.
- [ ] Relative order versus related sources documented.

## Author provenance

- [ ] User-authored versus AI-authored segments identified.
- [ ] Mixed authorship segments marked for review.

## Historical definitions

- [ ] Historical definition candidates extracted.
- [ ] Supersession relations noted.

## Current definitions

- [ ] Current candidate definitions identified.
- [ ] Candidate-current text compared to canonical scaffold.

## Explicit reversals

- [ ] Any explicit reversals logged.
- [ ] Reversal scope and date noted.

## Unresolved contradictions

- [ ] Contradictions entered into `framework_conflicts.csv`.
- [ ] No silent reconciliation performed.

## Category boundaries

- [ ] GILE/HEM boundary implications captured.
- [ ] Cross-component interaction kept separate from category reassignment.

## Scale-dependent claims

- [ ] Scale assertions identified.
- [ ] Claimed scale changes logged without forced harmonization.

## Empirical claims

- [ ] Empirical claims flagged with source evidence level.
- [ ] Unsupported empirical claims left unresolved pending source support.

## Speculative claims

- [ ] Speculative statements identified and tagged.
- [ ] No speculative statement promoted to canonical without approval.

## Pilot-specific operational content

- [ ] Pilot procedures/config references extracted.
- [ ] Any hash/manifest references captured for provenance.

## Inputs needed for 21-item reconstruction

- [ ] Corpus content references captured.
- [ ] Metadata references captured.
- [ ] Prompt/schema references captured.
- [ ] Preregistration references captured.