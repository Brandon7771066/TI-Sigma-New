# Authority Axis (AA) Pilot — Operationalization for T45-8

**Date:** 2026-05-11 (Pass 47)
**Status:** READY for Brandon-side recruitment.
**Trigger:** Brandon's Pass-47 ask "Tell me more about the AA Pilot."
**Prerequisite reading:** `papers/AUTHORITY_AXIS_AA_2026-05-07.md` (full AA theory paper)

---

## §1 — Quick recap: what AA is

The **Authority Axis (AA)** is the 5th truth-axis in TI Sigma (alongside PD-real, PD-imaginary, MR Truth Labels, and τ/δ separability). It tracks an agent's **operative authority grant** — willingness to act on, defer to, and build on a proposition — independent of whether the proposition is epistemically settled.

Two sub-axes:
- **AA-self**: how much operative authority the agent grants its own current understanding.
- **AA-other**: how much operative authority the agent grants to external sources (experts, lineages, institutions, peers).

**Operating principle:** honest AA-grants require **simultaneous foreground belief AND subconscious doubt-reservation** — both, not either.

---

## §2 — Why AA needs psychometric validation

Right now, AA is a *definition* (frozen 2026-05-07) — not an *instrument*. It can be invoked theoretically but cannot be measured. Without measurement, AA is unfalsifiable: any predicted relationship between AA and real-world behavior is unverifiable.

**T45-8 (per Pass-45 §8) is the minimum-viable instrument validation:**

> H1: A 6-item AA pilot instrument (3 reverse-coded), administered to N=15 of Brandon's network contacts, shows Cronbach's α ≥ 0.6 (acceptable internal consistency for a pilot) AND total-AA-score correlates r ≥ 0.4 with a single-item criterion.
>
> Kill: α < 0.5 OR criterion-r < 0.2.

If T45-8 KILLS, AA is operationally un-measurable — a definition with no instrumentation possible at this scale. That doesn't retract the theoretical paper but flags it as a non-empirical contribution until a stronger instrument is designed.

If T45-8 CONFIRMS, AA becomes the corpus's first **measurable** truth-axis (PD has never been operationalized as a self-report instrument; MR Truth Labels are propositional-classification, not person-level; τ/δ is an analyst-applied frame).

---

## §3 — Draft instrument (6 items, 3 reverse-coded)

Each item rated **1 (Strongly Disagree) → 7 (Strongly Agree)**. Items marked (R) are reverse-coded before summing.

### Self-Authority sub-scale (3 items)

1. **AA-S1.** "When I form a working position on a contested topic, I act on it confidently while remaining open that I might be wrong."
2. **AA-S2.** "I treat my own current understanding as a load-bearing foundation for further work, not as a tentative guess." *(higher = more AA-self granted)*
3. **AA-S3 (R).** "I withhold acting on my views until I am certain they are correct." *(reverse-coded: high score = low AA-self)*

### Other-Authority sub-scale (3 items)

4. **AA-O1.** "I build on what experts in a field tell me, while keeping a private reservation that they could be wrong on specifics."
5. **AA-O2 (R).** "I generally treat established expert claims as provisional and require independent verification before relying on them." *(reverse-coded: high score = low AA-other)*
6. **AA-O3 (R).** "When a respected source contradicts my own working position, I update entirely toward the source." *(reverse-coded: high score = epistemic deference > calibrated AA-other)*

### Criterion item (separate, used for criterion validity correlation)

C1. "How much do you defer to authoritative sources when forming opinions on contested topics?" 1 (Almost never) — 7 (Almost always)

### Composite scoring

`AA_total = AA_S1 + AA_S2 + (8 - AA_S3) + AA_O1 + (8 - AA_O2) + (8 - AA_O3)`
Range: 6 (low AA, dogmatic-self / dogmatic-other) → 42 (high AA, calibrated-with-doubt-reservation on both sub-axes).

Sub-scale scores (separately analyzable):
`AA_self = AA_S1 + AA_S2 + (8 - AA_S3)` (range 3-21)
`AA_other = AA_O1 + (8 - AA_O2) + (8 - AA_O3)` (range 3-21)

---

## §4 — Recruitment + administration

### §4.1 — Recruitment target

**N = 15** Brandon's network contacts. Acceptable diversity: mix of Retreat/MIU peers, family, professional contacts. No identifying data collected; first-name-or-pseudonym only. Ethics: pilot study, low-risk, no IRB needed for N=15 personal-network anonymous instrument validation.

### §4.2 — Administration

- **Format:** Google Form (free) with 7 items (6 AA + 1 criterion) + 2 demographic questions (age range, primary domain).
- **Time:** ~3 minutes per respondent.
- **Pre-text:** "This is a pilot validation of a brief 7-question instrument from an ongoing research project. There are no right answers; please respond on your honest first read of each statement. Anonymous; takes ~3 minutes."

### §4.3 — Pass-45 §11 anti-cheat

- Item wording, scoring formula, and criterion item frozen at this commit (SHA256 of this paper logged in Pass-48 results).
- Hypothesis pre-reg (per Pass-45 §8): α ≥ 0.6 AND criterion-r ≥ 0.4 → CONFIRM. α < 0.5 OR criterion-r < 0.2 → KILL. Anything else → INDETERMINATE.
- Brandon must NOT see individual responses before complete N=15 collection. Analysis only after N=15 is in.

---

## §5 — Analysis recipe (agent-side once data arrives)

```python
import numpy as np, pandas as pd
df = pd.read_csv("aa_pilot_responses.csv")  # rows = respondents, cols = AA_S1..O3 + C1
items = ["AA_S1", "AA_S2", "AA_S3_R", "AA_O1", "AA_O2_R", "AA_O3_R"]
# reverse-code
for c in ["AA_S3", "AA_O2", "AA_O3"]:
    df[c + "_R"] = 8 - df[c]
df["AA_total"] = df[items].sum(axis=1)
# Cronbach's alpha
def cronbach(x):
    k = x.shape[1]
    return (k / (k - 1)) * (1 - x.var(axis=0, ddof=1).sum() / x.sum(axis=1).var(ddof=1))
alpha = cronbach(df[items])
crit_r = np.corrcoef(df["AA_total"], df["C1"])[0, 1]
print(f"alpha = {alpha:.3f}, criterion-r = {crit_r:.3f}, N = {len(df)}")
verdict = "CONFIRM" if alpha >= 0.6 and crit_r >= 0.4 else \
          "KILL"    if alpha < 0.5 or crit_r < 0.2 else "INDETERMINATE"
print(f"verdict: {verdict}")
```

---

## §6 — What CONFIRM/KILL would mean

**If CONFIRM (α ≥ 0.6 AND r ≥ 0.4):**
- AA is the first **measurable** TI Sigma truth-axis at the person-level.
- Opens follow-up studies: AA-self correlates with what biographical / outcome variables? Does AA-other vary by domain (people grant high AA-other to medical experts but low AA-other to economists)?
- p47-AA-FOLLOWUP: a Pass-48+ Brandon-side N=50-100 follow-up to estimate stable population norms.

**If KILL (α < 0.5 OR r < 0.2):**
- The 6-item instrument as drafted is not measuring a coherent construct OR the construct is real but multi-dimensional and a 6-item scale cannot capture it.
- Two diagnostic next-steps: (a) inspect inter-item correlation matrix to see whether the AA-self and AA-other sub-scales hold internally even if the composite fails; (b) consider a 12-item v2 with more items per sub-scale.
- Theoretical paper (`AUTHORITY_AXIS_AA_2026-05-07.md`) is **not retracted** by KILL — it remains a coherent definition; only the *measurability* claim is downgraded.

**If INDETERMINATE (α between 0.5 and 0.6, or r between 0.2 and 0.4):**
- N = 15 is small. Underpowered. Recommend N=30 follow-up with same instrument before deciding.

---

## §7 — Cost + timeline

- **Cost:** $0 (Google Forms free; analysis agent-side).
- **Brandon time:** ~30 min (Form setup) + ~2 weeks recruitment + ~30 min reminder/follow-up.
- **Agent time:** ~30 min analysis once N=15 collected.
- **Total elapsed:** 2-4 weeks depending on recruitment speed.

---

## §8 — Recommended next-action for Brandon

1. Read this doc + skim §3 (the 6 items).
2. If items feel right as written, click "create Form" and copy-paste from §3.
3. If items feel off, redline them — but redline NOW before any responses, not after seeing data (anti-HARK).
4. Send to ~25 contacts to land N=15 responses (typical 60% response rate).
5. Ping agent when N=15 in hand. Agent runs §5 analysis script in <30 min.
