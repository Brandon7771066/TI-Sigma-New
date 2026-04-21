# Ugly-Truth Counterexamples Registry — Beauty Razor Failure-Mode Tracking

**Maintainer:** Brandon Charles Emerick
**Opened:** April 21, 2026
**Purpose:** Track apparent counterexamples to the Beauty Razor (URB #781 §B) so the Razor's failure modes are auditable, in the same disciplined pattern as URB #401's "what null looks like" approach.
**Status:** Living document. New entries appended as encountered.

---

## Why This Registry Exists

The Beauty Razor (BR) claims that, *ceteris paribus*, the more aesthetically pleasing depiction of a BT is the truer one. URB #781 §B.7 commits to a falsifiable prediction (P781) that blinded beauty ratings track later vindication at ≥ 2σ above chance. A responsible empirical program for BR must therefore maintain a registry of cases that *appear* to violate the Razor — both to surface genuine failures and to clarify the scope of the *ceteris paribus* clause when an apparent counterexample turns out to be a misapplication.

Two categories of apparent counterexample are tracked separately:

- **Type-1 (Ugly-True / Beautiful-False):** A relatively ugly explanation turned out true, *or* a relatively beautiful explanation turned out false, in a contest where BR would have selected the wrong side.
- **Type-2 (Scope misapplication):** An apparent failure that on closer inspection violates the *ceteris paribus* clause — one of the non-aesthetic GILE dimensions was not actually tied, so BR was never properly applicable.

A genuine refutation of BR requires accumulating Type-1 entries faster than chance would predict given the panel size and the threshold in P781. Type-2 entries clarify the Razor's scope without challenging it.

### Amendment (URB #784, April 21, 2026) — Type-3 Inversion-Cell Predictions

URB #784 establishes that the Beauty Razor is ρ-gated and *inverts* in the cell ρ ≤ ET ∧ PD < 0 (Beauty Razor Inversion Theorem). Apparent counterexamples falling in this cell are now **predicted** rather than refuting; they are reclassified as:

- **Type-3 (Inversion-cell prediction):** An apparent BR violation in which the BT under depiction has ρ(X) ≤ ET (Emerick Threshold, ≈ 0.4142) and an independently scored negative PD. In this cell URB #784 *predicts* that the uglier depiction is the truer one, so an observation of "ugly truth beating beautiful falsehood" *confirms* the Razor's URB #784 amendment rather than refuting it.

Registry intake protocol from this date forward: each candidate Type-1 entry is first ρ-classified using the procedure in URB #784 §3 and `gile_hem_pd_predictions.py`. If the entry lands in (ρ_low, PD−), it is re-coded as Type-3. P784.4 predicts that ≥ 60% of historical Type-1 entries reclassify as Type-3 once ρ-coded.

The five existing initial entries (UTC-2026-04-21-001 through 005) will be ρ-audited in a follow-up pass; preliminary inspection suggests all five are either Type-2 (scope misapplications, already so coded) or Type-3 cases — none are surviving Type-1 candidates.

---

## Registry Schema

Each entry uses the following fields:

| Field | Description |
|---|---|
| **ID** | UTC-yyyy-mm-dd-NNN |
| **Type** | 1 (genuine candidate) or 2 (scope misapplication) |
| **BT / Question** | The Being-Thing or question being depicted |
| **Beautiful candidate** | The depiction BR would prefer |
| **Ugly candidate** | The competing depiction |
| **Vindicated** | Which candidate was later vindicated (or "undecided") |
| **GILE-tie status** | Were all non-aesthetic GILE dimensions actually tied? (Y/N/partial) |
| **Razor verdict** | "Counterexample" / "Confirmation" / "Inapplicable" |
| **Notes** | One-paragraph diagnosis |

---

## Initial Entries (Historical, Pre-Registry)

These are added at registry opening based on prior knowledge, not new discovery. They calibrate the registry's baseline.

### UTC-2026-04-21-001 — Ptolemaic vs. Copernican astronomy (geocentric vs. heliocentric)

| Field | Value |
|---|---|
| Type | 2 (scope misapplication on first glance; confirmation under correct application) |
| BT / Question | The structure of the solar system |
| Beautiful candidate | Heliocentric (simpler orbits, single center, fewer epicycles) |
| Ugly candidate | Ptolemaic (epicycles on epicycles by Copernicus's era) |
| Vindicated | Heliocentric (with Keplerian elliptical refinement) |
| GILE-tie status | Y at the time of Copernicus's *De Revolutionibus* — both fit observation roughly equally; Copernican was more aesthetically unified |
| Razor verdict | **Confirmation** |
| Notes | Often cited as the canonical case where scientists "preferred beauty" before empirical resolution. Kuhn's *Copernican Revolution* makes this explicit. BR selected correctly. |

### UTC-2026-04-21-002 — Bohr atom (1913) vs. Sommerfeld–Wilson (1916)

| Field | Value |
|---|---|
| Type | 1 candidate; 2 on diagnosis |
| BT / Question | Atomic structure prior to quantum mechanics |
| Beautiful candidate | Bohr's circular orbits — visually clean, integer quantum numbers |
| Ugly candidate | Sommerfeld's elliptical orbits with relativistic corrections — fit fine structure better |
| Vindicated | Sommerfeld's extension was empirically superior; both were superseded by Schrödinger 1926 |
| GILE-tie status | N — Sommerfeld had genuinely better fit to fine-structure data |
| Razor verdict | **Inapplicable** (scope misapplication: empirical adequacy was not tied) |
| Notes | The case is sometimes cited as "beauty led astray" but the *ceteris paribus* clause was violated — Bohr's model lost on Environment-dimension fit, so BR was never the operative criterion. |

### UTC-2026-04-21-003 — Einstein's 1905 SR vs. Lorentz–Poincaré ether-frame formulation

| Field | Value |
|---|---|
| Type | 2 (confirmation under correct application) |
| BT / Question | Relativistic kinematics |
| Beautiful candidate | Einstein 1905 — derived from two postulates, no ether |
| Ugly candidate | Lorentz–Poincaré — same equations, retained ether as theoretical posit |
| Vindicated | Einstein (no ether detected; framework absorbed by GR by 1915) |
| GILE-tie status | Y for empirical predictions (the equations were identical); divergence was on the Existence-axis ontological commitment |
| Razor verdict | **Confirmation** |
| Notes | The two formulations made identical predictions for all 1905-era experiments. BR (or its Einsteinian "inner perfection" predecessor) selected correctly on the only available criterion. |

### UTC-2026-04-21-004 — Steady-state cosmology (Hoyle, Bondi, Gold) vs. Big Bang

| Field | Value |
|---|---|
| Type | 1 candidate |
| BT / Question | Origin and evolution of the universe |
| Beautiful candidate | Steady-state — perfect cosmological principle, eternal, no special initial moment |
| Ugly candidate | Big Bang — special singular moment, asymmetric in time |
| Vindicated | Big Bang (CMB discovery 1964 was decisive) |
| GILE-tie status | Y until ~1964 — both fit observation roughly equally before CMB |
| Razor verdict | **Counterexample (genuine, pre-1964)** |
| Notes | This is the strongest historical Type-1 entry. From the late 1940s through the early 1960s, BR would have selected steady-state, and steady-state was wrong. After 1964 the GILE-tie was broken on Environment-dimension fit and BR became inapplicable. **Lesson:** BR is a tie-breaker among genuinely tied candidates; the "tie" must be assessed at the time of the choice, not retrospectively. |

### UTC-2026-04-21-005 — Supersymmetry (SUSY) vs. Standard Model alone

| Field | Value |
|---|---|
| Type | 1 candidate (provisional — partially undecided) |
| BT / Question | Beyond-Standard-Model particle physics |
| Beautiful candidate | SUSY — doubles particle content but resolves hierarchy problem elegantly, predicts dark matter candidate, unifies couplings |
| Ugly candidate | SM-only — fewer postulates, no naturalness solution |
| Vindicated | LHC has not detected SUSY at predicted scales as of 2026; SUSY in original form is increasingly disfavored |
| GILE-tie status | Was Y in 1990s–2000s; broken on Environment-dimension by null LHC results |
| Razor verdict | **Counterexample (provisional, scope-clarifying)** |
| Notes | Most-cited contemporary case where physicists "preferred beauty" and beauty appears to have misled. Important caveat: the original SUSY parameter space is excluded but extended SUSY variants remain live. The honest entry: at the 1990s tie point, BR selected SUSY; subsequent LHC data has weakened that selection. Watch this entry — may need updating. |

---

## Aggregate Counts (as of 2026-04-21)

| Verdict | Count |
|---|---|
| Confirmation | 2 |
| Counterexample (genuine) | 1 (steady-state, pre-1964) |
| Counterexample (provisional) | 1 (SUSY) |
| Inapplicable / scope-misapplication | 1 (Bohr–Sommerfeld) |
| **Net Type-1 against BR** | **1 confirmed + 1 provisional out of 5 entries** |

This is too small a sample to evaluate P781. The registry exists to grow.

---

## Lessons Already Visible

1. **The "tie" must be assessed at the time of choice, not retrospectively.** Steady-state vs. Big Bang in 1955 was a genuine tie; in 1965 it was not. BR's correctness depends on the temporal indexing of the GILE-parity assessment. This is consistent with URB #772 clause 6 ("at the present moment") — BR inherits the same temporal-now anchoring.

2. **Most apparent BR failures dissolve into scope misapplication.** Of five entries, three are Type-2 (scope) and two are Type-1 (genuine). The Razor is more robust than its critics typically suppose, but the *ceteris paribus* clause has to be checked rigorously each time.

3. **Provisional Type-1 entries should be reviewed annually.** SUSY's verdict could shift if extended-SUSY variants are confirmed at higher energies. The registry is not a verdict ledger but a living audit.

---

## Appending New Entries

Add new entries chronologically. When a Type-1 (provisional) entry's status changes, add a new dated entry rather than overwriting — preserve the trajectory.

A formal review of the registry is recommended every six months. If the genuine Type-1 count exceeds chance expectation under P781's panel size and threshold, BR's empirical status should be downgraded from "ceteris paribus tie-breaker" to "heuristic without empirical truth-tracking warrant."

---

*Registry opened by Brandon Charles Emerick, April 21, 2026, in conjunction with URB #781. Maintainer commits to honest recording of all candidate counterexamples, including those that would refute BR.*
