# Biowell Rescreen — Pre-Brief Before Booking

**Date:** 2026-05-01
**Audience:** Brandon
**Standard:** asymmetric-standards #69 + budget constraint <$50
**Decision pending:** whether to book a second Biowell screening, when, and what to do differently this time so it's not a duplicate of Nov 25 2025.

---

## 1. What we already have from the Nov 25 2025 screening

**Files in repo:** two CSV uploads + two PDFs in `attached_assets/`. Both CSVs are byte-identical (md5 `fe8497a1...`); both PDFs are byte-identical too. So we have **one** Biowell session, not two. (You may have re-uploaded the same export twice.)

**Headline numbers from that session (2025-11-25 11:30):**

| Metric | Value | Note |
|---|---|---|
| Stress | 6.68 | Biowell's 0–10 scale; mid-range |
| Energy | 22.98 | Biowell's "JS" energy units |
| Organs disbalance, % | **−39.11** | Negative = right-side-dominant disbalance |
| Balance left | 40.63 | Out of 100 |
| Balance right | **90.63** | Out of 100 — large L/R asymmetry |
| Left disbalance organ count | **19** | High |
| Right disbalance organ count | 3 | Low |
| EC (Emotional Coefficient) | 1.75 | Reference normal ≈ 2.0–4.0 |
| FC (Functional Coefficient) | 2.89 | Reference normal ≈ 2.0–4.0 |
| Overall alignment | 91.67 | High |

**Per-chakra (Biowell calls them "nervous system centers") energy:**
- Center 4 (heart): 3.22 (highest)
- Center 5: 2.71
- Center 1: 2.69, Center 3: 2.67, Center 2: 2.66
- Center 6: 2.05
- Center 7: 1.88 (lowest — crown)

**Yin/Yang split:** 42.41 / 57.59 (Yang-dominant)

**Notable per-organ energy outliers:**
- High: Sacrum (4.41), Respiratory system (4.10), Liver (3.48), Yin of Liver (3.48), Yin of Kidneys (3.17), Coccyx/Pelvis (3.58), Throat (3.21)
- Low: Thorax zone (0.86), Cerebral vessels (1.32), Pancreas (1.43), Pituitary (1.48), Heart organ-level (1.64)

**Lifestyle scores:** Environment 91, Hormonal activity 82, Physical activity 64, Nutrition 36, Psychology 36, Regime of the day 35.

That last row is a real flag. Three of the six lifestyle dimensions Biowell measures came in at ≤36. Worth seeing whether those have shifted in 5+ months.

---

## 2. Why a second screening would be informative right now

**Five things have changed since Nov 25 2025:**

1. **You finished a 3-week Focalin 30 mg IR run.** Methylphenidate has measurable effects on autonomic tone — Biowell would likely show shifts in EC/FC and stress score from a baseline taken on it.
2. **You're now 10 days into Focalin withdrawal + Day 1 of Adderall 40 mg IR.** Capturing a Biowell *during* this transition is a one-time-only data point.
3. **URB #826 Phase H-1 ran twice (§8.6, §8.7).** Architectural validation only — no biological claim — but if you want to look for any post-protocol shift in chakra/meridian readings, this is the only chance.
4. **Polar H10 / Phase B / §10.6 collection window just started.** A Biowell at the start gives us a "T=0" snapshot to compare against a Biowell at T=21 days.
5. **The Nov 25 reading flagged Nutrition 36, Psychology 36, Regime of the day 35.** If any of those have changed, a rescreen documents it.

**One thing that has NOT changed and won't be informative:** your DNA. The genome-derived components (mito_snp 0.9468, telomere_proxy 0.4167, cpg 0.4757) are time-constant. A Biowell can't measure DNA.

---

## 3. Honest accuracy expectations for Biowell (asymmetric-standards #69)

Biowell is a **GDV (gas-discharge visualization) device** — it measures the corona discharge from your fingertips under a high-voltage electrical field and back-projects that into a chakra/meridian/organ map using proprietary algorithms.

**What Biowell can honestly claim to measure:**
- Skin electrical conductance and emission patterns (real, reproducible).
- Autonomic state proxies (real, somewhat noisy).
- Hydration-sensitive biomarkers (real but very confounded by fingertip moisture).

**What Biowell's UI presents but cannot honestly measure:**
- Chakra energies (no double-blind validation that fingertip GDV correlates with what traditional chakra theory describes; the mapping is an algorithmic choice).
- Per-organ energies (the spatial back-projection from fingertips to internal organs has no peer-reviewed neuroanatomical justification).
- Yin/Yang balance (TCM mapping is interpretive).
- Lifestyle dimensions (back-derived from the same fingertip data; circular).

**My honest recommendation for how to use a rescreen:**
- Treat the **stress, energy, EC, FC, balance L/R, and per-chakra energy raw numbers** as autonomic state proxies. Compare them against the Nov 25 baseline.
- Do NOT use Biowell as a Phase B feature for URB #826 or §10.6 — its data is too low-frequency (one snapshot) and too confounded by hydration/skin-state to enter the regression.
- Do use it as a one-shot **biographical marker** for the med transition: "before Focalin / on Focalin / Adderall transition."

---

## 4. Cost + scheduling

I don't know your local Biowell provider's price. From public US listings the typical session is **$60–$150**, which violates the <$50 budget cap as a single line item.

**Three honest options:**

| Option | Cost | When | Verdict |
|---|---|---|---|
| **A. Book a screening this month** | $60–$150 | While Adderall titration is fresh | **Out of budget** unless you have a provider in mind under $50 |
| **B. Wait until after the §10.6 H10 window completes** (≈2026-05-22) | $60–$150 | T+21 of Adderall | Same budget problem; better data |
| **C. Skip the rescreen; use the Nov 25 data as the only Biowell baseline** | $0 | n/a | The asymmetric-standards default if there's no provider under $50 |

**My recommendation:** Option B if and only if you can find a provider charging ≤$50, otherwise Option C. The data value of a rescreen is real but not large enough to break the budget for. We have the Nov 25 baseline already; the H10 + Oura + subjective log will carry the within-window biology.

---

## 5. If we DO book a rescreen — what to capture differently this time

**Minimum capture protocol (15 min on the day):**
- Same time of day as Nov 25 (11:30 AM) to control for circadian
- Same hydration state (note water intake in last 2 hours)
- Note in `data/medication_log.csv` the exact time of last Adderall dose vs the Biowell session
- Add a row to `data/subjective_daily_log.csv` immediately before AND immediately after the screening
- Get BOTH CSV exports (the per-finger raw + the summary) AND the PDF
- Drop the new files in `data/biowell/<date>/` (folder doesn't exist yet — I'll create it on first use)

**Statistical asks:**
- We have N=1 baseline. A second reading gives N=2 — still not enough to claim "improvement" or "deterioration" with any confidence. Don't let any provider tell you a 2-point delta is meaningful.
- Honest delta interpretation: only flag deltas > ~30% on any single metric as worth investigating. Smaller shifts are within Biowell's day-to-day measurement noise.

---

## 6. Concrete pending decisions for you

1. **Do you have a Biowell provider under $50?** If yes → book Option B for ~T+21. If no → Option C, archive Nov 25 as the sole baseline.
2. **Want me to set up `data/biowell/` folder + a `biowell_csv_loader.py` that diffs a new screening against the Nov 25 baseline automatically?** I can do this for $0 right now, takes ~10 min. It only becomes useful if you actually book Option A or B.
3. **Want me to add chakra-energy fields to `data/subjective_daily_log.csv`** so daily subjective notes can include a self-reported "where do I feel energy today" reading? Useful complement to a rescreen, also $0.

Defer #2 and #3 until you've answered #1 — no point building infrastructure for data we may not collect.
