# Biowell GDV Screening Data

This folder holds Brandon's Biowell (GDV — gas-discharge visualization) screening exports.

## Structure

```
data/biowell/
├── README.md                    (this file)
├── 2025-11-25/                  (one folder per screening date, ISO format)
│   ├── biowell_summary.csv      (the main parameter export)
│   └── biowell_overall.pdf      (the printable PDF report)
└── 2026-MM-DD/                  (next screening goes here)
```

## Baseline screening (2025-11-25 11:30)

The original Nov 25 2025 baseline lives in `attached_assets/`:
- `attached_assets/BioWell_1764096972523.csv` (md5 `fe8497a1...`)
- `attached_assets/BioWell Overall_1764096972523.pdf`

Both files were uploaded twice (the `_1764097221968` variants are
byte-identical duplicates, confirmed via md5sum). Treat as N=1 baseline.

Headline values from that screening:

| Metric | Value |
|---|---|
| Stress | 6.68 |
| Energy | 22.98 |
| Organs disbalance, % | −39.11 (right-side dominant) |
| Balance left / right | 40.63 / 90.63 |
| EC / FC | 1.75 / 2.89 |
| Overall alignment | 91.67 |
| Yin / Yang | 42.41 / 57.59 |
| Lifestyle (flagged low) | Nutrition 36, Psychology 36, Regime 35 |
| Per-chakra energy peak | Center 4 (heart) = 3.22 |
| Per-chakra energy floor | Center 7 (crown) = 1.88 |

Full per-organ + per-meridian values are in the CSV.

## How to add a new screening

1. Create a date-named folder: `data/biowell/<YYYY-MM-DD>/`
2. Drop the CSV export there as `biowell_summary.csv`
3. Drop the PDF there as `biowell_overall.pdf`
4. Add a row to `data/medication_log.csv` for any meds taken before/during the session
5. Add a row to `data/subjective_daily_log.csv` for that date if not already present
6. Run `python biowell_csv_loader.py --diff <YYYY-MM-DD>` to see the delta vs Nov 25 baseline

## Capture protocol (for screenings going forward)

Per `papers/BIOWELL_RESCREEN_PRE_BRIEF_2026-05-01.md`:

- Same time of day as Nov 25 baseline (11:30 AM) for circadian control
- Note hydration state — water intake in last 2 hours
- Time of last Adderall dose vs the Biowell session goes in medication_log
- Add a subjective_daily_log row immediately before AND immediately after the screening
- Get BOTH the per-finger raw CSV and the summary CSV if the provider exports both

## What Biowell honestly measures

- Skin electrical conductance + corona discharge from fingertips under high-voltage field
- Autonomic state proxies (real but noisy)
- Hydration-sensitive biomarkers (real but very confounded by fingertip moisture)

## What Biowell's UI presents but cannot directly measure

- Chakra energies (algorithmic mapping; no double-blind validation)
- Per-organ energies (spatial back-projection lacks peer-reviewed neuroanatomical justification)
- Yin/Yang balance (TCM mapping is interpretive)
- Lifestyle dimensions (back-derived from same fingertip data; circular)

Use Biowell as a biographical autonomic-state marker. Do NOT use it as a
Phase B feature for URB #826 §10.6 — too low-frequency and too
hydration-confounded to enter the regression.

## Honest delta interpretation

We have N=1 baseline. A second reading gives N=2 — not enough to claim
"improvement" or "deterioration" with statistical confidence. Flag deltas
> ~30% on any single metric as worth investigating. Smaller shifts are
within Biowell's day-to-day measurement noise.
