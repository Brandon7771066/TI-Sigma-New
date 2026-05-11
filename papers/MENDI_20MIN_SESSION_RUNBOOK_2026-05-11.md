# Mendi 20-Minute Structured Session — Acer Laptop Runbook

**Date:** 2026-05-11
**Target hardware:** Acer laptop (Windows), Mendi headband (MAC `F8:1C:96:82:73:AD`)
**Builds on:** `papers/MENDI_PATH_B_PHASE_2_COMPLETE_2026-05-06.md` (decoder shipped) + `mendi_ble_client.py` (live STREAM_CHAR_UUID)
**New artifacts:**
- `mendi_session_20min.py` — Python session orchestrator
- `mendi_session_20min.bat` — Windows one-click launcher

---

## §1 — Why this session exists

Path B Phase 2 (2026-05-06) shipped the bb4 protobuf decoder but the 10-min meditation capture had **only ~40% effective streaming** (two 156-s contact-loss gaps) and **no known-stimulus events** to verify the 12-bit-ADC NIR-intensity hypothesis. This 20-min session adds:

1. **4 known stimulus events** (2× mental arithmetic, 2× breath-hold), each preceded by ≥60 s baseline and followed by ≥120 s recovery → enables paired-comparison hemodynamic-response detection.
2. **Live dropout warning** in the script (warns if no frame for >5 s) so you can re-seat the headband mid-session if needed.
3. **Per-phase summary stats** auto-computed at session end (mean/min/max/stdev per phase + stimulus minus baseline deltas).
4. **Replicated stimulus design** — each stimulus type fires twice so the second occurrence is a within-session replication of the first.

## §2 — Pre-flight (do this ONCE on your Acer)

Open a Windows Command Prompt and check Python is installed:

```
py --version
```

Should print `Python 3.10` or later. If not, install Python from https://python.org (check "Add to PATH" during install).

Install the BLE library:

```
py -m pip install bleak requests
```

Make sure the Mendi is **NOT paired** in Windows Bluetooth settings (Settings → Bluetooth & devices → if Mendi appears, click ⋯ → Remove device). The library opens its own connection and pairing interferes.

Sanity check — confirm the script files are in your project folder:

```
cd \path\to\your\workspace\copy
dir mendi_session_20min.*
```

You should see `mendi_session_20min.py` and `mendi_session_20min.bat`.

## §3 — Running the session

**Easy mode (recommended):** double-click `mendi_session_20min.bat` from File Explorer, OR run from cmd:

```
mendi_session_20min.bat
```

This auto-checks bleak, prints the pre-flight checklist, waits for you to confirm, then launches the session.

**Manual mode:** if you want to override MAC or duration:

```
py mendi_session_20min.py --address F8:1C:96:82:73:AD --duration 1200 --label morning1
```

Options:
- `--address <MAC>` — override Mendi MAC if yours differs
- `--duration <seconds>` — default 1200 (20 min); use a smaller value for a quick test (e.g. `--duration 180` for a 3-min sanity test of the BLE path before the full session)
- `--label <name>` — file naming tag (e.g. `morning1`, `evening`, `caffeine-test`)
- `--no-prompts` — silent run (no on-screen stimulus prompts; useful if you have a phone timer)

## §4 — What the script does during the session

Every 10 seconds the script prints a live status line:
```
  t=03:20  phase=RECOVERY1            n_samp_10s= 14  mean= 3825.4  min=3822  max=3829
```
Meanings:
- **t=MM:SS** — elapsed session time
- **phase=** — current protocol phase (one of `BASELINE`, `STIM1_ARITHMETIC`, `RECOVERY1`, `STIM2_BREATHHOLD`, `RECOVERY2`, `STIM3_ARITHMETIC`, `RECOVERY3`, `STIM4_BREATHHOLD`, `CLOSING_MEDITATION`)
- **n_samp_10s** — frames received in the last 10 s (Mendi streams ~14 Hz; should be 12-15 if contact is good)
- **mean / min / max** — raw bb4 ADC values in last 10 s (typical baseline = 3820–3832 per Pass-2 capture)
- **⚠ DROPOUT Ns** — appears if no frame for >5 s; re-seat headband

When a stimulus phase fires, the script prints a banner:
```
────────────────────────────────────────────────────────────
  [t=02:00]  STIM1_ARITHMETIC
  → STIMULUS 1 — Count backwards from 1000 by 7s OUT LOUD for 60 seconds. Begin NOW.
────────────────────────────────────────────────────────────
```

**Just follow the banner.** No phone, no timer needed.

## §5 — The 20-minute protocol

| Time | Phase | What you do |
|---|---|---|
| 0:00–2:00 | BASELINE | Sit comfortably, eyes soft-focus, breathe normally. **Do not move.** |
| 2:00–3:00 | STIM1_ARITHMETIC | Count backwards from 1000 by 7s **out loud** (1000, 993, 986, ...) for 60 s. |
| 3:00–5:00 | RECOVERY1 | Stop counting, breathe normally, relax. |
| 5:00–6:00 | STIM2_BREATHHOLD | Exhale fully, hold 30–45 s, resume normal breathing. |
| 6:00–10:00 | RECOVERY2 | Eyes closed, meditation posture, breath natural. |
| 10:00–11:00 | STIM3_ARITHMETIC | Count backwards from 999 by 13s **out loud** for 60 s (replication). |
| 11:00–13:00 | RECOVERY3 | Relax. |
| 13:00–14:00 | STIM4_BREATHHOLD | Exhale fully, hold 30–45 s, resume (replication). |
| 14:00–20:00 | CLOSING_MEDITATION | Eyes closed, breath natural, no task. |
| 20:00 | SESSION_END | Done — script saves files and exits. |

## §6 — Output files (saved to `data/mendi/sessions/`)

Filenames are tagged with your `--label` and a timestamp like `2026-05-11T14-30-00`:

| File | Format | Use |
|---|---|---|
| `<label>_<ts>_raw.jsonl` | JSON-lines (one frame/line) | Audit trail — original hex bytes for re-decode if needed |
| `<label>_<ts>_decoded.csv` | CSV with header `t_elapsed_s, wallclock, raw_value, norm_intensity, phase` | Open in Excel / pandas / R for analysis |
| `<label>_<ts>_events.json` | JSON | Schedule + actual stimulus-onset wallclocks for time-locked analysis |
| `<label>_<ts>_summary.txt` | Plain text | Per-phase stats + stimulus deltas printed automatically |

The summary file is also printed to your terminal when the session ends, so you can see immediately whether anything interesting happened.

## §7 — How to read the auto-summary

Example:
```
Per-phase stats (raw bb4 ADC values; lower = more absorption):
phase                      n     mean   min   max   stdev
------------------------------------------------------------
BASELINE                  168   3825.32  3820  3832   2.36
STIM1_ARITHMETIC           84   3811.05  3804  3821   3.40
RECOVERY1                 168   3823.91  3819  3830   2.50
...

Stimulus deltas (mean during stim − mean during preceding recovery/baseline):
  STIM1_ARITHMETIC     − BASELINE     =  -14.27 ADC units (n_stim=84, n_base=168)
  STIM2_BREATHHOLD     − RECOVERY1    =   +8.41 ADC units (n_stim=72, n_base=168)
  ...
```

Per Pass-2 audit:
- **|delta| < 3 ADC units** = below noise floor → no signal detected
- **|delta| ≈ 5–15 units** = candidate hemodynamic response (consistent with mild prefrontal activation)
- **|delta| ≈ 20–60 units** = strong response (consistent with significant blood-volume change)
- **negative delta during arithmetic** = lower NIR intensity = MORE absorption = MORE blood-volume in the optical path = consistent with prefrontal cortex activation
- **positive delta during breath-hold initial phase** = LESS absorption initially = LESS blood, then negative as CO₂ builds and hyperemia kicks in

If your STIM1 and STIM3 deltas are both negative AND of similar magnitude → strong replication of the cognitive-stimulus → hemodynamic-response link, validating the 12-bit-ADC NIR-intensity hypothesis.

## §8 — If something goes wrong

| Symptom | Fix |
|---|---|
| `bleak NOT installed` | `py -m pip install bleak requests` (or run as Administrator if pip fails) |
| `Connection failed` | Headband off → power on. Mendi paired in Windows → Remove. Phone app open → Close. Try again. |
| `⚠ NO SAMPLES last 10s` for >30 s | Re-seat the headband; the optode needs flush forehead contact. If persistent, restart the script (Ctrl+C → re-run). |
| Mean ADC value is ~0 or wildly different from 3820-ish | Headband isn't actually streaming the NIR optode — check `--address` MAC. Run `py mendi_ble_client.py --scan` to confirm the device. |
| Script hangs at "Connecting..." | Run cmd as Administrator (Windows BLE permissions). |
| Sample rate <5 Hz | Bluetooth interference (move away from Wi-Fi router). Or low Mendi battery (charge it). |

## §9 — After the session

1. **Open the CSV** (`data/mendi/sessions/<label>_<ts>_decoded.csv`) in Excel — make a quick line chart of `raw_value` vs `t_elapsed_s` colored by `phase`. The arithmetic and breath-hold phases should look visibly different from baseline if the device is detecting anything.
2. **Save the session** — copy the entire `data/mendi/sessions/<label>_<ts>_*` set to a dated folder if you want to archive multiple sessions for comparison.
3. **Compare across sessions** by running the script daily/weekly with different `--label` values; the per-phase stats are directly comparable.
4. **Hand off to analysis** — the CSV is the input for any future Pass-43+ stimulus-response analysis (paired t-test on stimulus vs baseline, time-locked averaging, etc.).

## §10 — Honesty caveats (#69)

- **Mendi has only 1–2 NIR wavelengths in a single optode** — cannot do true Beer-Lambert HbO₂/HbR separation per `papers/MENDI_FNIRS_AUDIT_2026-05-01.md`. The signal is a single mixed prefrontal-blood-volume proxy, NOT research-grade fNIRS oxygenation.
- **The 12-bit-ADC NIR-intensity interpretation is the strongest hypothesis** but unverified in absolute physical units. The stimulus deltas measured here are the verification path.
- **Single-session results are noisy** — replicate across 3–5 sessions before drawing any individual-level conclusion. The protocol is designed for repeated runs.
- **Streaming dropout is expected** — Pass-2 saw ~60% dropout on a 10-min meditation. The 20-min protocol has 4 stimulus events specifically to give multiple chances at clean stimulus-baseline pairs even if 1–2 are corrupted by dropout.
- **No claim is made that this validates URB #828 or any GILE-HEM hypothesis** — this is hardware-functionality validation only. Higher-order theoretical claims require the multi-session designs in the relevant URB papers.
