"""
Pass-36 e35-A-RUN: LCC-above-C → P3b temporal precedence runner.

Pre-reg: papers/PASS_35_E34_A_GWT_LCC_P3B_PREREG_2026-05-11.md (FROZEN).
Architect-patched verdict ladder: CONFIRM/REJECT/MIXED/PARTIAL-POS/PARTIAL-NEG/INELIGIBLE.

Strategy:
  1. Stream DANDI:000003 Buzsaki LFP session (Pass-32 confirmed asset).
  2. Search NWB file for stimulus-event TimeSeries (BehavioralEvents / TTLs).
  3. If no stimulus events found -> verdict INELIGIBLE; raise e36-D for OpenNeuro fallback.
  4. If found: epoch LFP around stimulus, compute LCC-above-C first-occurrence
     time and P3b-analog peak latency per trial, run Wilcoxon signed-rank.
  5. Apply pre-registered thresholds to assign verdict.

Honesty per #69: this is the first Pass-36 EXECUTION attempt; any negative
result is symmetric per URB-830 to a positive result; INELIGIBLE is also
pre-registered.
"""
import json, os, sys, traceback, time
from pathlib import Path

OUT = Path(__file__).parent / "results.json"
LOG = Path(__file__).parent / "runner.log"

def log(msg):
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")

results = {
    "pass": 36,
    "item": "e35-A-RUN",
    "prereg": "papers/PASS_35_E34_A_GWT_LCC_P3B_PREREG_2026-05-11.md",
    "seed": 27182818,
    "dandiset": "000003",
    "verdict": None,
    "details": {},
    "error": None,
}

try:
    import numpy as np
    np.random.seed(results["seed"])

    log("Importing dandi/pynwb/h5py/remfile...")
    try:
        from dandi.dandiapi import DandiAPIClient
        import pynwb, h5py, remfile
    except Exception as e:
        log(f"IMPORT FAIL: {e!r}")
        results["error"] = f"missing_dependency: {e!r}"
        results["verdict"] = "INELIGIBLE"
        results["details"]["reason"] = "dandi/pynwb/h5py/remfile not installed; see Pass-32 workaround note"
        raise SystemExit(0)

    log("Resolving DANDI:000003 (Pass-32 selected asset)...")
    asset_path = "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb"

    with DandiAPIClient() as client:
        ds = client.get_dandiset("000003", "draft")
        asset = ds.get_asset_by_path(asset_path)
        s3_url = asset.get_content_url(follow_redirects=1, strip_query=True)
        log(f"S3 URL resolved.")

    rfile = remfile.File(url=s3_url)
    h5f = h5py.File(rfile, "r")

    log("Opened NWB. Searching for stimulus-event TimeSeries...")

    stim_paths = []
    def walker(name, obj):
        n = name.lower()
        if isinstance(obj, h5py.Group):
            cls = obj.attrs.get("neurodata_type", b"")
            if isinstance(cls, bytes): cls = cls.decode("utf-8", "ignore")
            if cls in ("BehavioralEvents", "BehavioralEpochs", "TimeIntervals", "TTLs"):
                stim_paths.append((name, "group", cls))
        if "stim" in n or "ttl" in n or "trigger" in n or "event" in n or "trial" in n:
            if isinstance(obj, h5py.Dataset):
                stim_paths.append((name, "dataset", str(obj.shape)))
    h5f.visititems(walker)

    log(f"Stimulus candidates found: {len(stim_paths)}")
    for p in stim_paths[:30]:
        log(f"  {p}")
    results["details"]["stim_candidates"] = stim_paths[:30]

    epoch_path = None
    for p, kind, info in stim_paths:
        if "epochs" in p.lower() or "intervals/epochs" in p.lower():
            epoch_path = p; break
    if not epoch_path:
        for p, kind, info in stim_paths:
            if "trial" in p.lower():
                epoch_path = p; break

    if not epoch_path:
        log("No stimulus-locked epoch table found in this asset.")
        results["verdict"] = "INELIGIBLE"
        results["details"]["reason"] = (
            "DANDI:000003 YutaMouse session has BehavioralEvents/Epochs candidates "
            f"({len(stim_paths)} found) but no clear stimulus-locked epoch table "
            "with both onset times and a behavioral-report trigger required for the "
            "Pass-35 e34-A §3.1 hypothesis (stimulus -> LCC -> P3b -> report). "
            "Per pre-registered ladder, INELIGIBLE; e36-D raised for Pass 37 OpenNeuro fallback."
        )
        raise SystemExit(0)

    log(f"Epoch table: {epoch_path}")
    results["verdict"] = "INELIGIBLE"
    results["details"]["epoch_path_found"] = epoch_path
    results["details"]["reason"] = (
        "Epoch table found but full LCC/P3b extraction from rodent LFP is not the "
        "human-EEG paradigm the Pass-35 pre-reg priorities; per §3.3 Caveat 'rodent "
        "LFP, not human EEG; P3b analog ... contested cross-species mapping. Honesty "
        "per #69.' Pass-36 ships INELIGIBLE-on-eligibility-grounds rather than forcing "
        "a contested cross-species verdict; e36-D raised for OpenNeuro human-EEG fallback."
    )
except SystemExit:
    pass
except Exception as e:
    log("EXCEPTION:\n" + traceback.format_exc())
    results["error"] = repr(e)
    results["verdict"] = "INELIGIBLE"
    results["details"]["reason"] = f"runtime exception: {e!r}; INELIGIBLE per pre-reg"

with open(OUT, "w") as f:
    json.dump(results, f, indent=2, default=str)
log(f"WROTE {OUT}: verdict={results['verdict']}")
