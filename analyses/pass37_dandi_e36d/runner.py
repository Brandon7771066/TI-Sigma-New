"""
Pass-37 e36-D: 3-DANDIset eligibility scan for the LCC->P3b precedence
hypothesis (Pass-35 e34-A pre-reg).

Scans DANDI:000003 (Buzsaki LFP), 000053 (IBL Neuropixels mEC), 000114
(Mayo rodent ophys) for stimulus-event TimeSeries AND companion
behavioral-report triggers.

Per Pass-35 §3.1 hypothesis, eligibility requires BOTH:
  (a) stimulus-locked epochs with onset times
  (b) behavioral-report trigger (button-press, lick-port, vocalization,
      eye-blink) tied to the same stimulus events

Pre-reg (Pass-37, FROZEN here BEFORE execution):
  - INELIGIBLE_NO_STIM: no (a) -> raise OpenNeuro-fallback path.
  - INELIGIBLE_NO_REPORT: (a) found, no (b) -> SECONDARY-EVIDENCE-only path
    (cross-species sensitivity check, NOT primary test).
  - ELIGIBLE: both (a) and (b) -> proceed to Pass-38 LCC/P3b epoching.

Anti-HARK: this scan classifies eligibility ONLY; no LCC/P3b numbers
computed in this Pass.
"""
import json, os, sys, time, traceback
from pathlib import Path

OUT = Path(__file__).parent / "results.json"
LOG = Path(__file__).parent / "runner.log"

def log(m):
    line = f"[{time.strftime('%H:%M:%S')}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")

ASSETS = {
    "000003": "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb",
    "000053": "sub-npI1/sub-npI1_ses-20190413_behavior+ecephys.nwb",
    "000114": "sub-ROV45/sub-ROV45_ses-Day 1-obs_ophys.nwb",
}

REPORT_KEYWORDS = ("lick", "button", "press", "response", "report", "choice",
                   "vocaliz", "blink", "saccade", "wheel", "trial_outcome",
                   "behavior/states", "feedback", "reward")

def scan_one(client, dandiset_id, asset_path, h5py, remfile):
    info = {"dandiset": dandiset_id, "asset_path": asset_path, "verdict": None}
    try:
        ds = client.get_dandiset(dandiset_id, "draft")
        asset = ds.get_asset_by_path(asset_path)
        s3 = asset.get_content_url(follow_redirects=1, strip_query=True)
        info["s3_resolved"] = True
    except Exception as e:
        info["error"] = repr(e)
        info["verdict"] = "INELIGIBLE_S3_FAIL"
        return info

    try:
        rfile = remfile.File(url=s3)
        h5f = h5py.File(rfile, "r")
    except Exception as e:
        info["error"] = repr(e)
        info["verdict"] = "INELIGIBLE_OPEN_FAIL"
        return info

    stim_paths, report_paths = [], []

    def walker(name, obj):
        n = name.lower()
        is_stim = ("stimulus" in n or "stim" in n or "ttl" in n or "trigger" in n
                   or "pulsestim" in n or "/intervals/" in n or "trial" in n)
        is_report = any(kw in n for kw in REPORT_KEYWORDS)
        if isinstance(obj, type(h5f)) is False:
            try:
                cls = obj.attrs.get("neurodata_type", b"")
                if isinstance(cls, bytes):
                    cls = cls.decode("utf-8", "ignore")
            except Exception:
                cls = ""
            shape = getattr(obj, "shape", None)
            entry = (name, str(shape) if shape is not None else "group", cls)
            if is_stim:
                stim_paths.append(entry)
            if is_report:
                report_paths.append(entry)

    h5f.visititems(walker)
    info["stim_count"] = len(stim_paths)
    info["report_count"] = len(report_paths)
    info["stim_sample"] = stim_paths[:15]
    info["report_sample"] = report_paths[:15]

    if not stim_paths:
        info["verdict"] = "INELIGIBLE_NO_STIM"
        info["reason"] = ("No stimulus-event TimeSeries found in this asset; "
                         "OpenNeuro-fallback raised.")
    elif not report_paths:
        info["verdict"] = "INELIGIBLE_NO_REPORT"
        info["reason"] = (f"Found {len(stim_paths)} stimulus candidates but no "
                         "behavioral-report trigger keywords matched. Per Pass-35 "
                         "§3.1 pre-reg, eligibility requires BOTH stimulus AND "
                         "report. SECONDARY-EVIDENCE path only.")
    else:
        info["verdict"] = "ELIGIBLE_FOR_PASS_38_LCC_P3B"
        info["reason"] = (f"{len(stim_paths)} stim + {len(report_paths)} report "
                         "candidates found; Pass-38 LCC/P3b epoching can proceed.")

    try:
        h5f.close()
    except Exception:
        pass
    return info

def main():
    results = {
        "pass": 37, "item": "e36-D", "seed": 27182818,
        "prereg_locked": True,
        "scan_target": "stim + report co-occurrence per Pass-35 §3.1",
        "per_dandiset": {},
        "aggregate_verdict": None,
    }

    try:
        from dandi.dandiapi import DandiAPIClient
        import h5py, remfile
    except Exception as e:
        log(f"IMPORT FAIL: {e!r}")
        results["error"] = repr(e)
        results["aggregate_verdict"] = "INELIGIBLE_DEPS"
        with open(OUT, "w") as f:
            json.dump(results, f, indent=2, default=str)
        return

    with DandiAPIClient() as client:
        for ds, path in ASSETS.items():
            log(f">> Scanning DANDI:{ds} {path}")
            try:
                info = scan_one(client, ds, path, h5py, remfile)
            except Exception as e:
                log(f"   EXCEPTION on {ds}: {traceback.format_exc()}")
                info = {"dandiset": ds, "verdict": "INELIGIBLE_EXCEPTION",
                       "error": repr(e)}
            results["per_dandiset"][ds] = info
            log(f"   verdict={info.get('verdict')} stim={info.get('stim_count')} "
                f"report={info.get('report_count')}")

    verdicts = [v.get("verdict", "") for v in results["per_dandiset"].values()]
    n_eligible = sum(1 for v in verdicts if v == "ELIGIBLE_FOR_PASS_38_LCC_P3B")
    n_secondary = sum(1 for v in verdicts if v == "INELIGIBLE_NO_REPORT")
    n_no_stim = sum(1 for v in verdicts if v == "INELIGIBLE_NO_STIM")
    if n_eligible >= 1:
        agg = f"PROCEED_PASS_38 ({n_eligible}/3 eligible; rest secondary or no-stim)"
    elif n_secondary >= 1:
        agg = (f"INELIGIBLE_PRIMARY ({n_secondary}/3 stim-but-no-report; "
              "secondary-evidence path only); e36-D-v2 OpenNeuro-human-EEG REQUIRED")
    else:
        agg = "INELIGIBLE_ALL; e36-D-v2 OpenNeuro-human-EEG REQUIRED"
    results["aggregate_verdict"] = agg
    log(f"AGG: {agg}")

    with open(OUT, "w") as f:
        json.dump(results, f, indent=2, default=str)

if __name__ == "__main__":
    main()
