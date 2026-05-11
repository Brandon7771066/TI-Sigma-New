"""Pass 43 — Mendi 20-min session #1 detrended analysis.
Anti-HARK: this script + threshold spec frozen BEFORE Welch t-test inspection
of detrended deltas (architect-style provenance: see _provenance block in
results.json). Pre-reg verdict: any |t| >= 3.0 on detrended stim-vs-base
delta = SIGNIFICANT response; |t| < 2.0 = NULL; 2.0 <= |t| < 3.0 = MARGINAL.
"""
import csv, json, math, statistics, hashlib, os
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = Path("data/mendi/sessions/session_2026-05-11T12-22-50_decoded.csv")

rows = []
with SRC.open() as f:
    for r in csv.DictReader(f):
        rows.append((float(r["t_elapsed_s"]), int(r["raw_value"]), r["phase"]))

ts  = [r[0] for r in rows]; vals = [r[1] for r in rows]; n = len(ts)
mt, mv = sum(ts)/n, sum(vals)/n
sxy = sum((t-mt)*(v-mv) for t,v in zip(ts,vals))
sxx = sum((t-mt)**2 for t in ts)
slope = sxy/sxx; intercept = mv - slope*mt
detrended = [(t, v - (slope*t + intercept), p) for t,v,p in rows]

groups = {}
for t,d,p in detrended: groups.setdefault(p,[]).append(d)

def welch(a,b):
    if len(a)<2 or len(b)<2: return None,None
    ma,mb = statistics.mean(a), statistics.mean(b)
    va,vb = statistics.variance(a), statistics.variance(b)
    se = math.sqrt(va/len(a)+vb/len(b))
    if se==0: return None,None
    t = (ma-mb)/se
    df = (va/len(a)+vb/len(b))**2 / ((va/len(a))**2/(len(a)-1) + (vb/len(b))**2/(len(b)-1))
    return t,df

phase_stats = {p: {"n": len(g), "mean_detrended": statistics.mean(g),
                   "stdev_detrended": statistics.stdev(g) if len(g)>1 else 0.0,
                   "raw_mean": statistics.mean([v for _,v,ph in rows if ph==p])}
               for p,g in groups.items()}

comps = [("STIM1_ARITHMETIC","BASELINE"),("STIM2_BREATHHOLD","RECOVERY1"),
         ("STIM3_ARITHMETIC","RECOVERY2"),("STIM4_BREATHHOLD","RECOVERY3")]
deltas = []
for s,b in comps:
    sg, bg = groups.get(s,[]), groups.get(b,[])
    delta = statistics.mean(sg) - statistics.mean(bg)
    t,df = welch(sg,bg)
    verdict = ("NULL" if abs(t)<2.0 else "MARGINAL" if abs(t)<3.0 else "SIGNIFICANT")
    deltas.append({"stim": s, "baseline": b, "n_stim": len(sg), "n_base": len(bg),
                   "delta_detrended_adc": round(delta,4),
                   "welch_t": round(t,3), "welch_df": round(df,1),
                   "verdict_pre_registered": verdict})

sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
out = {
    "pass": 43, "test_id": "mendi_session_1_detrended",
    "source_csv": str(SRC),
    "n_frames": n,
    "linear_drift": {"slope_adc_per_min": round(slope*60,4),
                     "total_drift_20min_adc": round(slope*1200,3),
                     "intercept_adc": round(intercept,2)},
    "phase_stats": phase_stats,
    "stimulus_deltas_detrended": deltas,
    "prereg_thresholds": {"SIGNIFICANT": "|t| >= 3.0",
                          "MARGINAL": "2.0 <= |t| < 3.0",
                          "NULL": "|t| < 2.0"},
    "_provenance": {"analyze_script_sha256": sha,
                    "anti_hark_status": "thresholds + script frozen before Welch t-inspection of detrended values"},
}
out_path = ROOT/"results.json"
out_path.write_text(json.dumps(out, indent=2))
print(json.dumps(out, indent=2))
