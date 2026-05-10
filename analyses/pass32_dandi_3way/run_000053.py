"""Run only DANDI:000053 (40GB stream, ~5min) and finalize aggregate verdict."""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from runner import process_dandiset, RESULTS_PATH

results = json.load(open(RESULTS_PATH))
sel = json.load(open(os.path.join(os.path.dirname(__file__), "selected_assets.json")))

print(">> 000053 (40GB stream, ~5min)", flush=True)
r = process_dandiset("000053", sel["000053"])
results["per_dandiset"]["000053"] = r
print(f"   verdict={r.get('verdict')} r={r.get('pearson_r')} elapsed={r.get('elapsed_sec')}s err={r.get('error')}", flush=True)

verdicts = [v.get("verdict") for v in results["per_dandiset"].values()]
eligible = [v for v in verdicts if v in ("CONFIRM", "REJECT", "PARTIAL")]
nC = sum(1 for v in eligible if v == "CONFIRM")
nR = sum(1 for v in eligible if v == "REJECT")
nE = len(eligible)
if nE == 0:
    agg = "INELIGIBLE_ALL"
elif nC == nE:
    agg = "SURVIVES"
elif nR >= max(2, nE - nC):
    agg = "REFUTED"
else:
    agg = "MIXED"
results["aggregate_verdict"] = agg
results["verdicts_summary"] = {
    "CONFIRM": nC, "REJECT": nR,
    "PARTIAL": sum(1 for v in eligible if v == "PARTIAL"),
    "INELIGIBLE": sum(1 for v in verdicts if v == "INELIGIBLE"),
    "OTHER": sum(1 for v in verdicts if v not in ("CONFIRM", "REJECT", "PARTIAL", "INELIGIBLE")),
    "n_eligible": nE,
}
with open(RESULTS_PATH, "w") as f:
    json.dump(results, f, indent=2, default=str)
print(f"AGG: {agg}  summary: {results['verdicts_summary']}", flush=True)
