"""
Finalize Pass-32 results.json by computing aggregate verdict from existing
per-Dandiset entries. Use after all 3 process_dandiset() calls have populated
results['per_dandiset'].
"""
import json, os
ROOT = os.path.dirname(os.path.abspath(__file__))
RESULTS_PATH = os.path.join(ROOT, "results.json")

results = json.load(open(RESULTS_PATH))
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
print(f"AGG: {agg}  summary: {results['verdicts_summary']}")
print(f"verdicts: {verdicts}")
