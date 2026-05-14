"""T51-H3 SATLIB UF-50 step-skip benchmark.

Pre-registered comparison (per `HYPERCOMPUTATION_OCCAMS_RAZOR_STEP_SKIPPING.md` + Pass-51 batch-2 H3):
  - BASELINE: DPLL with unit propagation only, chronological backtracking, first-literal branching.
  - STEP-SKIP: DPLL + unit propagation + pure-literal elimination + MOM-style occurrence
    heuristic with preferred polarity (NOT true 1-step look-ahead simulation; architect-flagged
    naming correction, 2026-05-14).
  
Metrics per instance:
  - decisions   (number of branching decisions)
  - unit_props  (unit-propagation events)
  - recursions  (recursive solve calls)
  - solved      (bool, must be SAT for UF-50 satisfiable corpus)

Pre-reg success criterion (Pass-51 batch-2 H3):
  >=10% reduction in decision count on UF-50 corpus => H3 CONFIRMS.
  <10% reduction => H3 DISCONFIRMS.

HONESTY NOTE (#69): "Step-skip" mapped to known classical heuristics (pure-literal + look-ahead) is
well-established SAT-solver methodology. A >=10% reduction is BANAL within classical SAT research.
This benchmark therefore tests whether the literal pre-reg threshold is met -- but the empirical
result, whichever direction, cannot directly discriminate hypercomputation from improved classical
heuristics. The methodological-vacuity verdict will be discussed in the writeup regardless of
the numerical outcome.
"""
import os, sys, time, json, glob, random
from pathlib import Path

random.seed(42)
sys.setrecursionlimit(20000)


def parse_dimacs(path):
    """Parse DIMACS CNF file. Returns list of clauses (each clause = list of ints)."""
    clauses = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("c") or line.startswith("p") or line.startswith("%"):
                continue
            if line == "0":
                continue
            lits = [int(x) for x in line.split() if x and x != "0"]
            if lits:
                clauses.append(lits)
    return clauses


# ============================================================================
# BASELINE DPLL: unit propagation + chronological backtracking + first-literal
# ============================================================================
def dpll_baseline(clauses, assignment=None, stats=None):
    if assignment is None:
        assignment = {}
    if stats is None:
        stats = {"decisions": 0, "unit_props": 0, "recursions": 0}
    stats["recursions"] += 1

    # Simplify
    simplified = []
    for clause in clauses:
        new_clause = []
        satisfied = False
        for lit in clause:
            var = abs(lit)
            if var in assignment:
                val = assignment[var]
                if (lit > 0 and val) or (lit < 0 and not val):
                    satisfied = True
                    break
            else:
                new_clause.append(lit)
        if satisfied:
            continue
        if not new_clause:
            return False, stats
        simplified.append(new_clause)

    if not simplified:
        return True, stats

    # Unit propagation
    for clause in simplified:
        if len(clause) == 1:
            lit = clause[0]
            var = abs(lit)
            stats["unit_props"] += 1
            new_assign = dict(assignment)
            new_assign[var] = (lit > 0)
            return dpll_baseline(simplified, new_assign, stats)

    # Branch: first unassigned variable from first non-unit clause
    var = abs(simplified[0][0])
    stats["decisions"] += 1
    for val in (True, False):
        new_assign = dict(assignment)
        new_assign[var] = val
        sat, _ = dpll_baseline(simplified, new_assign, stats)
        if sat:
            return True, stats
    return False, stats


# ============================================================================
# STEP-SKIP DPLL: unit prop + pure-literal elimination + 1-step look-ahead branching
# ============================================================================
def dpll_step_skip(clauses, assignment=None, stats=None):
    if assignment is None:
        assignment = {}
    if stats is None:
        stats = {"decisions": 0, "unit_props": 0, "recursions": 0, "pure_lits": 0}
    stats["recursions"] += 1

    # Simplify
    simplified = []
    for clause in clauses:
        new_clause = []
        satisfied = False
        for lit in clause:
            var = abs(lit)
            if var in assignment:
                val = assignment[var]
                if (lit > 0 and val) or (lit < 0 and not val):
                    satisfied = True
                    break
            else:
                new_clause.append(lit)
        if satisfied:
            continue
        if not new_clause:
            return False, stats
        simplified.append(new_clause)

    if not simplified:
        return True, stats

    # Unit propagation
    for clause in simplified:
        if len(clause) == 1:
            lit = clause[0]
            var = abs(lit)
            stats["unit_props"] += 1
            new_assign = dict(assignment)
            new_assign[var] = (lit > 0)
            return dpll_step_skip(simplified, new_assign, stats)

    # Pure-literal elimination (STEP-SKIP feature 1)
    polarities = {}  # var -> set of polarities seen
    for clause in simplified:
        for lit in clause:
            var = abs(lit)
            polarities.setdefault(var, set()).add(lit > 0)
    pure = [(var, list(pols)[0]) for var, pols in polarities.items() if len(pols) == 1]
    if pure:
        var, val = pure[0]
        stats["pure_lits"] += 1
        new_assign = dict(assignment)
        new_assign[var] = val
        return dpll_step_skip(simplified, new_assign, stats)

    # MOM-style occurrence heuristic with preferred polarity (STEP-SKIP feature 2):
    # NOT true 1-step look-ahead simulation -- uses raw occurrence counts only.
    # (Architect-flagged naming correction, 2026-05-14.)
    counts = {}
    for clause in simplified:
        for lit in clause:
            var = abs(lit)
            counts[var] = counts.get(var, 0) + 1
    var = max(counts, key=counts.get)
    stats["decisions"] += 1

    # Try the polarity that appears more often first
    pos_count = sum(1 for c in simplified for lit in c if lit == var)
    neg_count = sum(1 for c in simplified for lit in c if lit == -var)
    first_val = pos_count >= neg_count

    for val in (first_val, not first_val):
        new_assign = dict(assignment)
        new_assign[var] = val
        sat, _ = dpll_step_skip(simplified, new_assign, stats)
        if sat:
            return True, stats
    return False, stats


# ============================================================================
# Benchmark harness
# ============================================================================
def run_benchmark(n_instances=100, timeout_per_instance=20.0):
    """Run both solvers on n_instances UF-50 problems."""
    cnf_dir = Path("data/satlib_uf50")
    instances = sorted(cnf_dir.glob("uf50-*.cnf"))[:n_instances]
    print(f"Found {len(instances)} instances; running {n_instances}")

    results = []
    for i, path in enumerate(instances):
        clauses = parse_dimacs(path)
        if not clauses:
            continue
        n_vars = max(abs(l) for c in clauses for l in c)
        n_clauses = len(clauses)

        # Baseline
        t0 = time.time()
        try:
            sat_b, stats_b = dpll_baseline(clauses)
            time_b = time.time() - t0
            base_ok = True
        except RecursionError:
            sat_b, stats_b, time_b = None, {"decisions": -1, "unit_props": -1, "recursions": -1}, -1
            base_ok = False

        # Step-skip
        t0 = time.time()
        try:
            sat_s, stats_s = dpll_step_skip(clauses)
            time_s = time.time() - t0
            ss_ok = True
        except RecursionError:
            sat_s, stats_s, time_s = None, {"decisions": -1, "unit_props": -1, "recursions": -1, "pure_lits": -1}, -1
            ss_ok = False

        rec = {
            "instance": path.name,
            "n_vars": n_vars,
            "n_clauses": n_clauses,
            "baseline_sat": sat_b,
            "baseline_decisions": stats_b.get("decisions"),
            "baseline_unit_props": stats_b.get("unit_props"),
            "baseline_recursions": stats_b.get("recursions"),
            "baseline_time": time_b,
            "stepskip_sat": sat_s,
            "stepskip_decisions": stats_s.get("decisions"),
            "stepskip_unit_props": stats_s.get("unit_props"),
            "stepskip_recursions": stats_s.get("recursions"),
            "stepskip_pure_lits": stats_s.get("pure_lits"),
            "stepskip_time": time_s,
            "baseline_ok": base_ok,
            "stepskip_ok": ss_ok,
        }
        results.append(rec)
        if (i + 1) % 10 == 0:
            print(f"  {i+1}/{n_instances}: {path.name} | base={stats_b.get('decisions')} dec, "
                  f"skip={stats_s.get('decisions')} dec, b_sat={sat_b}, s_sat={sat_s}")

    return results


def summarize(results):
    valid = [r for r in results if r["baseline_ok"] and r["stepskip_ok"]
             and r["baseline_sat"] == r["stepskip_sat"]]
    n = len(valid)
    if n == 0:
        return {"error": "no valid pairs"}

    base_dec = [r["baseline_decisions"] for r in valid]
    skip_dec = [r["stepskip_decisions"] for r in valid]
    base_rec = [r["baseline_recursions"] for r in valid]
    skip_rec = [r["stepskip_recursions"] for r in valid]
    base_time = [r["baseline_time"] for r in valid]
    skip_time = [r["stepskip_time"] for r in valid]

    mean_base_dec = sum(base_dec) / n
    mean_skip_dec = sum(skip_dec) / n
    reduction_pct = 100 * (mean_base_dec - mean_skip_dec) / mean_base_dec if mean_base_dec > 0 else 0

    # Per-instance reductions
    per_inst_red = [100 * (b - s) / b for b, s in zip(base_dec, skip_dec) if b > 0]
    median_red = sorted(per_inst_red)[len(per_inst_red) // 2] if per_inst_red else 0
    n_better = sum(1 for r in per_inst_red if r > 0)
    n_worse = sum(1 for r in per_inst_red if r < 0)
    n_equal = sum(1 for r in per_inst_red if r == 0)

    summary = {
        "n_instances_total": len(results),
        "n_instances_valid": n,
        "n_sat_baseline": sum(1 for r in valid if r["baseline_sat"]),
        "n_sat_stepskip": sum(1 for r in valid if r["stepskip_sat"]),
        "mean_baseline_decisions": mean_base_dec,
        "mean_stepskip_decisions": mean_skip_dec,
        "mean_decision_reduction_pct": reduction_pct,
        "median_per_instance_reduction_pct": median_red,
        "n_stepskip_better": n_better,
        "n_stepskip_worse": n_worse,
        "n_tied": n_equal,
        "mean_baseline_recursions": sum(base_rec) / n,
        "mean_stepskip_recursions": sum(skip_rec) / n,
        "mean_baseline_time_s": sum(base_time) / n,
        "mean_stepskip_time_s": sum(skip_time) / n,
        "pre_reg_threshold_pct": 10.0,
        "verdict_literal": "CONFIRM" if reduction_pct >= 10 else "DISCONFIRM",
    }
    return summary


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    print(f"=== T51-H3 SATLIB Step-Skip Benchmark (N={n}) ===")
    results = run_benchmark(n_instances=n)
    summary = summarize(results)

    outdir = Path(os.path.dirname(os.path.abspath(__file__)))
    with open(outdir / "results_raw.json", "w") as f:
        json.dump(results, f, indent=2)
    with open(outdir / "summary.json", "w") as f:
        json.dump(summary, f, indent=2)

    print("\n=== SUMMARY ===")
    print(json.dumps(summary, indent=2))
