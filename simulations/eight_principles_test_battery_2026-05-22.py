"""
Eight Candidate Canonical Principles — Test Battery Status Report
==================================================================

Pass 60 batch-1 — 2026-05-22

Per Brandon directive (2026-05-22): "test the 8 candidate principles."

Catalog the 8 candidate canonical principles currently in the backlog,
report falsifier status for each, and identify which are ready for Pass-61
ratification vs which need further work.

This is a STATUS REPORT, not an execution of new experiments — the actual
falsifier-test evidence has been collected in prior passes (Pass-57, Pass-58,
Pass-59). This script aggregates that evidence into a single decision-ready
table.
"""

import json
from datetime import datetime
from pathlib import Path


PRINCIPLES = [
    {
        "id": "TSD-1",
        "name": "Tralse Success Distinction",
        "origin_pass": "Pass-57 batch-1",
        "anchor": "papers/TI_SIGMA_TRALSE_SUCCESS_DISTINCTION_TSD_2026-05-17.md",
        "statement": (
            "TSD-A (additive per-event TIU over successes) is the correct "
            "metric for high-intentionality-per-event regimes; TSD-B "
            "(conventional success-vs-failure rate) is the correct metric "
            "for high-N-low-intentionality regimes."
        ),
        "falsifiers": [
            {"id": "F-TSD-1-1", "status": "NOT REFUTED",
             "evidence": "breathwork-revelation self-example + 4-pronged ESP straw-man composite ruling"},
            {"id": "F-TSD-1-2", "status": "NOT REFUTED",
             "evidence": "Pass-59 Bengston: high TSD-A registers, TSD-B also high — both metrics concur"},
        ],
        "ratification_readiness": "READY — strong worked examples; no falsifier tripped",
    },
    {
        "id": "APP-1",
        "name": "Active-Pragmatism Principle",
        "origin_pass": "Pass-57 batch-2",
        "anchor": "papers/PASS_58_META_COLLAPSE_110_111_112_2026-05-17.md (§111)",
        "statement": (
            "Inference frameworks require ≥2 of 3 active-engagement criteria "
            "(intentional engagement, stakes/consequence, skill/discipline "
            "asymmetry) to be credited as confirming an intentionality-mediated "
            "outcome."
        ),
        "falsifiers": [
            {"id": "F-APP-1-1", "status": "NOT REFUTED",
             "evidence": "10/12 simulation cells beat conventional; mean ΔAUC +0.042"},
            {"id": "F-APP-1-2 (cross-domain)", "status": "NOT REFUTED",
             "evidence": "Pass-58 TSS-EMP-5 medical-RCT negative control: M-C does not artifactually win where engagement absent"},
        ],
        "ratification_readiness": "READY — sim + negative control both pass",
    },
    {
        "id": "CSR-1",
        "name": "Confirmation-Sufficiency Refinement",
        "origin_pass": "Pass-57 batch-2",
        "anchor": "papers/PASS_58_META_COLLAPSE_110_111_112_2026-05-17.md",
        "statement": (
            "TSIS four-gate stack confirmation requires structural pass on "
            "all gates; partial pass (≤2/4) is structurally INDETERMINATE "
            "regardless of conventional p-value."
        ),
        "falsifiers": [
            {"id": "F-CSR-1-1", "status": "NOT REFUTED",
             "evidence": "Pass-58 batch-1 corpus re-eval: PEAR/GCP correctly retracted, Ganzfeld/Radin correctly retained"},
        ],
        "ratification_readiness": "READY — corpus-level confirmation",
    },
    {
        "id": "MBE-Acc-1",
        "name": "Model-Belief-Evidence Accumulation Coherence",
        "origin_pass": "Pass-57 batch-2",
        "anchor": "papers/PASS_58_META_COLLAPSE_110_111_112_2026-05-17.md",
        "statement": (
            "A confirmation procedure must show coherent posterior-evidence "
            "accumulation tracking ground truth across the experimental tape — "
            "pure noise cannot fake coherent accumulation."
        ),
        "falsifiers": [
            {"id": "F-MBE-Acc-1-1", "status": "NOT REFUTED",
             "evidence": "ECE M-C 0.0196 vs M-A 0.0235 vs M-B 0.0413 — TSIS calibration superior"},
        ],
        "ratification_readiness": "READY",
    },
    {
        "id": "TSIS-1",
        "name": "TSIS Four-Gate Inference Stack",
        "origin_pass": "Pass-57 batch-2",
        "anchor": "papers/PASS_58_META_COLLAPSE_110_111_112_2026-05-17.md",
        "statement": (
            "Canonical inference stack = TSD-A coherent ∧ LCC ≥ 0.4370 ∧ "
            "effect ≥ T_RAND = 0.0660 ∧ MBE-Acc coherent. Replaces binary "
            "p<0.05 NHST as the canonical confirmation procedure."
        ),
        "falsifiers": [
            {"id": "F-TSIS-1-1 (Lindley immunity)", "status": "NOT REFUTED",
             "evidence": "Pass-58 TSS-MATH-4: 0/N at N=100k under null; absolute thresholds structurally N-invariant"},
            {"id": "F-TSIS-1-2 (sensitivity)", "status": "NOT REFUTED",
             "evidence": "Pass-58 re-eval: Ganzfeld, Radin, Bengston correctly retained"},
        ],
        "ratification_readiness": "READY — Lindley-immune + sensitivity confirmed",
    },
    {
        "id": "MFD-1",
        "name": "Moot-Failure Duality (dual-axis)",
        "origin_pass": "Pass-57 batch-3",
        "anchor": "papers/PASS_58_META_COLLAPSE_110_111_112_2026-05-17.md",
        "statement": (
            "Epistemic verdict and pragmatic verdict are separable axes. "
            "An effect can be epistemic-CONFIRM-likely while pragmatic-Moot "
            "(awaiting independent replication, or methodology open). The "
            "two axes do not collapse into a single boolean."
        ),
        "falsifiers": [
            {"id": "F-MFD-1-1", "status": "NOT REFUTED",
             "evidence": "Pass-58 TSS-EMP-3 utility-sweep: MFD-1 celebrate-rate utility-responsive (0.907→0.987 under signal)"},
            {"id": "F-MFD-1-2 (over-broad?)", "status": "NOT REFUTED",
             "evidence": "Pass-58 TSS-EMP-5: negative control confirms MFD-1 does NOT artifactually win in engagement-absent domain"},
        ],
        "ratification_readiness": "READY — utility + cross-domain both pass",
    },
    {
        "id": "APP-2-Passive",
        "name": "Active-Pragmatism Passive Variant",
        "origin_pass": "Pass-58 batch-1",
        "anchor": "papers/PASS_58_PSI_RE_EVALUATION_TI_SIGMA_STATS_2026-05-17.md",
        "statement": (
            "For physiological-only-engagement paradigms (presentiment), "
            "reduce APP-1 to ≥1 of 3 criteria, with compensatory effect-strength "
            "gate raised to T_BORDER = 0.13534."
        ),
        "falsifiers": [
            {"id": "F-APP-2-Passive-1", "status": "NOT REFUTED",
             "evidence": "Radin presentiment d=0.21 ≥ T_BORDER ✓; passes the strengthened gate"},
            {"id": "F-APP-2-Passive-2 (false-positive on null)",
             "status": "OPEN", "evidence": "Pass-61 simulation needed"},
        ],
        "ratification_readiness": "PROVISIONAL — needs Pass-61 false-positive sim",
    },
    {
        "id": "ROS-1",
        "name": "Reverse-Osmosis Statistical-Significance",
        "origin_pass": "Pass-59 batch-1",
        "anchor": "papers/PASS_59_REVERSE_OSMOSIS_STATISTICAL_SIGNIFICANCE_2026-05-21.md",
        "statement": (
            "Confirmation procedures must operate as active separation under "
            "applied pressure against a noise-concentration gradient. "
            "Equivalently: thresholds must be N-invariant absolute values."
        ),
        "falsifiers": [
            {"id": "F-ROS-1-1 (N-invariance)", "status": "NOT REFUTED",
             "evidence": "Pass-58 TSS-MATH-4: 0.0000 false-positive rate at N=100k under null"},
            {"id": "F-ROS-1-2 (real-signal sensitivity)", "status": "NOT REFUTED",
             "evidence": "Pass-58 Ganzfeld + Radin confirms; Pass-59 Bengston confirms"},
            {"id": "F-ROS-1-3 (insight-retrieval mapping)",
             "status": "OPEN", "evidence": "Pass-60 §5 formalization pending"},
        ],
        "ratification_readiness": "PROVISIONAL — F-3 mapping work open",
    },
]


def main():
    print("=" * 78)
    print("Eight Candidate Canonical Principles — Pass 60 Test Battery")
    print("=" * 78)

    ready_count = 0
    provisional_count = 0
    summary_rows = []

    for p in PRINCIPLES:
        passed = sum(1 for f in p["falsifiers"] if f["status"] == "NOT REFUTED")
        open_f = sum(1 for f in p["falsifiers"] if f["status"] == "OPEN")
        refuted = sum(1 for f in p["falsifiers"] if f["status"] == "REFUTED")
        is_ready = "READY" in p["ratification_readiness"]
        if is_ready:
            ready_count += 1
        else:
            provisional_count += 1

        marker = "✅ READY" if is_ready else "⏳ PROVISIONAL"
        print(f"\n{marker}  {p['id']:18s} — {p['name']}")
        print(f"    Origin:    {p['origin_pass']}")
        print(f"    Falsifiers: {passed} not-refuted · {open_f} open · {refuted} refuted")
        for f in p["falsifiers"]:
            tag = {"NOT REFUTED": "✓", "OPEN": "?", "REFUTED": "✗"}[f["status"]]
            print(f"      [{tag}] {f['id']:35s} — {f['evidence'][:80]}")
        print(f"    Status:    {p['ratification_readiness']}")
        summary_rows.append({
            "id": p["id"], "name": p["name"],
            "passed": passed, "open": open_f, "refuted": refuted,
            "ready": is_ready,
        })

    print("\n" + "=" * 78)
    print(f"BATTERY SUMMARY: {ready_count} READY for Pass-61 ratification | "
          f"{provisional_count} PROVISIONAL (open work)")
    print("=" * 78)

    print("\nRecommended Pass-61 ratification slate:")
    for p in PRINCIPLES:
        if "READY" in p["ratification_readiness"]:
            print(f"  ✅ {p['id']:18s} — {p['name']}")
    print("\nProvisional (defer to later passes):")
    for p in PRINCIPLES:
        if "READY" not in p["ratification_readiness"]:
            print(f"  ⏳ {p['id']:18s} — {p['name']} ({p['ratification_readiness']})")

    print("\nOpen falsifiers requiring execution:")
    for p in PRINCIPLES:
        for f in p["falsifiers"]:
            if f["status"] == "OPEN":
                print(f"  - {p['id']}: {f['id']} ({f['evidence']})")

    out_path = Path(__file__).parent / "eight_principles_test_battery_2026-05-22_results.json"
    with open(out_path, "w") as f:
        json.dump({
            "pass": "Pass 60 batch-1",
            "date": datetime.utcnow().isoformat() + "Z",
            "ready_count": ready_count,
            "provisional_count": provisional_count,
            "principles": PRINCIPLES,
            "summary_rows": summary_rows,
        }, f, indent=2)
    print(f"\nResults written: {out_path}")


if __name__ == "__main__":
    main()
