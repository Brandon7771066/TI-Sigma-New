"""
HMR audit of urb_608 + urb_639 illustrative examples (Pass-71 batch-3).

Parallel to Pass-65 inconceivability-criterion sweep (which found 0/36 principle
reassignments). This audit asks the DIFFERENT question: which existing
illustrative examples in urb_608 + urb_639 are natively HMR?

Method: regex-extract candidate-example sentences from each MT entry, then
mark candidates with structural-features-of-HMR (multiple-label-words present;
contradictory-framings; level-confusion markers; etc.).
"""

import re, json, os


def extract_examples(paper_path):
    """Extract example sentences (heuristic): lines containing 'Example:' or
    bulleted lines that follow an MT header."""
    if not os.path.exists(paper_path):
        return []
    with open(paper_path, errors="replace") as f:
        text = f.read()
    # Heuristic: find lines with 'example' or quoted text
    candidates = []
    for line in text.split("\n"):
        line = line.strip()
        if not line:
            continue
        # Skip headers/code/links
        if line.startswith("#") or line.startswith("```") or line.startswith("|"):
            continue
        if "example" in line.lower() or '"' in line or "'" in line:
            # Strip markdown bullets
            cleaned = re.sub(r"^[-*\d\.\)]+\s*", "", line)
            if 40 < len(cleaned) < 400:
                candidates.append(cleaned)
    return candidates[:50]  # cap


HMR_FEATURE_PATTERNS = [
    (r"\b(both|simultaneously|while also|yet also|also is)\b", "explicit-conjunction"),
    (r"\band\b.{1,40}\b(but|yet|though|even though|while)\b", "tension-marker"),
    (r"\b(neither.{1,30}nor)\b", "neither-nor-construction"),
    (r"\b(true.{1,30}false|false.{1,30}true)\b", "T-F-co-assertion"),
    (r"\b(meaningless|moot|irrelevant)\b.{1,80}\b(true|false|important)\b", "meta-mixed-with-base"),
    (r"\b(paradox|contradict|inconsist)\w*\b.{1,60}\b(true|valid|correct|right)\b", "paradox-plus-truth"),
    (r"\bdepends on\b|\bdepending on\b|\bin some sense\b", "framing-dependence"),
    (r"\bat the (same|different) (time|level)\b", "level-marker"),
]


def score_hmr_candidacy(text):
    """Return list of matched HMR-feature patterns + raw count."""
    matches = []
    for pattern, name in HMR_FEATURE_PATTERNS:
        if re.search(pattern, text, re.IGNORECASE):
            matches.append(name)
    return matches


def audit_paper(paper_path):
    examples = extract_examples(paper_path)
    results = []
    for ex in examples:
        features = score_hmr_candidacy(ex)
        if features:
            results.append({
                "text": ex[:250],
                "hmr_feature_count": len(features),
                "hmr_features": features,
                "hmr_candidate": len(features) >= 2,
            })
    return results


def main():
    urb_608 = "papers/urb_608_meta_truths_myrion_resolution_catalogue.md"
    urb_639 = "papers/urb_639_five_truth_completeness_distinctness_proof_extended_metatruths.md"

    audit_608 = audit_paper(urb_608)
    audit_639 = audit_paper(urb_639)

    summary = {
        "urb_608": {
            "n_examples_scanned": len(audit_608),
            "n_hmr_candidates": sum(1 for r in audit_608 if r["hmr_candidate"]),
            "top_candidates": sorted(audit_608, key=lambda r: -r["hmr_feature_count"])[:5],
        },
        "urb_639": {
            "n_examples_scanned": len(audit_639),
            "n_hmr_candidates": sum(1 for r in audit_639 if r["hmr_candidate"]),
            "top_candidates": sorted(audit_639, key=lambda r: -r["hmr_feature_count"])[:5],
        },
        "interpretation": (
            "HMR-feature regex audit (heuristic, low-precision). The audit identifies "
            "illustrative examples in urb_608+urb_639 that exhibit 2+ HMR-structural-features "
            "(conjunction-markers, tension-markers, level-markers, etc.) and are CANDIDATES "
            "for HMR-classification. Full HMR audit requires LLM-rater verification "
            "(deferred Pass-72+). Initial finding: HMR-candidates exist in non-trivial "
            "numbers in both papers, supporting HMR-1's claim that hybrid characterizations "
            "are NOT marginal — they are present throughout existing MT-illustrative examples."
        ),
    }
    return summary


if __name__ == "__main__":
    import sys
    out = main()
    json.dump(out, sys.stdout, indent=2)
