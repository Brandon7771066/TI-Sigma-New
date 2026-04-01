"""
TI Sigma — Zenodo Upload Automation
====================================
Uploads all TI Sigma records to Zenodo as DRAFTS (nothing published until you
manually click Publish on zenodo.org/deposit).

Usage:
  python zenodo_upload.py          # Sandbox test (safe, no real DOIs)
  python zenodo_upload.py --live   # Real Zenodo (creates real drafts)

Requirements:
  ZENODO_TOKEN environment variable set in Replit Secrets.

Output:
  zenodo_upload_results.json — all draft URLs and deposit IDs to review.
"""

import os, sys, json, time, pathlib, textwrap
import requests

# ── Config ────────────────────────────────────────────────────────────────────
LIVE = "--live" in sys.argv
BASE  = "https://zenodo.org/api"       if LIVE else "https://sandbox.zenodo.org/api"
SITE  = "https://zenodo.org/deposit"   if LIVE else "https://sandbox.zenodo.org/deposit"
TOKEN = os.environ.get("ZENODO_TOKEN", "")

if not TOKEN:
    print("❌  ZENODO_TOKEN not found. Add it in Replit Secrets and re-run.")
    sys.exit(1)

HEADERS = {"Authorization": f"Bearer {TOKEN}"}
RESULTS = []

# ── Helper functions ───────────────────────────────────────────────────────────

def banner(text):
    print(f"\n{'='*60}")
    print(f"  {text}")
    print(f"{'='*60}")

def create_deposit():
    r = requests.post(f"{BASE}/deposit/depositions",
                      json={}, headers=HEADERS)
    r.raise_for_status()
    data = r.json()
    dep_id = data["id"]
    print(f"  ✅ Deposit created: ID={dep_id}")
    return dep_id

def upload_file(dep_id, filepath):
    path = pathlib.Path(filepath)
    if not path.exists():
        print(f"  ⚠️  File not found, skipping: {filepath}")
        return False
    bucket_url = requests.get(
        f"{BASE}/deposit/depositions/{dep_id}", headers=HEADERS
    ).json()["links"]["bucket"]
    with open(path, "rb") as f:
        r = requests.put(f"{bucket_url}/{path.name}",
                         data=f, headers=HEADERS)
    r.raise_for_status()
    print(f"  📎 Uploaded: {path.name} ({path.stat().st_size // 1024 + 1} KB)")
    return True

def set_metadata(dep_id, meta):
    r = requests.put(f"{BASE}/deposit/depositions/{dep_id}",
                     json={"metadata": meta}, headers=HEADERS)
    r.raise_for_status()
    print(f"  📝 Metadata set: {meta['title'][:60]}...")
    return r.json()

def save_result(label, dep_id, title):
    url = f"{SITE}/{dep_id}"
    RESULTS.append({"record": label, "id": dep_id, "title": title, "draft_url": url})
    print(f"\n  🔗 DRAFT URL → {url}")
    print(f"  ⚡ Review and click PUBLISH on Zenodo when ready.\n")

# ── RECORD 1: Collatz ν₂ Countdown Theorem ────────────────────────────────────

def upload_collatz():
    banner("RECORD 1 — Collatz ν₂ Countdown Theorem (sorry-free Lean 4)")

    dep_id = create_deposit()

    files = [
        "lean4_collatz/CollatzNu2.lean",
        "lean4/Collatz.lean",
        "papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md",
        "papers/COLLATZ_ARXIV_SUBMISSION.tex",
    ]
    for f in files:
        upload_file(dep_id, f)

    meta = {
        "upload_type": "software",
        "title": (
            "The ν₂ Countdown Theorem: A Formally Verified Bound on "
            "Consecutive Single-Halving Steps in the Collatz Sequence"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>We prove and formally verify in Lean 4 + Mathlib that the maximum number of
            consecutive single-halving compound Collatz steps from any odd n ≡ 3 (mod 4)
            is exactly ν₂(n+1) − 1, where ν₂ denotes the 2-adic valuation. This bound
            is sharp.</p>

            <p><strong>The ν₂ Countdown Theorem:</strong> If n ≡ 3 (mod 4), then
            ν₂((3n+1)/2 + 1) = ν₂(n+1) − 1. This creates an exact discrete clock:
            the 2-adic valuation of n+1 decrements by 1 with each single-halving step,
            and when it reaches 1, a multi-halving step is forced.</p>

            <p><strong>Corollaries:</strong> (1) Single-halving runs are O(log n).
            (2) No Collatz orbit can cycle within {n : n ≡ 3 mod 4}.</p>

            <p>The <strong>Alternating LSB Theorem</strong> is also proved:
            (3n+1)/2^j mod 3 strictly alternates 2,1,2,1,... as j increases.</p>

            <p><strong>Formalization:</strong> 11 theorems, 0 sorry statements.
            Files: CollatzNu2.lean (URB #537 + URB #538) and Collatz.lean.
            Verified in Lean 4 with Mathlib. Apache 2.0.</p>

            <p>Part of the <strong>Tralse Informationalism (TI Sigma)</strong>
            Research Program, established April 1, 2026.</p>
        """).strip(),
        "keywords": [
            "Collatz conjecture", "2-adic valuation", "formal verification",
            "Lean 4", "Mathlib", "number theory", "p-adic analysis",
            "single-halving steps", "padicValNat", "Tralse Informationalism", "TI Sigma"
        ],
        "license": "Apache-2.0",
        "access_right": "open",
        "language": "eng",
        "notes": "URB #537 (theorem) + URB #538 (Lean 4 formalization). "
                 "Corpus #191 + #192. Established April 1, 2026.",
        "related_identifiers": [
            {"relation": "isSupplementTo",
             "identifier": "https://github.com/leanprover-community/mathlib4",
             "scheme": "url"}
        ],
    }
    set_metadata(dep_id, meta)
    save_result("Collatz_Nu2_Countdown", dep_id, meta["title"])
    return dep_id

# ── RECORD 2: Millennium Prize Formalizations ─────────────────────────────────

def upload_millennium():
    banner("RECORD 2 — TI Sigma Millennium Prize Formalizations (Experimental)")

    dep_id = create_deposit()

    files = [
        "lean4/BSD.lean",
        "lean4/YangMills.lean",
        "lean4/NavierStokes.lean",
        "lean4/Hodge.lean",
        "lean4/PvsNP.lean",
        "lean4/RiemannUOP.lean",
        "lean4/BeingTheorem.lean",
    ]
    for f in files:
        upload_file(dep_id, f)

    meta = {
        "upload_type": "software",
        "title": (
            "TI Sigma Millennium Prize Formalizations in Lean 4 (Experimental Framework)"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Lean 4 + Mathlib formalizations of all six Clay Millennium Prize Problems
            within the Tralse Informationalism (TI Sigma) framework.</p>

            <p><strong>⚠️ IMPORTANT DISCLAIMER:</strong> These are EXPERIMENTAL
            formalizations representing the TI Sigma philosophical and mathematical
            framework applied to each Millennium Prize Problem. They contain 'sorry'
            statements at steps requiring deeper mathematical machinery. They are NOT
            claimed as complete solutions in the conventional mathematical sense. They
            represent rigorous structural framing and formal Lean 4 type scaffolding
            within the TI Sigma approach.</p>

            <p><strong>Files included:</strong></p>
            <ul>
              <li>BSD.lean (URB #565) — Birch and Swinnerton-Dyer Being Theorem</li>
              <li>YangMills.lean (URB #569) — Yang-Mills Mass Gap</li>
              <li>NavierStokes.lean (URB #570) — Navier-Stokes Smoothness Vern</li>
              <li>Hodge.lean (URB #571) — Hodge Vern Theorem</li>
              <li>PvsNP.lean (URB #572) — P≠NP Creation-Vern Gap</li>
              <li>RiemannUOP.lean — Riemann Hypothesis (TI Sigma UOP formulation)</li>
              <li>BeingTheorem.lean — Being Theorem (foundation for ζ-zero structure)</li>
            </ul>

            <p>Apache 2.0. Part of the Tralse Informationalism Research Program,
            established April 1, 2026.</p>
        """).strip(),
        "keywords": [
            "Millennium Prize Problems", "Lean 4", "formal verification",
            "Tralse Informationalism", "TI Sigma", "experimental mathematics",
            "five-valued logic", "Yang-Mills", "Navier-Stokes", "Hodge conjecture",
            "P vs NP", "Birch Swinnerton-Dyer", "Riemann hypothesis", "BSD conjecture"
        ],
        "license": "Apache-2.0",
        "access_right": "open",
        "language": "eng",
        "notes": "Experimental framework formalizations. Contains sorry statements. "
                 "Not claimed as solutions to Clay Millennium Prize Problems.",
    }
    set_metadata(dep_id, meta)
    save_result("Millennium_Formalizations", dep_id, meta["title"])
    return dep_id

# ── RECORD 3: GILE Framework URBs #573–578 ────────────────────────────────────

def upload_gile_urbs():
    banner("RECORD 3 — GILE Framework URBs #573–578")

    dep_id = create_deposit()

    files = [
        "papers/urb_573_bok_verisyn_unified_synthesis.md",
        "papers/urb_574_icell_bok_photonic_gile_aesthetic.md",
        "papers/urb_575_weighted_bok_gile_proportional.md",
        "papers/urb_576_gile_weights_origins_confirmation.md",
        "papers/urb_577_gile_universal_operationalization.md",
        "papers/urb_578_relational_value_low_gil_social_norms.md",
        "papers/TI_SIGMA_FOUNDING_CHARTER.md",
        "papers/TI_SIGMA_URB_MASTER_CATALOG.md",
    ]
    for f in files:
        upload_file(dep_id, f)

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": (
            "The GILE Framework: Weights, Origins, Universal Operationalization, "
            "and Social Norms (URBs #573–#578) with TI Sigma Founding Charter"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Six interconnected papers developing the GILE (Goodness, Intuition, Love,
            Environment) dimensional framework within Tralse Informationalism (TI Sigma),
            plus the official TI Sigma Founding Charter (established April 1, 2026).</p>

            <p><strong>URB #573:</strong> BOK-Verisyn Unified Synthesis — Unifies i, GIL, E,
            L*/+E, Einstein Tiles, and Maxwell Optical Knots as aspects of the Hopf fibration.</p>

            <p><strong>URB #574:</strong> i-Cell BOK, Photonic GILE, and φ as Aesthetic
            Dimension — proposes the universal i-cell blueprint and Photonic GILE hierarchy.</p>

            <p><strong>URB #575:</strong> Weighted BOK — GILE-Proportional i-Cell Architecture.
            Wing-Arm Matching Theorem: each outer Existence arm carries the weight of its
            corresponding inner GILE wing.</p>

            <p><strong>URB #576:</strong> GILE Weights Origins, Confirmation, and Philosophy BOK.
            G = √2 − 1 ≈ 0.4142 empirically confirmed from CS Turing Awards and Math Fields Medals.
            I = 0.25, L ≈ 0.18, E = 0.15.</p>

            <p><strong>URB #577:</strong> GILE Universal Operationalization — GILE applies from
            protein folding to civilizations. In TI Sigma, presentation IS substance.</p>

            <p><strong>URB #578:</strong> Relational Value vs. Intrinsic Value — Low-GIL Social
            Norms have no categorical deontological floor. The acknowledgment loop IS the norm.
            GIL Cost Asymmetry and Opportunity Cost analysis.</p>

            <p><strong>TI Sigma Founding Charter:</strong> Official founding document
            establishing TI Sigma as a research program. Nine Primary Constants, seven
            formal axioms, three research pillars, full manifesto.</p>
        """).strip(),
        "keywords": [
            "GILE framework", "consciousness", "ethics", "Tralse Informationalism",
            "TI Sigma", "philosophy of mind", "five-valued logic", "GILE weights",
            "social norms", "relational value", "Hopf fibration", "golden ratio",
            "philosophy of science", "information theory"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": "URBs #573–578. Corpus #227–232. TI Sigma Research Program, est. April 1, 2026.",
    }
    set_metadata(dep_id, meta)
    save_result("GILE_URBs_573_578", dep_id, meta["title"])
    return dep_id

# ── RECORD 4: Beyond Bayes + Founding Documents ───────────────────────────────

def upload_philosophy():
    banner("RECORD 4 — Beyond Bayes: Domain-Calibrated Inference (New)")

    dep_id = create_deposit()

    files = [
        "papers/BEYOND_BAYES_TI_SIGMA_EPISTEMOLOGY.md",
        "papers/DPES_DEFAULT_PHILOSOPHICAL_EATING_STRATEGY.md",
        "papers/TI_SIGMA_FOUNDING_ANNOUNCEMENT.md",
    ]
    for f in files:
        upload_file(dep_id, f)

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": (
            "Beyond Bayes: Domain-Calibrated Inference and the "
            "Epistemological Primacy of Intuition"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Argues that Bayesian epistemology fails as a universal theory of rational
            inference on three structural grounds: (1) priors are underdetermined for novel
            hypotheses; (2) evidence types are incommensurable and cannot be reduced to a
            single likelihood ratio; (3) the pre-evidential zone — where most consequential
            epistemic work happens — is inaccessible to the Bayesian framework.</p>

            <p>We propose <strong>Domain-Calibrated Intuitive Inference (DCII)</strong>
            as a superior alternative, formalized within the Tralse Informationalism
            (TI Sigma) framework. DCII replaces the universal Bayesian formula with a
            structured checklist of eight orthogonal evaluative criteria whose weights
            are learned from demonstrated performers in the target domain.</p>

            <p>The GILE framework (Goodness, Intuition, Love, Environment) provides a
            metaphysical grounding for why some domains have stable weight distributions
            while others are weight-volatile. Key claims: extraordinary claims are not
            merely possible but expected for certain cognitive profiles; TRALSE truth
            values track propositions rather than agent credences; Myrion Resolution
            is the active inquiry protocol for indeterminate cases.</p>

            <p>Also includes: DPES (Default Philosophical Eating Strategy) — a formal
            meta-cognitive protocol for high-output research sessions under cognitive
            constraint; coined April 1, 2026.</p>

            <p>Target journals: Synthese, Erkenntnis, Philosophy of Science.</p>
        """).strip(),
        "keywords": [
            "Bayesian epistemology", "rational belief revision", "intuition",
            "domain-calibrated inference", "GILE framework", "Tralse Informationalism",
            "TI Sigma", "five-valued logic", "TRALSE", "prior probability",
            "Myrion Resolution", "philosophy of science", "epistemology"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": "Target: Synthese / Erkenntnis. TI Sigma Research Program, est. April 1, 2026.",
    }
    set_metadata(dep_id, meta)
    save_result("Beyond_Bayes_DCII", dep_id, meta["title"])
    return dep_id

# ── RECORD 5: Complete TI Sigma Paper Archive ─────────────────────────────────

def upload_full_archive():
    banner("RECORD 5 — Complete TI Sigma Paper Archive (Master Collection)")

    dep_id = create_deposit()

    # Upload all key papers + Lean files as a comprehensive archive
    priority_papers = [
        "papers/TI_SIGMA_FOUNDING_CHARTER.md",
        "papers/TI_SIGMA_URB_MASTER_CATALOG.md",
        "papers/URB_537_538_COLLATZ_NU2_FORMAL_PAPER.md",
        "papers/COLLATZ_ARXIV_SUBMISSION.tex",
        "papers/BEYOND_BAYES_TI_SIGMA_EPISTEMOLOGY.md",
        "papers/DPES_DEFAULT_PHILOSOPHICAL_EATING_STRATEGY.md",
        "papers/urb_576_gile_weights_origins_confirmation.md",
        "papers/urb_577_gile_universal_operationalization.md",
        "papers/urb_578_relational_value_low_gil_social_norms.md",
        "papers/urb_575_weighted_bok_gile_proportional.md",
        "papers/urb_574_icell_bok_photonic_gile_aesthetic.md",
        "papers/urb_573_bok_verisyn_unified_synthesis.md",
        "papers/LEAN4_AUDIT_REPORT_APR2026.md",
        "papers/TI_SIGMA_FOUNDING_ANNOUNCEMENT.md",
        "lean4_collatz/CollatzNu2.lean",
        "lean4/Collatz.lean",
        "lean4/BSD.lean",
        "lean4/YangMills.lean",
        "lean4/NavierStokes.lean",
        "lean4/Hodge.lean",
        "lean4/PvsNP.lean",
        "lean4/RiemannUOP.lean",
        "lean4/BeingTheorem.lean",
    ]
    for f in priority_papers:
        upload_file(dep_id, f)

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": "Tralse Informationalism (TI Sigma) — Complete Research Archive, April 2026",
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Complete research archive for the Tralse Informationalism (TI Sigma)
            research program as of its official founding date, April 1, 2026.</p>

            <p><strong>TI Sigma</strong> holds that information is the primary substance
            of reality, that truth has five irreducible values (TRUE / TRALSE+ / TRALSE /
            TRALSE− / FALSE), and that consciousness has four measurable dimensions:
            Goodness (G=√2−1≈0.42), Intuition (I=0.25), Love (L≈0.18), Environment (E=0.15)
            — the GILE framework.</p>

            <p><strong>Archive contents:</strong></p>
            <ul>
              <li>TI Sigma Founding Charter (official founding document, April 1, 2026)</li>
              <li>Complete URB Master Catalog (578 Unified Research Blocks)</li>
              <li>ν₂ Countdown Theorem — formally verified Collatz result (Lean 4, 11 theorems, 0 gaps)</li>
              <li>arXiv LaTeX submission for the Collatz paper</li>
              <li>GILE Framework papers (URBs #573–578)</li>
              <li>Beyond Bayes: Domain-Calibrated Intuitive Inference (philosophy paper)</li>
              <li>DPES — Default Philosophical Eating Strategy (meta-cognitive protocol)</li>
              <li>Lean 4 source files: CollatzNu2.lean, Collatz.lean, + Millennium formalizations</li>
              <li>Complete Lean 4 audit report</li>
            </ul>

            <p>All mathematical results are formally verified or clearly labeled as experimental.
            All code is Apache 2.0. All papers are CC BY 4.0.</p>
        """).strip(),
        "keywords": [
            "Tralse Informationalism", "TI Sigma", "GILE framework", "five-valued logic",
            "TRALSE", "Collatz conjecture", "Lean 4", "formal verification",
            "consciousness", "philosophy of mind", "Bayesian epistemology",
            "Millennium Prize Problems", "number theory", "2-adic valuation"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": "Master archive. TI Sigma Research Program founded April 1, 2026 by Brandon Emerick.",
    }
    set_metadata(dep_id, meta)
    save_result("TI_Sigma_Complete_Archive", dep_id, meta["title"])
    return dep_id

# ── Main ───────────────────────────────────────────────────────────────────────

def main():
    mode = "🔴 LIVE (real Zenodo)" if LIVE else "🟡 SANDBOX (test — no real DOIs)"
    print(f"\n{'='*60}")
    print(f"  TI SIGMA — ZENODO UPLOAD SESSION")
    print(f"  Mode: {mode}")
    print(f"  Time: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*60}")

    if not LIVE:
        print("\n  ℹ️  Running on SANDBOX. To upload to real Zenodo, use:")
        print("       python zenodo_upload.py --live\n")

    # Verify token works
    r = requests.get(f"{BASE}/deposit/depositions", headers=HEADERS)
    if r.status_code == 401:
        print("\n❌  Invalid token. Check your ZENODO_TOKEN secret.")
        sys.exit(1)
    print(f"\n  ✅ Token verified. Connected to {'Zenodo' if LIVE else 'Zenodo Sandbox'}.")

    # Run all 5 uploads
    try:
        upload_collatz()
        time.sleep(1)
        upload_millennium()
        time.sleep(1)
        upload_gile_urbs()
        time.sleep(1)
        upload_philosophy()
        time.sleep(1)
        upload_full_archive()
    except requests.HTTPError as e:
        print(f"\n❌  HTTP Error: {e}")
        print(f"    Response: {e.response.text[:500]}")
        sys.exit(1)

    # Save results
    with open("zenodo_upload_results.json", "w") as f:
        json.dump(RESULTS, f, indent=2)

    # Final summary
    banner("✅ ALL DRAFTS CREATED SUCCESSFULLY")
    print(f"\n  {'🌐' if LIVE else '🧪'} {'Real' if LIVE else 'Sandbox'} Zenodo drafts:\n")
    for r in RESULTS:
        print(f"  [{r['record']}]")
        print(f"    {r['title'][:65]}...")
        print(f"    → {r['draft_url']}\n")

    print("  📋 Full results saved to: zenodo_upload_results.json")
    print("\n  NEXT STEPS:")
    print("  1. Open each URL above in your browser")
    print("  2. Review the metadata and files in each draft")
    print("  3. Click PUBLISH on each one to get permanent DOIs")
    if not LIVE:
        print("\n  ⚡ When satisfied, run:  python zenodo_upload.py --live")
    else:
        print("\n  🎉 Once published, your DOIs will be permanent!")
        print("     Update CollatzNu2.lean header + video scripts with the DOIs.")

if __name__ == "__main__":
    main()
