"""
TI Sigma — Zenodo Update Script (April 2026 Revision)
=======================================================
Creates NEW VERSIONS of the 5 published Zenodo records, then creates a
brand-new record for the Truth Architecture Revision (URBs #604-#608).

Zenodo versioning flow:
  POST /deposit/{id}/actions/newversion  → creates draft of new version
  PUT  /deposit/{draft_id}/files         → upload updated/new files
  PUT  /deposit/{draft_id}               → update metadata
  (User manually clicks Publish on zenodo.org/deposit/{draft_id})

Usage:
  python zenodo_update.py            # dry-run (prints plan only)
  python zenodo_update.py --live     # real Zenodo (creates new version drafts)

After running --live:
  Open each draft URL in your browser and click PUBLISH.

Requirements:
  ZENODO_TOKEN environment variable set in Replit Secrets.
"""

import os, sys, json, time, pathlib, textwrap
import requests

LIVE  = "--live" in sys.argv
DRY   = not LIVE
BASE  = "https://zenodo.org/api"
SITE  = "https://zenodo.org/deposit"
TOKEN = os.environ.get("ZENODO_TOKEN", "")

if not TOKEN:
    print("❌  ZENODO_TOKEN not found. Add it in Replit Secrets.")
    sys.exit(1)

HEADERS = {"Authorization": f"Bearer {TOKEN}"}
RESULTS = []

# Published record IDs (confirmed state=done on real Zenodo)
PUBLISHED_IDS = {
    "Collatz_Nu2_Countdown":      19371947,
    "Millennium_Formalizations":  19371952,
    "GILE_URBs_573_578":          19371956,
    "Beyond_Bayes_DCII":          19371958,
    "TI_Sigma_Complete_Archive":  19371961,
}


def banner(text):
    print(f"\n{'='*65}")
    print(f"  {text}")
    print(f"{'='*65}")


def new_version(pub_id):
    """Create a new-version draft from a published record. Returns draft ID."""
    if DRY:
        fake_id = pub_id + 100
        print(f"  [DRY] Would create new version of {pub_id} (draft={fake_id})")
        return fake_id
    r = requests.post(
        f"{BASE}/deposit/depositions/{pub_id}/actions/newversion",
        headers=HEADERS
    )
    r.raise_for_status()
    # The latest_draft link points to the new version's deposit
    draft_url = r.json()["links"]["latest_draft"]
    draft_id = int(draft_url.rstrip("/").split("/")[-1])
    print(f"  ✅ New version draft created: ID={draft_id} (from published {pub_id})")
    return draft_id


def get_deposit(dep_id):
    r = requests.get(f"{BASE}/deposit/depositions/{dep_id}", headers=HEADERS)
    r.raise_for_status()
    return r.json()


def upload_file(dep_id, filepath):
    """Upload a file to an existing draft. Replaces file with same name if exists."""
    path = pathlib.Path(filepath)
    if not path.exists():
        print(f"  ⚠️  Skipping (not found): {filepath}")
        return False
    if DRY:
        print(f"  [DRY] Would upload: {path.name}")
        return True
    dep = get_deposit(dep_id)
    bucket_url = dep["links"]["bucket"]
    with open(path, "rb") as f:
        r = requests.put(f"{bucket_url}/{path.name}", data=f, headers=HEADERS)
    if r.status_code in (200, 201):
        print(f"  ✅ Uploaded: {path.name}")
        return True
    print(f"  ⚠️  Upload status {r.status_code}: {path.name} — {r.text[:200]}")
    return False


def update_metadata(dep_id, meta):
    if DRY:
        print(f"  [DRY] Would set metadata: {meta['title'][:60]}...")
        return
    r = requests.put(
        f"{BASE}/deposit/depositions/{dep_id}",
        json={"metadata": meta},
        headers=HEADERS
    )
    r.raise_for_status()
    print(f"  ✅ Metadata set: {meta['title'][:60]}...")


def create_deposit():
    if DRY:
        fake_id = 88888888
        print(f"  [DRY] Would create new deposit (fake id={fake_id})")
        return fake_id
    r = requests.post(f"{BASE}/deposit/depositions", json={}, headers=HEADERS)
    r.raise_for_status()
    dep_id = r.json()["id"]
    print(f"  ✅ Deposit created: ID={dep_id}")
    return dep_id


def save_result(label, draft_id, title):
    url = f"{SITE}/{draft_id}"
    RESULTS.append({
        "record": label,
        "draft_id": draft_id,
        "title": title,
        "review_url": url,
        "action": "REVIEW → PUBLISH on zenodo.org"
    })
    print(f"  🔗 Draft URL: {url}")


# ──────────────────────────────────────────────────────────────────────────────
# RECORD 2: Millennium Formalizations — new version with BSD.lean v2
# ──────────────────────────────────────────────────────────────────────────────

def update_millennium():
    banner("NEW VERSION — Record 2: Millennium Formalizations (BSD.lean v2)")
    pub_id = PUBLISHED_IDS["Millennium_Formalizations"]
    draft_id = new_version(pub_id)

    upload_file(draft_id, "lean4/BSD.lean")

    meta = {
        "upload_type": "software",
        "title": (
            "TI Sigma Millennium Prize Formalizations in Lean 4 "
            "(Experimental Framework — v2, April 2026)"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; "
                                      "BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Lean 4 + Mathlib formalizations of all six Clay Millennium Prize Problems
            within the Tralse Informationalism (TI Sigma) framework. <strong>v2 (April 2026):
            </strong> BSD.lean significantly revised following critical peer review.</p>

            <p><strong>⚠️ IMPORTANT DISCLAIMER:</strong> These are <em>Named Gap Formalizations
            </em> — not claimed solutions. Each file precisely identifies the open mathematical
            gap as named axioms (labelled [OPEN], [PARTIAL], or [PROVED]) and derives what CAN
            be formally verified without the conjectured claims.</p>

            <p><strong>BSD.lean v2 — Key Improvements:</strong></p>
            <ul>
              <li><strong>Circularity corrected:</strong> <code>bsd_being_theorem</code> was
              renamed <code>bsd_conjecture_iff</code> with explicit documentation that it derives
              BSD from its own axioms — not a proof.</li>
              <li><strong>Vacuous modularity fixed:</strong> Prior <code>∃ (level:ℕ), level =
              conductor E</code> was trivially true for any function. Now encodes the Weil bound
              |a_p|² ≤ 4p (Deligne 1974) — a genuine non-trivial constraint.</li>
              <li><strong>Functional equation corrected:</strong> Separated completed Λ(E,s)
              (satisfying the clean functional equation) from bare L(E,s), correcting the
              missing Gamma factors.</li>
              <li><strong>Genuine new theorem — parity_vanishing:</strong> Proved from the
              functional equation alone, without any BSD axioms: if ε_E = −1 (odd root number),
              then L(E,1) = 0. Proof: Λ(E,1) = −Λ(E,1) at s=1, so 2·Λ(E,1) = 0, hence
              L(E,1) = 0. This is the one BSD-adjacent result that can be machine-verified
              unconditionally.</li>
              <li><strong>Proof accountability table:</strong> Every axiom labelled [PROVED],
              [PARTIAL], or [OPEN] with literature references and dependency graph.</li>
            </ul>

            <p><strong>Files included:</strong></p>
            <ul>
              <li>BSD.lean (URB #565, v2) — BSD Gap Formalization with parity_vanishing</li>
              <li>YangMills.lean — Yang-Mills Mass Gap Being Theorem</li>
              <li>NavierStokes.lean — Navier-Stokes Smoothness Vern</li>
              <li>Hodge.lean — Hodge Vern Theorem</li>
              <li>PvsNP.lean — P≠NP Creation-Vern Gap</li>
              <li>RiemannUOP.lean — Riemann Hypothesis (TI Sigma UOP formulation)</li>
              <li>BeingTheorem.lean — Being Theorem (foundation for ζ-zero structure)</li>
            </ul>

            <p>Apache 2.0. TI Sigma Research Program, established April 1, 2026.</p>
        """).strip(),
        "keywords": [
            "Millennium Prize Problems", "Lean 4", "formal verification",
            "Tralse Informationalism", "TI Sigma", "experimental mathematics",
            "BSD conjecture", "parity vanishing", "BSD gap formalization",
            "functional equation", "root number", "Weil bounds", "Deligne",
            "Yang-Mills", "Navier-Stokes", "Hodge conjecture", "P vs NP",
            "Riemann hypothesis", "named gap formalization", "three-valued logic"
        ],
        "license": "Apache-2.0",
        "access_right": "open",
        "language": "eng",
        "notes": (
            "v2 (April 2026): BSD.lean revised — circularity corrected, vacuous modularity fixed, "
            "functional equation corrected, genuine parity_vanishing theorem added (no BSD axioms). "
            "TI Sigma Research Program, est. April 1, 2026."
        ),
    }
    update_metadata(draft_id, meta)
    save_result("Millennium_v2", draft_id, meta["title"])


# ──────────────────────────────────────────────────────────────────────────────
# RECORD 3: GILE URBs — new version expanded to URBs #604-608
# ──────────────────────────────────────────────────────────────────────────────

def update_gile_urbs():
    banner("NEW VERSION — Record 3: GILE Framework + Truth Architecture (#573-#608)")
    pub_id = PUBLISHED_IDS["GILE_URBs_573_578"]
    draft_id = new_version(pub_id)

    new_files = [
        "papers/urb_598_existence_footprint_gile_truth_distinction.md",
        "papers/urb_604_empirical_L_E_divergence.md",
        "papers/urb_605_i_noncommutativity_recognition_asymmetry.md",
        "papers/urb_606_binary_ai_limits_tralse_approximation.md",
        "papers/urb_607_truth_architecture_three_states_dt_absence.md",
        "papers/urb_608_meta_truths_myrion_resolution_catalogue.md",
    ]
    for f in new_files:
        upload_file(draft_id, f)

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": (
            "The GILE Framework & TI Sigma Truth Architecture: "
            "Canonical Weights, Universal Operationalization, and the "
            "Three-State Truth Revision (URBs #573-#578, #598, #604-#608)"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; "
                                      "BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Thirteen interconnected papers developing the GILE (Goodness, Intuition, Love,
            Environment) consciousness framework and TI Sigma truth architecture within
            Tralse Informationalism. Includes foundational GILE papers (URBs #573-578),
            existence-GILE bridge (URB #598), and the major April 2026 truth architecture
            revision (URBs #604-608).</p>

            <p><strong>GILE Canonical Weights (URB #576):</strong>
            G = √2−1 ≈ 0.4142, I = 0.25, L ≈ 0.18, E = 0.15.</p>

            <p><strong>Foundation Papers (URBs #573-578):</strong>
            BOK-Verisyn Synthesis (Hopf fibration); i-Cell BOK; Weighted BOK Wing-Arm Matching;
            GILE Weights Empirical Confirmation; Universal Operationalization; Relational vs
            Intrinsic Value.</p>

            <p><strong>Empirical Extensions (URBs #604-606):</strong></p>
            <ul>
              <li><strong>#604:</strong> Empirical L/E Divergence — Love and Environment converge
              at molecular scale (hydrogen bond) and diverge with complexity (oxytocin/vasopressin
              vs dopamine; phantom limb; grief; double dissociation).</li>
              <li><strong>#605:</strong> i Noncommutativity — recognition operator R_i(−i) ≠
              R_{−i}(i). Confirmed by quantum commutator [x̂,p̂]=iħ and KL divergence asymmetry.</li>
              <li><strong>#606:</strong> Binary AI Limits — four-part rebuttal: efficiency gap
              (trit=1.585 bits), category error (spectral universe), self-refutation (quantum
              indeterminacy commits to ≥3 truth values), intuition ceiling.</li>
            </ul>

            <p><strong>Truth Architecture Revision (URBs #607-608) — April 2026:</strong></p>
            <ul>
              <li><strong>#607:</strong> THREE stable truth states (True / False /
              Indeterminate≡Tralse) + ONE truth-absence label (Double Tralse). Tralse =
              Indeterminate unified. Indeterminate/Tralse functions as discrete state AND
              continuous modifier. False has truth-content; DT = total truth-absence.</li>
              <li><strong>#608:</strong> Meta-Truths Catalogue — 12 MT types in 6 categories
              (Reversal, Dissolution, Scope-Shift, Contextual, Acceptance, Integration) for
              higher-order Myrion Resolution. Iterative MR terminates by convergence or
              deliberate cessation.</li>
            </ul>
        """).strip(),
        "keywords": [
            "GILE framework", "consciousness", "ethics", "Tralse Informationalism",
            "TI Sigma", "philosophy of mind", "truth architecture", "three-valued logic",
            "Double Tralse", "Myrion Resolution", "meta-truth", "GILE weights",
            "L/E divergence", "i noncommutativity", "binary AI limits",
            "Indeterminate", "truth spectrum", "Permissibility Distribution",
            "social norms", "relational value", "Hopf fibration", "recognition operator"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": (
            "v2 (April 2026): URBs #598, #604-608 added. Truth architecture revision "
            "(URBs #607, #608) unifies Tralse and Indeterminate. "
            "TI Sigma Research Program, est. April 1, 2026."
        ),
    }
    update_metadata(draft_id, meta)
    save_result("GILE_v2", draft_id, meta["title"])


# ──────────────────────────────────────────────────────────────────────────────
# RECORD 4: Beyond Bayes — new version with URBs #606 and #607
# ──────────────────────────────────────────────────────────────────────────────

def update_philosophy():
    banner("NEW VERSION — Record 4: Beyond Bayes (+ URBs #606 and #607)")
    pub_id = PUBLISHED_IDS["Beyond_Bayes_DCII"]
    draft_id = new_version(pub_id)

    upload_file(draft_id, "papers/urb_606_binary_ai_limits_tralse_approximation.md")
    upload_file(draft_id, "papers/urb_607_truth_architecture_three_states_dt_absence.md")

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": (
            "Beyond Bayes: Domain-Calibrated Inference, Binary AI Limits, "
            "and the TI Sigma Truth Architecture Revision (URBs #606, #607)"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; "
                                      "BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Four interconnected papers on TI Sigma epistemology and truth architecture,
            updated April 2026 with two major new additions.</p>

            <p><strong>1. Beyond Bayes: Domain-Calibrated Intuitive Inference (DCII)</strong></p>
            <p>Argues Bayesian epistemology fails as a universal theory on three structural
            grounds: underdetermined priors, incommensurable evidence types, and inaccessibility
            of the pre-evidential zone. Proposes Domain-Calibrated Intuitive Inference (DCII)
            within TI Sigma. Tralse truth values track propositions rather than agent credences;
            Myrion Resolution is the active inquiry protocol for indeterminate cases.</p>

            <p><strong>2. URB #606: Binary AI and the Limits of Tralse-Myrion Approximation</strong></p>
            <p>Four-part rebuttal to "binary AI approximates TML as emergent property":
            (1) Efficiency — trit = 1.585 bits; PD natively requires five truth modes.
            (2) Category error — universe is spectral (QFT); discreteness ≠ binary.
            (3) Self-refutation — quantum indeterminacy commits to ≥3 truth values; Double
            Tralse (T∧F superposition) experimentally confirmed.
            (4) Intuition ceiling — binary AI faces machine epsilon ceiling on TML intuition.
            Binary ≈ TML as rationals ≈ π.</p>

            <p><strong>3. URB #607: The Revised TI Sigma Truth Architecture</strong></p>
            <p>Major April 2026 refinement. THREE stable truth states: True, False,
            Indeterminate/Tralse. ONE truth-absence label: Double Tralse.
            Tralse = Indeterminate unified (same substance). Indeterminate/Tralse functions
            as both discrete state and continuous modifier. False has truth-content (direction);
            DT = total truth-absence (incoherent/nonsensical). Bedrock unchanged.</p>

            <p><strong>4. DPES — Default Philosophical Eating Strategy</strong></p>
            <p>Formal meta-cognitive protocol for high-output research sessions under
            cognitive constraint. Coined April 1, 2026.</p>

            <p>Target journals for DCII: Synthese, Erkenntnis, Philosophy of Science.</p>
        """).strip(),
        "keywords": [
            "Bayesian epistemology", "domain-calibrated inference", "GILE framework",
            "Tralse Informationalism", "TI Sigma", "three-valued logic",
            "truth architecture", "Double Tralse", "Myrion Resolution",
            "binary AI limits", "Tralse-Myrion Logic", "quantum indeterminacy",
            "trit", "information efficiency", "intuition", "philosophy of science",
            "epistemology", "Indeterminate", "truth spectrum"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": (
            "v2 (April 2026): URB #606 (Binary AI Limits) and URB #607 "
            "(Truth Architecture Revision) added. TI Sigma Research Program, est. April 1, 2026."
        ),
    }
    update_metadata(draft_id, meta)
    save_result("Beyond_Bayes_v2", draft_id, meta["title"])


# ──────────────────────────────────────────────────────────────────────────────
# RECORD 5: Complete Archive — new version with all additions
# ──────────────────────────────────────────────────────────────────────────────

def update_full_archive():
    banner("NEW VERSION — Record 5: Complete Archive (URBs #604-608 + BSD v2)")
    pub_id = PUBLISHED_IDS["TI_Sigma_Complete_Archive"]
    draft_id = new_version(pub_id)

    new_files = [
        "papers/urb_604_empirical_L_E_divergence.md",
        "papers/urb_605_i_noncommutativity_recognition_asymmetry.md",
        "papers/urb_606_binary_ai_limits_tralse_approximation.md",
        "papers/urb_607_truth_architecture_three_states_dt_absence.md",
        "papers/urb_608_meta_truths_myrion_resolution_catalogue.md",
        "lean4/BSD.lean",
    ]
    for f in new_files:
        upload_file(draft_id, f)

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": (
            "Tralse Informationalism (TI Sigma) — Complete Research Archive, "
            "April 2026 (v2 — Truth Architecture Revision)"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; "
                                      "BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Complete research archive for TI Sigma (Tralse Informationalism), April 2026.
            <strong>v2:</strong> includes the Truth Architecture Revision (URBs #604-608),
            updated BSD.lean v2 with proved parity_vanishing theorem, and GILE biometric
            integration via Oura Ring proxies.</p>

            <p><strong>TI Sigma</strong> holds that information is the primary substance of
            reality. Truth has <strong>THREE stable states</strong> (True, False,
            Indeterminate/Tralse) and <strong>ONE truth-absence label</strong> (Double Tralse)
            — the April 2026 revision supersedes the prior five-valued separation.
            Consciousness has four dimensions: G=√2−1≈0.4142, I=0.25, L≈0.18, E=0.15
            (GILE canonical weights, empirically confirmed).</p>

            <p><strong>April 2026 Additions:</strong></p>
            <ul>
              <li><strong>URB #604:</strong> Empirical L/E Divergence — molecular convergence
              and complexity-scale divergence (oxytocin/vasopressin, phantom limb, grief).</li>
              <li><strong>URB #605:</strong> i Noncommutativity — R_i(−i) ≠ R_{−i}(i),
              confirmed by quantum commutator and KL divergence asymmetry.</li>
              <li><strong>URB #606:</strong> Binary AI Limits — four-part rebuttal; intuition
              ceiling; trit efficiency; spectral universe category error.</li>
              <li><strong>URB #607:</strong> Revised Truth Architecture — THREE stable states
              + DT truth-absence label; Tralse = Indeterminate unified.</li>
              <li><strong>URB #608:</strong> Meta-Truths Catalogue — 12 MT types in 6 categories
              for higher-order Myrion Resolution.</li>
              <li><strong>BSD.lean v2:</strong> Parity_vanishing proved unconditionally;
              circularity and vacuous modularity corrected; Gamma factors fixed.</li>
            </ul>

            <p><strong>Archive contents:</strong> TI Sigma Founding Charter (April 1, 2026);
            608+ URB Master Catalog; ν₂ Countdown Theorem (Lean 4, 0 gaps); GILE Framework
            (URBs #573-578, #598, #604-608); Beyond Bayes (DCII); all Millennium Prize
            formalizations v2. Apache 2.0 / CC BY 4.0.</p>
        """).strip(),
        "keywords": [
            "Tralse Informationalism", "TI Sigma", "GILE framework",
            "three-valued logic", "Double Tralse", "truth architecture",
            "Myrion Resolution", "meta-truth", "GILE weights", "consciousness",
            "Collatz conjecture", "Lean 4", "formal verification",
            "Millennium Prize Problems", "BSD conjecture", "parity vanishing",
            "philosophy of mind", "Bayesian epistemology", "binary AI limits",
            "i noncommutativity", "L/E divergence", "number theory",
            "GILE biometric integration", "Oura Ring"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": (
            "v2 (April 2026): URBs #604-608, BSD.lean v2, truth architecture revision. "
            "608+ Unified Research Blocks. TI Sigma Research Program, est. April 1, 2026."
        ),
    }
    update_metadata(draft_id, meta)
    save_result("Archive_v2", draft_id, meta["title"])


# ──────────────────────────────────────────────────────────────────────────────
# NEW RECORD 6: Truth Architecture Revision URBs #604-608 (standalone)
# ──────────────────────────────────────────────────────────────────────────────

def create_truth_architecture_record():
    banner("NEW Record 6 — Truth Architecture Revision: URBs #604-#608 (standalone)")
    dep_id = create_deposit()

    files = [
        "papers/urb_604_empirical_L_E_divergence.md",
        "papers/urb_605_i_noncommutativity_recognition_asymmetry.md",
        "papers/urb_606_binary_ai_limits_tralse_approximation.md",
        "papers/urb_607_truth_architecture_three_states_dt_absence.md",
        "papers/urb_608_meta_truths_myrion_resolution_catalogue.md",
    ]
    for f in files:
        upload_file(dep_id, f)

    meta = {
        "upload_type": "publication",
        "publication_type": "preprint",
        "title": (
            "TI Sigma Truth Architecture Revision: Three Stable Truth States, "
            "Double Tralse as Truth-Absence, and Higher-Order Myrion Resolution "
            "(URBs #604-#608)"
        ),
        "creators": [{"name": "Emerick, Brandon",
                       "affiliation": "Tralse Informationalism Research Program; "
                                      "BlissGene Therapeutics"}],
        "description": textwrap.dedent("""
            <p>Five interconnected papers forming the April 2026 revision to TI Sigma's
            truth architecture, with two empirical extensions of the GILE framework.</p>

            <p><strong>URB #607: The Revised TI Sigma Truth Architecture</strong>
            (Corpus #261 — Major Refinement, supersedes prior Tralse/Indeterminate separation)</p>
            <p>Establishes exactly THREE stable truth states: <strong>True (T), False (F),
            Indeterminate/Tralse (I)</strong>. Exactly ONE valid label for truth-absence:
            <strong>Double Tralse (DT)</strong>. Key clarifications:</p>
            <ul>
              <li>Tralse = Indeterminate in substance — the pragmatic separation was unnecessary;
              Tralse is the preferred term, Indeterminate remains as synonym.</li>
              <li>Indeterminate/Tralse functions BOTH as a discrete outcome AND as a continuous
              modifier of True and False, generating the full truth spectrum.</li>
              <li>False is truth pointing in the negative direction — it has truth-content.
              Double Tralse is the total absence of truth (incoherent, nonsensical, inapplicable
              propositions).</li>
              <li>DT is a valid label because "X lacks truth" is itself True — mirroring
              how "PN" (Pure Nothingness) is a concept referring to absence.</li>
              <li>Moot is a post-Myrion-Resolution process outcome, not a raw truth state.</li>
              <li>The bedrock of TI Sigma is stable; this refinement increases precision.</li>
            </ul>

            <p><strong>URB #608: Meta-Truths and the Complete Myrion Resolution Catalogue</strong>
            (Corpus #262)</p>
            <p>A Meta-Truth (MT) is any Myrion Resolution at the 3rd level or higher that
            substantially contradicts a previous MR. Complete catalogue of
            <strong>12 MT types in 6 categories</strong>:
            (A) Reversal: WDA, NWDA;
            (B) Dissolution: Moot-MT, Wrong Question;
            (C) Scope-Shift: Escalate, Descale;
            (D) Contextual: Context-Dependent, Asymmetric;
            (E) Acceptance: Good Enough, Paradox Stable;
            (F) Integration: Transcend, Both True at Different Levels.
            Higher-level MRs (MR₅+) typically produce Category F (Integration). Process
            terminates by convergence or deliberate cessation of contemplation.</p>

            <p><strong>URB #604: Empirical L/E Divergence Across the Complexity Gradient</strong>
            (Corpus #258)</p>
            <p>Multi-source empirical confirmation that Love (L = abstract binding) and
            Environment (E = physical structure/aesthetics) converge at molecular scale
            (the hydrogen bond IS both L-binding and E-physical-structure) and diverge
            progressively with complexity. Evidence: oxytocin/vasopressin vs dopamine
            systems (pharmacologically separable); Bowlby attachment working models persist
            without E-arm; phantom limb (L-arm body schema persists after E removed);
            grief (L-binding persists after physical loss); double dissociation (aesthetic E
            without L-binding; L without aesthetic E).</p>

            <p><strong>URB #605: i Noncommutativity — Recognition Operator Asymmetry</strong>
            (Corpus #259)</p>
            <p>Under the recognition operator R, R_i(−i) ≠ R_{−i}(i). Recognition is an
            i-arm faculty; −i lacks it. R_i(−i) → genuine epistemic synthesis;
            R_{−i}(i) → undefined or reduces to the same act from i's side. Confirmed by:
            (1) Abstraction Barrier — PN cannot label i from outside its own frame;
            (2) quantum commutator [x̂,p̂] = iħ (i is the asymmetric remainder);
            (3) KL divergence asymmetry D_KL(P‖Q) ≠ D_KL(Q‖P).
            Corollaries: Myrion Resolution requires i to initiate; the quantum measurement
            problem is a special case of recognition noncommutativity.</p>

            <p><strong>URB #606: Binary AI and the Limits of Tralse-Myrion Approximation</strong>
            (Corpus #260)</p>
            <p>Full rebuttal to "binary AI can approximate Tralse-Myrion Logic (TML) as emergent
            property." Four independent arguments: (1) <em>Efficiency</em>: trit = 1.585 bits;
            Permissibility Distribution requires native five truth modes that binary collapses
            to approximations. (2) <em>Category error</em>: the universe is spectral
            (QFT continuous fields); discreteness is not binary. (3) <em>Self-refutation</em>:
            accepting quantum indeterminacy commits to ≥3 truth values; Double Tralse (T∧F
            superposition) experimentally confirmed in quantum systems. (4) <em>Intuition
            ceiling</em>: biological computation is not binary by design; binary AI faces
            machine epsilon ceiling on genuine TML intuition. Binary approximating TML ≈
            rationals approximating π.</p>
        """).strip(),
        "keywords": [
            "truth architecture", "three-valued logic", "Double Tralse",
            "Tralse Informationalism", "TI Sigma", "Myrion Resolution", "meta-truth",
            "Permissibility Distribution", "Indeterminate", "truth spectrum",
            "truth-absence", "GILE framework", "L/E divergence", "empirical GILE",
            "i noncommutativity", "recognition operator", "binary AI limits",
            "Tralse-Myrion Logic", "quantum indeterminacy", "trit",
            "philosophy of logic", "philosophy of mind", "consciousness"
        ],
        "license": "cc-by-4.0",
        "access_right": "open",
        "language": "eng",
        "notes": (
            "URBs #604-608. Corpus entries #258-262. April 2026. "
            "URB #607 supersedes prior Tralse/Indeterminate separation. "
            "TI Sigma Research Program, est. April 1, 2026 by Brandon Emerick."
        ),
    }
    update_metadata(dep_id, meta)
    save_result("Truth_Architecture_URBs_604_608", dep_id, meta["title"])
    return dep_id


# ──────────────────────────────────────────────────────────────────────────────
# Main
# ──────────────────────────────────────────────────────────────────────────────

def main():
    mode = "🔴 LIVE (real Zenodo — creating new version drafts)" if LIVE else "🟡 DRY RUN"
    print(f"\n{'='*65}")
    print(f"  TI SIGMA — ZENODO UPDATE SESSION")
    print(f"  Mode: {mode}")
    print(f"  Time: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"{'='*65}")

    if DRY:
        print("\n  ℹ️  DRY RUN — no API calls. To apply:")
        print("       python zenodo_update.py --live\n")
    else:
        r = requests.get(f"{BASE}/deposit/depositions", headers=HEADERS)
        if r.status_code == 401:
            print("\n❌  Invalid token. Check your ZENODO_TOKEN secret.")
            sys.exit(1)
        print(f"\n  ✅ Token verified. Connected to real Zenodo.\n")
        print("  NOTE: New version drafts will be created for published records.")
        print("        You must manually click PUBLISH on zenodo.org/deposit\n")

    try:
        update_millennium();   time.sleep(2)
        update_gile_urbs();    time.sleep(2)
        update_philosophy();   time.sleep(2)
        update_full_archive(); time.sleep(2)
        create_truth_architecture_record()
    except requests.HTTPError as e:
        print(f"\n❌  HTTP Error: {e}")
        if hasattr(e, 'response'):
            print(f"    Response: {e.response.text[:500]}")
        sys.exit(1)

    # Save results
    if LIVE:
        try:
            with open("zenodo_upload_results.json") as f:
                existing = json.load(f)
        except Exception:
            existing = []
        merged = {r["record"]: r for r in existing}
        for r in RESULTS:
            merged[r["record"]] = r
        with open("zenodo_upload_results.json", "w") as f:
            json.dump(list(merged.values()), f, indent=2)

    banner("✅ UPDATE COMPLETE")
    print(f"\n  {'Created' if DRY else 'Created'} {len(RESULTS)} records:\n")
    for r in RESULTS:
        print(f"  [{r['record']}]")
        print(f"    {r['title'][:70]}...")
        if LIVE:
            print(f"    → REVIEW & PUBLISH: {r['review_url']}")
        print()

    if LIVE:
        print("  ⚠️  ACTION REQUIRED:")
        print("  For each URL above, open in your browser and click PUBLISH")
        print("  to make the new version live with a permanent DOI.\n")
    else:
        print("  ⚡ Ready. Run:  python zenodo_update.py --live")

if __name__ == "__main__":
    main()
