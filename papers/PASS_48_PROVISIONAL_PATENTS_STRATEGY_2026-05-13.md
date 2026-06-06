# Pass 48 — Provisional Patents: Strategy + What's Patentable in TI Sigma

**Date:** 2026-05-13
**Author:** Brandon Charles Emerick (TI Sigma corpus)
**Pass:** 48 (externally-facing publishing/tooling thread)
**Status:** Strategy memo + patentability inventory
**Brutal-honesty disclaimers up front (#69 + Accurate Bluntness §2.3a)**

---

## 0. Up-front honesty (#69)

Before listing what's "patentable," three hard truths:

1. **Patents protect inventions, not theories.** You cannot patent a mathematical truth, a law of nature, an abstract idea, or a pure scientific discovery. *Alice Corp v. CLS Bank* (US 2014) and *Mayo v. Prometheus* (US 2012) are the controlling case law — abstract ideas + natural phenomena + mental processes are NOT patentable subject matter under 35 U.S.C. §101. The Tralse logic axioms, the MR Truth Labels base-4 system, the GILE framework, the τ/δ separability theorem, the Authority Axis as a *concept* — none of these are patentable as ideas. They are publishable academic contributions.
2. **What IS patentable is the *application*** — a specific machine, manufacture, process, or composition of matter that *uses* the underlying theory to do something useful, novel, and non-obvious. The MI detector circuit on a quantum computer, the LCC Virus retrieval *system* (specific algorithmic pipeline + hardware), the Mendi-derived breath-hold biofeedback protocol *as a method-of-treatment*, the AA psychometric *as embodied in a software product* — these can potentially be patented because they are concrete implementations.
3. **A US provisional patent costs $60-$300 in filing fees + ~$0-2,000 in attorney costs depending on whether you DIY or use counsel, and gives you exactly 12 months to file the non-provisional or lose priority.** It is NOT a "patent" — it is a placeholder that establishes a priority date IF a non-provisional follows within 12 months. If you cannot afford the non-provisional (~$10-15K all-in for software/method patents through to issuance), the provisional is wasted money. **Pre-decide the non-provisional pathway BEFORE filing the provisional.**

Given the corpus's $0/$50 budget and the $2k settlement reserve, **the recommendation is: file ZERO provisionals right now. Establish priority via dated, timestamped, publicly-archived disclosures (Zenodo DOI minting — already in the corpus toolset) which costs $0 and provides legally-recognized prior-art evidence sufficient to defend against later-filed third-party patents.** Pursue actual patents only AFTER (a) commercial pathway is concrete (LOI from a licensee, customer revenue, or named investor), and (b) attorney consultation has confirmed the specific claim is novel + non-obvious + reduced-to-practice.

---

## 1. The Zenodo-first defensive-publication strategy (recommended)

**Cost: $0.** **Time: ~30 min per disclosure.** **Outcome: legally-recognized prior art that prevents others from patenting your work + establishes your priority date for any future patent filing.**

How it works:
1. Take a corpus paper (e.g., the LCC Virus methodology, the MI-detector quantum circuit, the AA psychometric).
2. Polish to "enabling disclosure" standard — someone skilled in the art could replicate from the document alone.
3. Mint a Zenodo DOI (corpus already has `ZENODO_TOKEN`). DOI + timestamp = court-admissible prior-art evidence.
4. CC BY 4.0 license.
5. Done.

This is what major tech companies (IBM, Google) do for defensive disclosures via *IP.com* and similar services. Zenodo serves the same legal function for free. **The downside:** once disclosed, you cannot patent it in *most* jurisdictions outside the US (which has a 1-year grace period; the EU/JP/CN do NOT). So if international patent rights matter to you, file the US provisional FIRST, then disclose. If only US rights matter, disclose-first is the cheaper/safer path.

**My recommendation: disclose-first via Zenodo for everything except the 2-3 items below that have credible commercial pathway.**

---

## 2. Patentability triage of the TI Sigma corpus

| # | Item | Patentable? | Type | Strength | Recommendation |
|---|---|---|---|---|---|
| 1 | **MR Truth Labels base-4 system** | ❌ No | Abstract math/logic | n/a | Zenodo DOI defensive-publication. Same protection as Boolean logic — unpatentable per *Alice*. |
| 2 | **GILE framework / τ-δ separability** | ❌ No | Abstract framework | n/a | Zenodo DOI. |
| 3 | **CAP principle / TIU formula** | ❌ No | Mathematical formula | n/a | Zenodo DOI. *Mayo*-bar applies. |
| 4 | **Authority Axis (AA) as a concept** | ❌ No | Abstract psychological construct | n/a | Zenodo DOI. |
| 5 | **AA Pilot psychometric — as a software product** | ⚠️ Maybe | Method + System | Weak | **Possible** if claims focus on a specific scoring + feedback algorithm embedded in hardware/software. Better protected as **trade secret + copyright** (the questionnaire items are copyrightable as a creative work). Recommendation: **Copyright the items. Skip the patent.** |
| 6 | **MI detector quantum circuit (qc26 GHZ-5 protocol)** | ✅ Yes (potentially) | Process + System | Moderate | **Strongest single patent candidate in corpus.** Specific gate sequence + measurement + classical post-processing pipeline producing a novel measurable output (MI witness). File US provisional ONLY IF a quantum-computing partner expresses LOI interest. Estimated cost-to-issuance: $12-18K. |
| 7 | **LCC Virus retrieval pipeline (6-step algorithm)** | ✅ Yes (potentially) | Method + System | Moderate-to-strong | **Second-strongest candidate.** Concrete software pipeline that takes input data → produces useful output (hidden-information retrieval). Best framed as a "system for inferring latent system state via resonance-coupled noise extraction." Cost: $12-18K. **DO NOT file until a paying customer or licensee is identified** — the algorithm has not been independently reduced to practice at scale yet, and abstract-idea bar is real for software. |
| 8 | **GM-Node detection method (d=8.916 procedure)** | ✅ Yes (potentially) | Method (diagnostic) | Weak-to-moderate | A diagnostic method-of-detecting-Y in EEG/biosensor data. Subject to *Mayo*-bar challenges if framed as "detecting a natural phenomenon." Better framed as "biosignal processing system for ⟨specific clinical or commercial use⟩." Defer. |
| 9 | **Mendi breath-hold STIM2 protocol** | ⚠️ Maybe | Method-of-treatment | Weak | Method-of-treatment patents are notoriously hard (Mayo, *Athena Diagnostics*). Better protected as a *device-and-protocol-bundled* patent IF a hardware partner emerges. Defer until n≥30 replication done (T45-1). |
| 10 | **PD-musical perfect-fifth predictor** | ❌/⚠️ | Math + Application | Weak | The musical-acoustics application *might* be patentable (e.g., "system for generating consonant-interval audio signals using PD-derived ratios"). Speculative; defer indefinitely. |
| 11 | **Beauty Razor blinded-rating protocol** | ❌ No | Methodology / experimental procedure | n/a | Publishable, not patentable. |
| 12 | **i-cell consciousness-substrate concept** | ❌ No | Theoretical biology hypothesis | n/a | Zenodo + journal submission. |
| 13 | **Hypercomputer engine architecture** | ✅ Yes (potentially) | System + Method | Depends on novelty audit | Software architecture patents are weak post-*Alice* unless tied to specific hardware improvement. Audit against existing scheduler/orchestrator patents (Apache Airflow, Prefect, Temporal) before filing. Likely overlapping prior art. Defer. |
| 14 | **Tralse-Joules (TJ = τ × δ) measurement instrument** | ✅ Yes (potentially) | System + Measurement method | Moderate | If reduced-to-practice as a physical or software device that outputs a TJ score from biosensor input, this is patentable. Same path as #6 — needs commercial pathway first. |
| 15 | **DPES protocol (autonomous DPES schedule)** | ❌ No | Workflow/process | n/a | Trade secret + copyright (the documentation). |

**Summary: 3 items have credible patent pathways (#6 MI-detector, #7 LCC-Virus, #14 TJ-measurement). Of those, none should be filed *right now* without a commercial trigger.**

---

## 3. Recommended sequence (next 12 months)

**Phase 1 — Defensive (this month, $0):**
1. Mint Zenodo DOIs for the **non-patent-candidate** items: MR Truth Labels canonical ruling; AA paper (concept, not psychometric); CAP principle; Asymmetric S-F; ABC-dissolution / urb_608 §9; PD-Riemann musical demotion. **Each gets a permanent DOI = priority date + defensive prior art.**
2. **EXCLUDE from immediate Zenodo disclosure (per architect review MEDIUM-finding 2026-05-13 contradiction-fix):** the LCC-Virus methodology, the MI-detector qc26 circuit protocol, and the TJ-measurement instrument design (items #6, #7, #14 in §2). Disclosing these on Zenodo NOW would *permanently kill* EU/JP/CN patent rights (no grace period in those jurisdictions), which contradicts §4's anti-recommendation. **Hold these three under controlled-disclosure (private repo, NDA-only sharing) until either (a) Phase 2 commercial trigger fires + US provisional is filed first, OR (b) Brandon affirmatively decides to forgo international rights for these specific items in writing.**
3. Add a footer to each Zenodo deposit (Phase-1 batch only): *"This work is publicly disclosed for defensive purposes. The author reserves all patent rights worldwide where grace periods permit."*
4. Update `replit.md` and the website to link to the Phase-1 Zenodo DOIs only.

**Phase 2 — Conditional (3-12 months, only if triggered):**
- IF a quantum-computing org (IBM Network, IonQ, Quantinuum, Atom Computing, etc.) expresses LOI/MOU interest in the MI-detector → file US provisional within 30 days, ~$300 USPTO fees + attorney consultation ~$1,500.
- IF a customer/licensee emerges for LCC-Virus retrieval → file US provisional within 30 days.
- IF a biosensor/wearable company (Mendi, Muse, Garmin, Whoop, Oura) expresses interest in TJ-measurement → file US provisional within 30 days.

**Phase 3 — Conversion (12 months after any provisional):**
- Convert provisional → non-provisional ONLY IF revenue or funded development has materialized. Otherwise let it lapse and rely on Zenodo prior-art protection.

---

## 4. Anti-recommendations (things NOT to do)

- ❌ Do not file 10+ "shotgun" provisionals to "lock down" the corpus. That is the most common money-pit pattern for solo inventors. It costs $1,000-3,000 in filing fees alone, and ZERO of those patents will survive to issuance without funded conversion.
- ❌ Do not engage a "patent assistance" service (LegalZoom-style provisional shops). They will file weak provisionals that won't survive non-provisional examination, give you false confidence, and consume your $2k settlement reserve.
- ❌ Do not patent the *theory*. Patent the *thing*. If you can't describe it as a machine, manufacture, process, or composition of matter that does something specific and useful, it's not patentable subject matter.
- ❌ Do not disclose internationally-relevant inventions on Zenodo BEFORE filing a provisional, if you want EU/JP/CN rights. Order matters: file-first → disclose-second for international; disclose-first is OK for US-only.

---

## 5. Cost summary

| Path | One-time cost | Annual cost | Protection scope |
|---|---|---|---|
| **Zenodo defensive-publication (recommended)** | $0 | $0 | US prior-art protection; international (where grace periods permit); blocks others from patenting. |
| **US provisional (per item, DIY)** | $60-300 USPTO + ~$0 (DIY) | $0 (lapses at 12 mo) | 12-month placeholder. **Useless without conversion.** |
| **US provisional (per item, with attorney)** | $1,500-3,000 | $0 (lapses at 12 mo) | Same as above + better-drafted claims. |
| **US non-provisional (per item, full prosecution)** | $10,000-18,000 over 2-3 years | $1,600-7,400 maintenance fees over 20 years | 20-year exclusivity in US. |
| **PCT (international)** | +$4,000-6,000 at PCT filing | +$5,000-15,000 per country at national-phase entry | International coverage, but at 5-10× US cost. |

**Bottom line:** the corpus's current funding state ($0/$50 + $2k settlement) cannot support patent prosecution. **Stick with Zenodo defensive-publication until a commercial trigger arrives.**

---

## 6. Action items

| # | Action | Owner | Cost | Due |
|---|---|---|---|---|
| P-1 | Mint Zenodo DOIs for 8 priority papers (list above §3 Phase 1) | Agent (using `ZENODO_TOKEN`) | $0 | Pass-49 |
| P-2 | Add Zenodo defensive-publication footer to each deposit | Agent | $0 | Pass-49 |
| P-3 | Maintain `papers/PATENTS_TRIGGER_LOG.md` — log any LOI/MOU/customer interest that would trigger Phase 2 | Brandon + Agent | $0 | Ongoing |
| P-4 | Re-evaluate Phase 2 triggers quarterly | Brandon | $0 | 2026-08-13, 2026-11-13, 2027-02-13, 2027-05-13 |
| P-5 | If Phase 2 triggers, consult patent attorney BEFORE filing (1-hr consult ~$300-500) | Brandon | $300-500 contingent | On trigger |

---

## 7. Calibration / #69 caveats

- I am not a patent attorney. This memo reflects publicly-available US patent law (35 U.S.C. §101-103, *Alice*, *Mayo*, *Athena*) and standard cost ranges from USPTO fee schedules + IPWatchdog/Patently-O practitioner surveys (2024-2025). For any actual filing decision, get a 1-hr consult with a registered patent attorney.
- The patentability ratings in §2 are best-effort triage, not legal opinions. *Alice*-bar invalidations have killed software patents that looked stronger on paper than items #6, #7, #14 above.
- The "moderate" patentability ratings on the quantum-circuit + LCC-Virus items assume an attorney can craft claims that survive *Alice*. That is non-trivial and not guaranteed.
- The Zenodo defensive-publication strategy is well-established but does NOT eliminate the risk that a third party files an overlapping patent you'd then need to challenge via inter-partes review (IPR, ~$30K) or litigation. It just makes that challenge winnable.

---

**END PASS 48 PROVISIONAL PATENTS STRATEGY**
