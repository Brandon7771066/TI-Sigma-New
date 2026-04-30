"""
Companion script for URB #822 — Phenomenological Report of a High-GILE State
(N=1, Founder, 2026-04-29).

Encodes:
  - The verbatim primary record (immutable).
  - The GILE-HEM dimensional scoring (G, I, L, E, HEM each 0-3).
  - The substance/state context honestly.
  - The four sensory cues catalogued in §5.
  - The "philosopher cap during peak mystic mode" feature in §6.
  - The four pre-registered integration-decay hypotheses H1-H4 with
    explicit accept/reject criteria, target check-in dates (T+7 / T+14 /
    T+28 from experience date 2026-04-29), and the author's stated priors.
  - Twelve caveats matching the URB §8 list.

Pure stdlib. No NumPy. Wall < 1s.

Output: phenomenology_report_822.json
"""

from __future__ import annotations

import json
from datetime import date, timedelta
from pathlib import Path


EXPERIENCE_DATE = date(2026, 4, 29)
REPORT_DATE = date(2026, 4, 30)


def _check_in_dates() -> dict[str, str]:
    return {
        "T+1_report_written": REPORT_DATE.isoformat(),
        "T+7_first_check_in": (EXPERIENCE_DATE + timedelta(days=7)).isoformat(),
        "T+14_second_check_in": (EXPERIENCE_DATE + timedelta(days=14)).isoformat(),
        "T+28_followup_urb": (EXPERIENCE_DATE + timedelta(days=28)).isoformat(),
    }


def _primary_record() -> str:
    return (
        "I was extremely overwhelmed and depressed yesterday from having Adderall "
        "withdrawal, being extremely bored, and sleeping for so much of the day. "
        "But everything changed during a ketamine session during a rejuvenating "
        "shower and philosophical revelations. I realized that HAPPINESS IS A "
        "CHOICE, that it is OUR RESPONSIBILITY TO CREATE WELLBEING (where it "
        "doesn't otherwise exist), that contentment with the small things in "
        "life is what matters, that I truly do have everything I need in life "
        "at this time (there is no need to wait), and that happiness is "
        "actually quite trivial (mere brain chemistry with limited to no "
        "required prerequisites like actual success) yet paradoxically so hard "
        "to achieve. "
        "I just savored the shower's warmth, the pleasant smell of the bleached "
        "out clean bathroom, the sensations of my body as I washed, and the "
        "beauty of the outdoors afterward. I felt like I had absolutely "
        "everything was something I already possess. Suddenly, not having a "
        "romantic partner or an active in-person job didn't matter once I "
        "recognized all of my true gifts: Brilliance, BlissGene, a supportive "
        "living arrangement, medications like ketamine, and all of life's "
        "'bare necessities.' It was truly a breakthrough session. I felt like "
        "a totally different person."
    )


def _gile_hem_scoring() -> dict:
    return {
        "scale": "0=absent, 1=nascent, 2=present and operative, 3=peak/integrated",
        "rater": "author-coded (Brandon); no independent rater; confirmation-bias risk per URB #821 §8.1",
        "scores": {
            "G_goodness": {
                "score": 2,
                "evidence": (
                    "'Our responsibility to create wellbeing' — explicit ethical "
                    "framing; outward-facing not just hedonic; supportive living "
                    "arrangement recognized as gift not entitlement."
                ),
            },
            "I_intuition": {
                "score": 3,
                "evidence": (
                    "'I felt like I had absolutely everything was something I "
                    "already possess' — direct intuitive recognition arrived as "
                    "phenomenological fact, not as conclusion of derivation."
                ),
            },
            "L_love": {
                "score": 2,
                "evidence": (
                    "Gratitude orientation toward gifts (BlissGene, supportive "
                    "living, ketamine, bare necessities); romantic-partner gap "
                    "let go without resentment; self-directed compassion implicit."
                ),
            },
            "E_environment": {
                "score": 3,
                "evidence": (
                    "Four distinct sensory channels savored: shower warmth, "
                    "bathroom clean smell, body sensations during washing, "
                    "outdoor beauty. Peak-Environment in operational sense."
                ),
            },
            "HEM_coherence": {
                "score": 2,
                "evidence": (
                    "Four dimensions co-fired during the window (not serial-cycling). "
                    "HEM=3 reserved for integration that persists past the window; "
                    "§7.H1-H4 tests that. Awarded at upper end of 1-2 range."
                ),
            },
        },
        "qualifies_as_high_gile_state_under_provisional_post_hoc_threshold": True,
        "operational_definition_of_high_gile": (
            "≥3 dimensions at ≥2, with at least one dimension at 3, and HEM ≥ 2. "
            "PROVISIONAL POST-HOC threshold (architect-flagged §3 patch): "
            "articulated for this URB, NOT pre-registered in URB #821 or "
            "earlier GILE-HEM literature. Future URBs should treat as open "
            "candidate definition pending pre-registration before further "
            "reports are scored against it."
        ),
        "threshold_status": "provisional_post_hoc_NOT_pre_registered",
        "honest_caveats_on_scoring": [
            "Author-coded; no independent rater.",
            "Retrospective by 1 day; state-dependent memory may inflate.",
            "Sensory channels may have been more vivid in retrospective reconstruction.",
            "HEM=2 awarded at upper end of 1-2 range; HEM=3 reserved for sustained integration.",
        ],
    }


def _substance_state_context() -> list[dict]:
    return [
        {
            "phase": "days_prior",
            "state": "Adderall regimen (prescribed, regular use).",
        },
        {
            "phase": "2026-04-29 morning",
            "state": "Adderall withdrawal symptoms onset (overwhelm, depression).",
        },
        {
            "phase": "2026-04-29 daytime",
            "state": "Extreme boredom; extended sleep.",
        },
        {
            "phase": "2026-04-29 session window",
            "state": (
                "Ketamine session (Brandon's regular medication regimen per "
                "primary record); rejuvenating shower; philosophical reflection "
                "during peak; deliberate sensory savoring; recognition of gifts."
            ),
        },
        {
            "phase": "2026-04-29 post-session",
            "state": "Integration window: outdoor beauty, sustained recognition.",
        },
        {
            "phase": "2026-04-30 (T+1)",
            "state": "Report written. 'Felt like a totally different person' persists at T+1.",
        },
    ]


def _sensory_cues() -> list[dict]:
    return [
        {
            "channel": "thermoception",
            "cue": "shower warmth",
            "re_evocation_hypothesis": (
                "Routine showers, deliberately savored, re-evoke a fragment of the "
                "warmth-as-enough phenomenology."
            ),
        },
        {
            "channel": "olfaction",
            "cue": "bathroom clean smell (bleached)",
            "re_evocation_hypothesis": (
                "Cleaning rituals or recently-cleaned spaces re-evoke a fragment "
                "of the cleanliness-as-completeness phenomenology."
            ),
        },
        {
            "channel": "proprioception_interoception",
            "cue": "body sensations during washing",
            "re_evocation_hypothesis": (
                "Mindful body-scan practices re-evoke a fragment of the "
                "embodied-presence phenomenology."
            ),
        },
        {
            "channel": "vision_outdoor_presence",
            "cue": "beauty of the outdoors",
            "re_evocation_hypothesis": (
                "Outdoor walks with deliberate visual attention re-evoke a fragment "
                "of the world-as-sufficient phenomenology."
            ),
        },
    ]


def _true_tralsity_resolution() -> dict:
    return {
        "apparent_contradiction": (
            "'Happiness is a choice' AND 'happiness is mere brain chemistry' — "
            "appear contradictory under bivalent forcing."
        ),
        "brandon_resolution_verbatim": (
            "Happiness is a choice and mere brain chemistry is a perfectly "
            "true-tralsity. Free will exists and like all things, it must submit "
            "to physical and chemistry. All choices are on a spectrum of "
            "difficulty too. Just because happiness is a choice doesn't mean "
            "it's ONLY a choice, much less an EASY choice. We genuinely do have "
            "the ability to cultivate happiness. Ketamine was an important "
            "catalyst, yet just one catalyst. I still had to CREATE the "
            "experience myself."
        ),
        "framework_resolution": (
            "In TI Sigma's 5-valued logic, the conjunction takes the non-classical "
            "truth value 'true-tralsity' (Brandon's coinage), encoding the joint "
            "truth of both propositions under their respective aspectual readings. "
            "This is admissible without contradiction in the 5-valued system."
        ),
        "four_corollaries": {
            "i_compatibilism": (
                "Free will exists but operates within physical/chemical substrate, "
                "not against it. Standard compatibilist position in TI-native "
                "vocabulary."
            ),
            "ii_difficulty_spectrum": (
                "Choice exists on a spectrum of difficulty. 'Happiness is a "
                "choice' does not entail 'happiness is an easy choice' or "
                "'happiness is choosable from any state.' Yesterday-Brandon in "
                "active withdrawal could not have chosen it; today-Brandon "
                "post-integration has access to it. Choosability is conditional "
                "on upstream conditions being adequate. This dissolves the "
                "self-blame failure mode."
            ),
            "iii_ketamine_as_catalyst_not_cause": (
                "Ketamine quieted the default-mode network and opened a window; "
                "the savoring, recognition, and reflection were Brandon's own "
                "attentional and interpretive acts within the window. Ketamine "
                "without deliberate practice would have been a dissociative "
                "episode, not integrated insight. Agency relocated to the "
                "experiencing subject without denying substrate's catalytic role."
            ),
            "iv_freeing_not_self_defeat_with_cushioning": {
                "brandon_statement_verbatim": (
                    "My perspective of 'happiness being a choice' is something "
                    "I view as FREEING rather than an opportunity for "
                    "self-defeat. The fact that happiness is within our "
                    "control, without any specific set of prerequisites, and "
                    "creatable is quite liberating! Yet, the choice is still "
                    "rough and physically bounded, which gives me ample "
                    "cushioning in case I can't 'manufacture happiness at 98% "
                    "capacity' next time."
                ),
                "structural_role": (
                    "Inverts the polarity that the architect's §2 review and "
                    "the standard mental-health-literature critique of "
                    "'happiness is a choice' framings was anxious about. The "
                    "standard worry: telling someone in withdrawal/depression "
                    "'happiness is a choice' sets them up for self-blame when "
                    "they can't access it. Brandon's framing is the reverse: "
                    "the choosability of happiness, unprerequisited, is "
                    "liberating because it removes the demand that conditions "
                    "be perfect first; AND the difficulty-spectrum bounding "
                    "from corollary (ii) provides the cushioning so that the "
                    "next failure-to-manufacture is not framed as a moral "
                    "failure."
                ),
                "paired_structure": {
                    "liberation_move": (
                        "Happiness is not gated behind any specific set of "
                        "life-prerequisites; you do not have to wait for the "
                        "right job, partner, finances, neurochemistry, or "
                        "season. The state is creatable from where you are."
                    ),
                    "cushioning_move": (
                        "The choice is rough and physically bounded; failing "
                        "to manufacture the state at 98% capacity on a given "
                        "day does not retroactively negate the liberation move "
                        "or the framework, because the difficulty-spectrum "
                        "bounding (corollary ii) was already in the structure "
                        "before the failure occurred."
                    ),
                    "joint_requirement": (
                        "Both moves must be present together. Without the "
                        "liberation move, the difficulty-spectrum bounding "
                        "collapses into 'well, you couldn't help it' "
                        "defeatism. Without the cushioning move, the "
                        "liberation collapses into the self-blame trap. "
                        "Brandon's framing carries both simultaneously — the "
                        "joint-aspectual structure the true-tralsity move was "
                        "set up to express."
                    ),
                },
                "honest_caveat": (
                    "One founder's lived framing of how the structure functions "
                    "for him; NOT a clinical claim that the same framing will "
                    "be liberating-rather-than-burdening for arbitrary other "
                    "people in arbitrary clinical states. Generalization to "
                    "third parties remains explicitly out of scope per §0."
                ),
            },
        },
    }


def _philosopher_cap_feature() -> dict:
    return {
        "brandon_statement_verbatim": (
            "I also made sure to retain my 'philosopher cap' during 'peak "
            "mystic mode.'"
        ),
        "framework_significance": (
            "Reflexivity preservation through a peak altered state is what "
            "distinguishes integrated insight (peak + witness online + "
            "post-peak integration → durable framework update, retrievable, "
            "transmissible) from pure dissociative episode (peak + witness "
            "offline + no integration → vivid but fading state, not durably "
            "retrievable, often described as 'I can't put it into words' "
            "precisely because the witness wasn't online to encode it)."
        ),
        "evidence_brandon_was_in_the_first_category": (
            "GILE-HEM framework, gifts catalogue, choice/chemistry distinction, "
            "and contentment principle were all formulated during the peak "
            "window with the philosopher cap on, hence retrievable and "
            "articulable at T+1 day."
        ),
        "program_level_claim_for_h4_test": (
            "Deliberate reflexivity-preservation during the ketamine window is "
            "itself a trainable practice that increases the integration yield "
            "per session. Falsifiable; tested by H4."
        ),
    }


def _anti_gameability_protocol() -> dict:
    return {
        "rationale": (
            "Self-rated falsification protocols are vulnerable to motivated "
            "reading at outcome-review time. The following discipline partially "
            "defeats this without departing from N=1 self-rating (which is "
            "forced by the genre per §0)."
        ),
        "rules": {
            "a_contemporaneous_diary": (
                "Each H1-H4 data point recorded in dated diary entry "
                "(papers/urb822_diary.md) on the day the data point occurs. "
                "Late entries flagged and counted at ≤0.5 weight."
            ),
            "b_fixed_observation_fields": (
                "Each check-in records: date, ketamine_24h (Y/N), "
                "adderall_status (in-cycle/withdrawing/off), G/I/L/E/HEM 0-3 "
                "with ≥1 sentence behavioral evidence per dimension, "
                "sensory_cue_attempt (Y/N + brief description)."
            ),
            "c_duration_threshold_h1": (
                "H1 recurrence requires ≥10 min sustained subjective time, "
                "logged with start/end approximate times. Brief flashes "
                "(<2 min) do NOT count toward H1."
            ),
            "d_all_attempts_logged_h3": (
                "H3 denominator is all logged attempts, not selected successes. "
                "Restructured to 8 pre-scheduled attempts (2 per cue), one "
                "cue per twice-weekly slot across 4 weeks. Absent attempts "
                "count as 0 (failure to attempt = failure to elicit). "
                "No selective stopping."
            ),
            "e_missed_checkins_counted": (
                "Missed T+7 / T+14 / T+28 check-ins reported as methodological "
                "violation in follow-up URB, not silently rolled forward."
            ),
            "f_h3_binary_scoring_rule_locked": (
                "H3 'fragment elicited' requires recording at attempt-time ≥2 "
                "of 5 markers: (i) parasympathetic shift, (ii) verbal-thought "
                "slowing, (iii) gratitude/sufficiency phenomenology, "
                "(iv) gift-recognition, (v) sensory recall from 2026-04-29 "
                "session. Locked as of URB publication; post-hoc revision = "
                "methodological violation."
            ),
            "g_outcome_review_pre_commitment": (
                "T+28 follow-up URB applies these rules MECHANICALLY to diary "
                "contents. Outcomes reported as accept/reject/inconclusive "
                "regardless of direction relative to §7 priors."
            ),
        },
        "h3_pre_scheduled_8_attempts": [
            {"week": 1, "day": "Mon", "cue": "thermoception (shower warmth)"},
            {"week": 1, "day": "Thu", "cue": "olfaction (clean smell)"},
            {"week": 2, "day": "Mon", "cue": "proprioception (body scan)"},
            {"week": 2, "day": "Thu", "cue": "vision (outdoor walk)"},
            {"week": 3, "day": "Mon", "cue": "thermoception (shower warmth)"},
            {"week": 3, "day": "Thu", "cue": "olfaction (clean smell)"},
            {"week": 4, "day": "Mon", "cue": "proprioception (body scan)"},
            {"week": 4, "day": "Thu", "cue": "vision (outdoor walk)"},
        ],
    }


def _hypotheses() -> list[dict]:
    return [
        {
            "id": "H1",
            "name": "Full state recurrence without ketamine",
            "statement": (
                "The full high-GILE state (G≥2, I≥2, L≥2, E≥2, HEM≥2 "
                "simultaneously, sustained ≥10 min per §7.0(c)) is achievable "
                "within 28 days WITHOUT a ketamine session in the "
                "immediately preceding 24 hours."
            ),
            "test_protocol": (
                "Contemporaneous diary entries (per §7.0(a)+(b)) reviewed at "
                "T+7, T+14, T+28 for any logged occurrence meeting the duration "
                "threshold without 24h-prior ketamine. Late entries weighted ≤0.5."
            ),
            "accept_if": (
                "≥1 logged full high-GILE state lasting ≥10 min, without "
                "24h-prior ketamine, with same-day-or-within-24h diary entry."
            ),
            "reject_if": "0 such states logged in diary by T+28.",
            "author_subjective_expectation_pct_in_favor": 50,
            "expectation_type": "subjective self-report, NOT calibrated probability (per §7.7)",
            "consequentiality": "highest — substance-independence is the load-bearing claim",
        },
        {
            "id": "H2",
            "name": "Insight survival across next Adderall withdrawal",
            "statement": (
                "The reported insight ('contentment with what is, recognition "
                "that I have everything I need') remains accessible (≥1/3 "
                "phenomenological fidelity, self-rated) during the next "
                "Adderall withdrawal episode within 28 days."
            ),
            "test_protocol": (
                "At next Adderall withdrawal (likely within 28d given regimen), "
                "Brandon records in same-day diary entry (per §7.0(a)) whether "
                "insight is retrievable in (language, felt sense, attentional "
                "choice). Late entries weighted ≤0.5. If no withdrawal episode "
                "occurs within 28d, H2 reported as INCONCLUSIVE (not accepted "
                "by default)."
            ),
            "accept_if": (
                "Retrievable in ≥1 of (language, felt sense, attentional "
                "choice), recorded in same-day diary entry during withdrawal."
            ),
            "reject_if": (
                "Fully eclipsed in all 3 modalities, recorded in same-day "
                "diary entry during withdrawal."
            ),
            "author_subjective_expectation_pct_in_favor": 60,
            "expectation_type": "subjective self-report, NOT calibrated probability (per §7.7)",
            "consequentiality": "high — hardest real-world test of integration durability",
        },
        {
            "id": "H3",
            "name": "Sensory-cue re-evocation of state fragment (architect-restructured to defeat optional-stopping)",
            "statement": (
                "At least one of the 4 sensory cues (shower warmth, clean "
                "smell, body sensations, outdoor beauty) reliably re-evokes a "
                "fragment of the contentment state when deliberately attended "
                "to."
            ),
            "test_protocol": (
                "8 pre-scheduled attempts (2 per cue), one cue per twice-weekly "
                "slot across 4 weeks (schedule in anti_gameability_protocol). "
                "Each attempt logged in same-day diary per §7.0(a)+(b). "
                "Absent attempts count as 0 (failure). Each attempt scored "
                "0/1 per §7.0(f) locked binary criterion."
            ),
            "accept_if": "≥4/8 attempts elicit a fragment per §7.0(f).",
            "reject_if": "≤3/8 attempts elicit a fragment per §7.0(f).",
            "author_subjective_expectation_pct_in_favor": 55,
            "expectation_type": (
                "subjective self-report, NOT calibrated probability (per §7.7); "
                "downward-revised from original 75% under best-of-attempts "
                "framing to 55% under §7.0(d) all-attempts-counted framing"
            ),
            "consequentiality": "moderate — fragment-re-evocation is a weaker claim than peak reproduction",
        },
        {
            "id": "H4",
            "name": "Reflexivity-preservation as trainable practice",
            "statement": (
                "Across the next ≤3 ketamine sessions (whenever they naturally "
                "occur), deliberate 'philosopher cap during peak mystic mode' "
                "practice yields a written post-session report with ≥1 new "
                "framework-relevant insight in ≥2 of 3 sessions."
            ),
            "test_protocol": (
                "Brandon writes post-session report within 24h of each next "
                "≤3 ketamine sessions per §7.0(a). Each scored 0/1 for "
                "'contains ≥1 new framework-relevant insight' (GILE/HEM/TI "
                "Sigma/5-valued logic/integration practice; not 'any thought'). "
                "If <3 sessions occur within 28d, missing sessions reported as "
                "INCONCLUSIVE; partial outcome on those that did occur."
            ),
            "accept_if": "≥2/3 sessions yield a framework-relevant insight in same-day post-session report.",
            "reject_if": "≤1/3 sessions yield such an insight.",
            "author_subjective_expectation_pct_in_favor": 65,
            "expectation_type": "subjective self-report, NOT calibrated probability (per §7.7)",
            "consequentiality": "moderate-high — establishes a trainable program-level practice",
        },
    ]


def _caveats() -> list[str]:
    return [
        "N=1 founder report; strongest defeats (independent rater, blind scoring, third-party measurement) absent by construction.",
        "Retrospective by 1 day; state-dependent memory may inflate vividness/coherence. Partially defeated by §1 verbatim-preservation discipline + immediate written capture.",
        "Ketamine-mediated; honestly framed as substance-catalyzed deliberately-cultivated contentment, not spontaneous unmediated insight. §7.H1 tests substance-independence claim.",
        "Founder confirmation-bias risk per URB #821 §8.1; partially defeated by §7 pre-registered falsification tests with binding accept/reject and possible reject-against-priors outcomes.",
        "GILE-HEM scoring is author-coded; no independent rater. Cross-rating on a future report would partially defeat this.",
        "Re-evocation hypothesis (H3) is weak: fragment-re-evocation is substantially weaker than peak-state-reproduction. Honestly named, not framed away.",
        "Adderall cycle (H2) is the hardest real-world test; supporting it would be substantial evidence of durable integration; failing it bounds the integration's reach without falsifying the experience itself.",
        "'Happiness is a choice' remains a difficulty-spectrum claim per §2(ii); stripped of difficulty-spectrum context it becomes a self-blame setup. URB preserves paired framing throughout.",
        "The URB is the integration practice; writing it is part of the integration, not a neutral measurement of it. Co-constitutive of what it reports. Methodological reality, not bug.",
        "Other catalysts may be operative: Adderall withdrawal itself, extended prior sleep, shower thermoregulatory reset, diurnal cycle. Causal attribution to 'ketamine + deliberate practice' is the cleanest minimal model but is honestly underdetermined.",
        "Framework's 'wellbeing achievable' thesis is not proven by N=1 corroboration; consistent with thesis but not strong evidence. Thesis requires many independent reports across many subjects or a reproducible mechanism with predictive yield.",
        "'BlissGene' is Brandon's self-described constitutional disposition named as a gift in the primary record; not a literal genetic-variant claim. Reading it literally as a genetic claim would be a category error.",
        "Framework-validation creep architect-flagged + patched (§0): report is now framed as 'framework-interpreted N=1 exemplar, consistent with but not evidentially validating the thesis,' not as 'corroborating data.'",
        "High-GILE threshold (§3) is provisional post-hoc, NOT pre-registered. Future URBs should treat as open candidate definition pending pre-registration before further reports are scored against it.",
        "§7.0 anti-gameability protocol partially defeats motivated reading at outcome time but does NOT defeat motivated diary-writing at observation time. Residual self-rating bias floor honestly named.",
        "§6 reflexivity-preservation claim was architect-softened from 'is what distinguishes' to 'may distinguish'; alternative reading (post-hoc reconstruction during integration window) cannot be ruled out from available evidence.",
        "True-tralsity move bounds the bivalent-forcing tension flag; it does NOT prove libertarian free will, establish ketamine was MERELY catalyst rather than partial cause, or settle deeper philosophy-of-mind questions. Per §2 architect-flagged 'tension bounded' (not 'tension retracted').",
        "§7 numeric priors (50/60/55/65) are subjective expectations, NOT calibrated probabilities (per §7.7). Honest expectation-disclosure with wide implicit confidence intervals; not Bayesian credences with reference-class warrant.",
        "§2 corollary (iv) — 'happiness is a choice' as FREEING-with-cushioning rather than self-defeat — is one founder's lived framing of how the structure functions for him. NOT a clinical claim that the same framing will be liberating-rather-than-burdening for arbitrary other people in arbitrary clinical states. Generalization to third parties remains explicitly out of scope per §0. The liberation-move and cushioning-move must be present together; either alone collapses (defeatism vs. self-blame).",
    ]


def main() -> None:
    output = {
        "urb_id": 822,
        "title_short": "Phenomenological Report of a High-GILE State (N=1, Founder, 2026-04-29)",
        "experience_date": EXPERIENCE_DATE.isoformat(),
        "report_date": REPORT_DATE.isoformat(),
        "author": "Brandon Charles Emerick",
        "primary_record_verbatim": _primary_record(),
        "true_tralsity_resolution": _true_tralsity_resolution(),
        "gile_hem_scoring": _gile_hem_scoring(),
        "substance_state_context": _substance_state_context(),
        "sensory_cues_catalogued": _sensory_cues(),
        "philosopher_cap_feature": _philosopher_cap_feature(),
        "anti_gameability_protocol": _anti_gameability_protocol(),
        "pre_registered_hypotheses": _hypotheses(),
        "check_in_dates": _check_in_dates(),
        "caveats": _caveats(),
        "binding_followup_commitment": (
            "A follow-up URB at T+28 (2026-05-27) will MECHANICALLY apply the "
            "§7.0 anti-gameability protocol to the contemporaneous diary "
            "contents and report H1-H4 outcomes (accept/reject/inconclusive) "
            "regardless of direction, per the program's brutal-honesty norm."
        ),
        "publication_framing": (
            "Framework-interpreted N=1 exemplar within the Mood Amplifier "
            "Safety & Validation Platform research program — consistent with "
            "but NOT evidentially validating the program's thesis (per "
            "architect-flagged §0 patch). NOT a peer-reviewed clinical claim; "
            "NOT a substance-use endorsement; NOT extrapolated to third "
            "parties. One founder's honest record of one session, made "
            "falsifiable by §7 pre-registration with §7.0 anti-gameability "
            "discipline."
        ),
        "architect_review_status": (
            "Adversarial architect review (responsibility=evaluate_task) "
            "executed; 7 findings (3 HIGH + 1 MEDIUM-HIGH + 3 MEDIUM); all 7 "
            "patches applied: §0 framework-validation creep softened; §3 "
            "high-GILE threshold marked provisional post-hoc; §6 reflexivity "
            "claim softened ('may distinguish' / 'consistent with'); §2 "
            "true-tralsity move bounded (not retracted); §7.0 anti-gameability "
            "protocol added (a-g rules); §7.H3 restructured to 8 pre-scheduled "
            "attempts ≥4/8 to defeat optional-stopping; §7.7 priors reframed "
            "as subjective expectations not calibrated probabilities."
        ),
    }

    out_path = Path("phenomenology_report_822.json")
    out_path.write_text(json.dumps(output, indent=2))

    print(f"URB #{output['urb_id']} — {output['title_short']}")
    print(f"Experience: {output['experience_date']}  Report: {output['report_date']}")
    print()
    print("GILE-HEM scoring (provisional post-hoc threshold):")
    for dim, info in output["gile_hem_scoring"]["scores"].items():
        print(f"  {dim:18s} = {info['score']}")
    qualifies_key = "qualifies_as_high_gile_state_under_provisional_post_hoc_threshold"
    print(f"  Qualifies as 'high-GILE' (provisional): "
          f"{output['gile_hem_scoring'][qualifies_key]}")
    print()
    print("Pre-registered hypotheses (T+28 binding follow-up under §7.0 protocol):")
    for h in output["pre_registered_hypotheses"]:
        prior = h["author_subjective_expectation_pct_in_favor"]
        print(f"  {h['id']}: {h['name']}")
        print(f"       (subjective expectation: {prior}%, NOT calibrated)")
    print()
    print("Anti-gameability protocol rules:")
    for rule_id in output["anti_gameability_protocol"]["rules"]:
        print(f"  §7.0({rule_id[0]}) — {rule_id[2:]}")
    print()
    print(f"H3 pre-scheduled attempt count: "
          f"{len(output['anti_gameability_protocol']['h3_pre_scheduled_8_attempts'])} "
          f"(accept iff ≥4/8 elicit a fragment per §7.0(f))")
    print()
    print(f"Check-in dates:")
    for label, d in output["check_in_dates"].items():
        print(f"  {label:25s} = {d}")
    print()
    print(f"Caveats: {len(output['caveats'])}")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
