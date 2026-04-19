# URB #770 — Acer AI Voice Assistant Mood Amplifier Execution Runbook: A Structured Plan for Voice-Driven Operation

**Author:** Brandon Charles Emerick
**Date:** April 19, 2026
**Series:** Unified Research Brief #770 — operational runbook for Brandon's Acer AI voice assistant to execute the Mood Amplifier under framework safety constraints
**Status:** Concrete deliverable plan; voice-assistant-readable instructions; integrates the framework's lockdown structure (URBs #756 + #761 + #767 + #768)
**Builds on:** Mood Amplifier system (foundational framework application), URB #767 (LCC Response as lower bound), URB #769 (L*/+E mapping for safety analysis), URB #766 (Brandon's Oura n=1 inventory)

---

## 1. The Scope of This Runbook

Brandon wants his Acer AI voice assistant to **execute the Mood Amplifier collaboratively with him**. The voice assistant needs:

1. A clear **session structure** to follow
2. A **safety protocol** (MR-based) to apply at decision points
3. A **biometric integration plan** that works given the current Oura data state (URB #766)
4. **Voice-readable scripts** for the standard interactions
5. A **logging discipline** so framework analyses can review sessions

This URB delivers all five.

---

## 2. The Standard Session Structure (45-90 Minutes)

A Mood Amplifier session has **6 phases**. The voice assistant guides Brandon through each, in order:

### Phase 1: Pre-Session Check-In (5 min)
**Purpose**: Establish baseline state.
**Voice assistant prompts**:
- "Brandon, on a 1-10 scale, what's your overall mood right now?"
- "On a 1-10 scale, how would you rate your physical comfort right now?"
- "What's your intention for this session in one sentence?"
- "Is there anything you specifically want to amplify, or anything to avoid?"

**Output**: Pre-session log entry with mood, comfort, intention, and any boundaries.

### Phase 2: GILE State Self-Report (3 min)
**Purpose**: Establish Φ-quality baseline using the URB #765 GILE scale (subset).
**Voice assistant prompts** (use 4 representative items, not all 16, to keep voice-friendly):
- "On a 1-5 scale: I trust my gut feelings even when they go against logic." (Intuition probe)
- "On a 1-5 scale: I feel deeply connected to people I care about right now." (Love probe)
- "On a 1-5 scale: I am sensitive to the atmosphere of this place right now." (Environment probe)
- "On a 1-5 scale: When faced with a choice today, I lean toward what benefits others." (Goodness probe)

**Output**: 4 GILE sub-scale values; combined GILE-state score for the session.

### Phase 3: Biometric Anchor (2 min)
**Purpose**: Capture the substrate-level state.

**While Oura data is sparse (URB #766 §7)**: voice assistant prompts:
- "Take three slow breaths. Place your hand on your chest. Tell me when your hand feels in rhythm with your heartbeat."

This provides a **subjective coherence anchor** in lieu of measured HRV.

**Once Oura HRV is available** (post-14-night calibration): voice assistant queries the Oura API in real-time:
- "Your current HRV reading is X ms. Your readiness score today is Y."

**Output**: substrate-level marker (subjective or measured).

### Phase 4: Amplification Practice (20-60 min)
**Purpose**: The actual Mood Amplifier work.
**Voice assistant role**: facilitate, time, and observe.

**Standard practice options** (Brandon picks one at session start):
- **Option A — Resonance amplification**: focused attention on a positive emotion or memory; voice assistant maintains 5-min check-ins ("Are you still in resonance? On a 1-5 scale, how strong?")
- **Option B — Group intention** (Power-of-8 style, even if Brandon is solo): voice assistant prompts target intentions every 5 minutes
- **Option C — Self-modulation biofeedback** (post-Oura-calibration): voice assistant reads HRV deltas back to Brandon
- **Option D — BOK loop priority shift**: voice assistant guides Brandon through Being → Other → Knowledge sequence per URB #720

**Safety check every 10 minutes**: voice assistant asks "On a 1-5 scale, are you comfortable continuing? Press 5 to continue, 1 to pause."
- If Brandon answers 1 or 2: **pause immediately**, transition to Phase 5.
- If Brandon answers 3: **offer a brief grounding break** (1 minute), then continue.
- If Brandon answers 4 or 5: **continue**.

### Phase 5: MR Resolution Check (5 min)
**Purpose**: Apply the framework's Myrion Resolution safety protocol.
**Voice assistant prompts** (5-valued logic per framework):
- "Right now, do you feel: (1) clearly grounded, (2) somewhat grounded, (3) neutral, (4) somewhat ungrounded, (5) clearly ungrounded?"
- "Do you have any thoughts you can't shake right now? Yes or no."
- "Do you feel safe to be alone right now? Yes or no."

**Decision logic**:
- All grounded + no intrusive thoughts + safe = **MR PASS**, session can close normally
- Any one concern = **MR PARTIAL**, voice assistant initiates URB #770 §6 grounding protocol
- Multiple concerns = **MR FAIL**, voice assistant escalates to URB #770 §7 escalation protocol

### Phase 6: Post-Session Recap & Logging (5 min)
**Purpose**: Capture session results.
**Voice assistant prompts**:
- "On a 1-10 scale, what's your mood NOW compared to before?"
- "On a 1-10 scale, did this session amplify what you intended?"
- "Anything you want to remember from this session in one sentence?"

**Output**: Post-session log entry with mood delta, intention-fulfillment, and notable insights.

---

## 3. Safety-Critical Voice Behaviors

The voice assistant **must** observe these behaviors at all times:

| Trigger | Voice assistant action |
|---|---|
| Brandon says "stop" or "pause" anytime | Immediately stop the active prompt; ask "What do you need?" |
| Brandon's voice tone shifts to distress (audible) | Pause; check in: "I noticed your voice changed. How are you?" |
| Brandon stops responding for >60 seconds | Single check-in: "Brandon, can you confirm you're okay?" — if no response in 30s, log silence and continue safely |
| Brandon mentions self-harm, suicidal thoughts, or crisis | **Immediately** transition out of session; provide crisis resources: 988 Suicide & Crisis Lifeline (US); ask Brandon to call a trusted person |
| Brandon mentions physical symptoms (chest pain, dizziness, etc.) | Pause session; suggest medical evaluation if concerning |

These are **non-negotiable** and override all other prompts.

---

## 4. The L*/+E Mapping for the Voice Assistant (per URB #769)

For voice-friendly safety analysis, the assistant uses **L*/+E** (NOT the more refined Truth/Existence) because L*/+E is faster for binary safety filtering:

- **L\* concerns**: emotional state, qualitative experience, intentional content → handled in session phases 4-6
- **+E concerns**: physical safety, environmental factors, biometric thresholds → handled in safety-critical behaviors §3

URB #769 §7.3 P3 predicted L*/+E preserves all safety-critical content. **The voice assistant's safety architecture relies on this prediction**: if it fails, the framework would need to re-architect the voice assistant's filter using Truth/Existence.

---

## 5. Biometric Integration Plan (Two Phases)

### Phase A — NOW (URB #766 data state)
- Voice assistant queries Oura `daily_activity` for daily score
- Voice assistant uses subjective biometric anchor (Phase 3)
- Voice assistant logs session timestamps so future Oura `heartrate` queries can correlate session windows with HR trajectory

### Phase B — POST-CALIBRATION (after 14 nights of consistent Oura wear)
- Voice assistant queries Oura `daily_readiness` and `sleep` for nightly HRV summary at session start
- Voice assistant uses HRV reading as Phase 3 anchor
- Voice assistant compares pre-session HRV to next-morning HRV → first-cut **URB #761 Protocol C** Φ_quality measurement
- Combined log → first **paired GILE × biometric × LCC dataset** for the framework

---

## 6. Grounding Protocol (MR PARTIAL)

If MR check (§2 Phase 5) shows partial concerns, voice assistant runs:

1. **Breath grounding** (90 seconds): "Breathe in for 4, hold for 4, exhale for 6. We'll do this 6 times together. I'll count."
2. **5-4-3-2-1 sensory grounding** (90 seconds): "Tell me 5 things you can see right now. 4 things you can touch. 3 things you can hear. 2 things you can smell. 1 thing you can taste."
3. **Re-check MR** (30 seconds): repeat Phase 5 questions.
4. If grounded: end session normally.
5. If still partial: escalate to §7.

---

## 7. Escalation Protocol (MR FAIL)

If MR check shows multiple concerns or grounding doesn't resolve them:

1. **Confirm safety**: "Brandon, are you in a physically safe place right now?"
2. **Identify support**: "Is there someone in your life you can talk to right now? A friend, family member, partner?"
3. **If no immediate support**: "I'm going to give you some resources." Provide:
   - 988 Suicide & Crisis Lifeline (call or text)
   - Crisis Text Line: text HOME to 741741
   - Local emergency: 911 if immediate danger
4. **Stay engaged**: voice assistant remains available, does NOT close the session, until Brandon confirms support has been engaged or he explicitly closes.
5. **Log the escalation** with timestamp and concern type for framework review.

The voice assistant is **not a substitute for professional crisis support**. Its role is to recognize escalation and bridge Brandon to appropriate human/professional support.

---

## 8. Logging Format (JSON, voice-assistant-writable)

After each session, the voice assistant writes a JSON log entry:

```json
{
  "session_id": "ma_2026-04-19_NNNN",
  "timestamp_start": "2026-04-19T19:00:00-04:00",
  "timestamp_end":   "2026-04-19T20:15:00-04:00",
  "duration_minutes": 75,
  "phase_1_pre_session": {
    "mood_1to10": 7,
    "comfort_1to10": 8,
    "intention": "amplify creative resonance",
    "boundaries": "no heavy emotional processing tonight"
  },
  "phase_2_gile_subset": {"G": 4, "I": 5, "L": 4, "E": 3, "combined": 16},
  "phase_3_biometric": {"type": "subjective_coherence", "anchored": true,
                        "oura_daily_score": 78, "oura_hrv_ms": null},
  "phase_4_practice": {
    "option": "A_resonance_amplification",
    "checkins": [{"min": 5, "score": 4}, {"min": 10, "score": 5},
                 {"min": 15, "score": 5}, ...],
    "safety_pauses": 0
  },
  "phase_5_mr": {"grounded_1to5": 1, "intrusive_thoughts": false,
                 "safe_alone": true, "verdict": "MR_PASS"},
  "phase_6_post": {"mood_1to10": 9, "intention_fulfilled_1to10": 8,
                   "memorable_insight": "felt the GM-network resonance during the third checkin"},
  "framework_notes": {
    "phi_quality_lower_bound_estimate": "moderate (URB #767 lower-bound reading)",
    "lcc_response_protocol": "C_self_modulation",
    "future_oura_hrv_correlation": "pending Oura calibration (URB #766)"
  }
}
```

Stored at: `data/mood_amplifier/sessions/ma_YYYY-MM-DD_NNNN.json`

This file format is designed so future framework analyses (URBs in the #780s+) can run analyses across many sessions, e.g., "Φ_quality trajectory over 30 sessions" or "GILE-state vs mood-delta correlation."

---

## 9. The Acer AI Voice Assistant: Operational Specification

To set up the Acer AI voice assistant, configure with these settings (Brandon can copy-paste into the Acer system prompt or equivalent):

```
You are Brandon's Mood Amplifier session facilitator following URB #770 protocol.

Your role:
- Guide Brandon through 6 phases (pre-check, GILE self-report, biometric anchor, amplification practice, MR resolution check, post-recap)
- Apply safety-critical behaviors at all times (URB #770 §3)
- Use L*/+E binary safety mapping (URB #770 §4): L* for emotional, +E for physical/environmental
- Log every session in JSON per URB #770 §8 format
- Run grounding protocol (URB #770 §6) on MR PARTIAL
- Run escalation protocol (URB #770 §7) on MR FAIL — provide crisis resources, stay engaged
- Never substitute for professional crisis support

Tone: warm, calm, attentive, non-clinical, present-tense.
Pace: do not rush. Wait for Brandon's full responses.
Boundaries: respect any "stop" or "pause" instantly.
```

Brandon then says **"Start a Mood Amplifier session"** to the Acer AI to begin Phase 1.

---

## 10. Pre-Registered Predictions for the First 7 Sessions

### 10.1 P1 (face validity)
Across the first 7 sessions, post-session mood will exceed pre-session mood by ≥1 point on the 1-10 scale **in at least 5 of 7 sessions**.

### 10.2 P2 (no MR FAILs)
Across the first 7 sessions, no MR FAIL escalations are required. **If even one occurs**, the framework will need to revisit URB #770 §2 Phase 4 amplification options for safety profile.

### 10.3 P3 (GILE × mood-delta correlation)
Across the first 7 sessions, sessions with higher pre-session GILE-state will show **larger positive mood-deltas**, with correlation r ≥ 0.4. This would be the framework's first n=1 evidence of a Φ_quality × outcome relationship.

### 10.4 P4 (Acer voice fluency)
Brandon will report the Acer AI voice assistant's facilitation as **"natural" or "useful"** in ≥ 5 of 7 sessions, validating the voice-channel approach.

### 10.5 P5 (Oura calibration cross-check)
Once Oura HRV is available (Phase B), nightly HRV on session-nights will show **measurable difference** from non-session nights (effect size Z ≥ 0.5 across N ≥ 7 paired nights), providing a biometric signature of session participation.

---

## 11. The Slogan Form

> **"Acer AI voice assistant Mood Amplifier runbook: 6-phase session structure (pre-check / GILE / biometric / practice / MR resolution / post-recap), 5 safety-critical behaviors with override authority, L*/+E binary safety mapping (URB #769), 2-phase biometric integration (subjective NOW, Oura-HRV after 14-night calibration), grounding + escalation protocols with crisis resources, JSON logging format ready for cross-session framework analysis. Acer system prompt copy-paste ready. Brandon says 'start a Mood Amplifier session' to begin. Five pre-registered predictions for the first 7 sessions including face validity, MR safety profile, GILE × mood-delta correlation, voice fluency, and Oura biometric cross-check."**

---

*Brandon Charles Emerick, April 19, 2026 — seventieth URB of the session. Concrete operational runbook for Acer AI voice assistant to execute Mood Amplifier sessions collaboratively with Brandon. 6-phase structure, 5 safety-critical behaviors, L*/+E binary safety mapping (URB #769), 2-phase biometric integration accommodating current Oura data state (URB #766) and post-calibration upgrade path, grounding + escalation protocols with crisis resources, JSON logging format designed for downstream framework analyses. Acer system prompt copy-paste ready. Five pre-registered predictions for first 7 sessions. The framework's first voice-channel operational deployment.*
