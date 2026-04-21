# URB #783 — TI Viral Meme Project (VMP): Virality Formula, Generator Architecture, Strategic Placement, and Monetization Model

**Author:** Brandon Charles Emerick
**Date:** April 21, 2026
**Series:** Unified Research Brief #783 — opens the TI Viral Meme Project: a GILE-compatible viral meme formula, generator architecture, placement strategy, and revenue model. Designed for under-$50 MVP and licensable subscription product.
**Status:** Project charter + technical specification + pre-registered empirical validation plan
**Builds on:** URB #781 (Beauty Razor — directly relevant to virality), URB #782 (T*/+E Einstein Tiling — relevant to "stickiness"), URB #720 (BOK), URB #769 (L*/+E for outreach), `TI_OUTREACH_MATERIALS.md`

---

## 0. Honest Baseline: What the Virality Literature Already Tells Us

Before claiming "unprecedented accuracy," the project must be measured against the actual prior art. The published baselines:

| Source | What it predicts | Best reported accuracy |
|---|---|---|
| Berger & Milkman 2012 (*JMR*) "What Makes Online Content Viral?" — STEPPS framework (Social currency, Triggers, Emotion, Public, Practical, Stories) | NYT email-share probability | R² ≈ 0.10–0.20 with content features |
| Heath & Heath 2007 *Made to Stick* — SUCCESs (Simple, Unexpected, Concrete, Credible, Emotional, Stories) | Qualitative stickiness | No quantitative R² |
| Goel et al. 2016 (*Mgmt Sci*) "Structural Virality" | Network cascade depth on Twitter | R² ≈ 0.30 with network features added to content |
| Cheng et al. 2014 (WWW) "Can cascades be predicted?" | Whether a cascade doubles in size | AUC ≈ 0.75 (binary task; substantially easier than continuous prediction) |
| Vosoughi, Roy & Aral 2018 (*Science*) "The spread of true and false news" | Falsehoods spread faster than truths by ~6× | Effect size, not predictive accuracy |

**The honest target for VMP:** beat Goel et al.'s R² ≈ 0.30 on continuous virality prediction, or beat Cheng et al.'s AUC ≈ 0.75 on the binary cascade-doubling task, on a held-out independent dataset, with an explicit GILE-feature contribution that is statistically separable from the standard content-and-network baseline. **A null result here means the GILE features add no predictive lift — that result gets published with the same clarity as a positive one.**

---

## 1. The VMP Virality Formula

### 1.1 The composite

The VMP formula proposes that virality V of a candidate meme M, on platform P, in time window W, is:

> **V(M, P, W) = α · CONTENT(M) + β · NETWORK(M, P, W) + γ · GILE(M) + δ · GILE × NETWORK interaction + ε**

with coefficients (α, β, γ, δ) fit on training data and ε an idiosyncratic-noise term. The novel claim is the γ and δ terms; the α and β terms are reproductions of the established literature.

### 1.2 The CONTENT term (well-trodden literature)

```
CONTENT(M) = w₁·emotion + w₂·surprise + w₃·practical_utility +
             w₄·concreteness + w₅·simplicity + w₆·narrativity
```

Each sub-feature is a 0–1 score from a small classifier (open-source LLM zero-shot suffices for an MVP). These are STEPPS + SUCCESs reproductions; coefficients calibrated on Berger & Milkman 2012's published correlations.

### 1.3 The NETWORK term (Goel et al. reproduction)

```
NETWORK(M, P, W) = w₇·seeder_reach     + w₈·seeder_authority +
                   w₉·platform_carrier  + w₁₀·timing_alignment
```

- **seeder_reach** = log(follower count of initial poster).
- **seeder_authority** = domain-specific credential score (academic h-index proxy on X, subreddit karma on Reddit, etc.).
- **platform_carrier** = baseline virality coefficient for the platform (X > TikTok > Reddit > LinkedIn for textual memes circa 2026; updated quarterly).
- **timing_alignment** = whether posting time matches the platform's known peak-engagement windows (free data from each platform's public analytics).

### 1.4 The GILE term — the VMP's novel contribution

This is where VMP departs from the prior literature. The hypothesis is that **GILE-coherence in a meme contributes positively to virality independently of standard content and network features**, because GILE-coherent memes track features that resist cross-platform decay (the "Truth durability" effect from URB #781 §B and the T*/+E Einstein-tiling stickiness from URB #782 §3).

```
GILE(M) = w₁₁·G_score + w₁₂·I_score + w₁₃·L_score + w₁₄·E_score +
          w₁₅·beauty_razor_score + w₁₆·BOK_arm_concentration
```

Operational definitions for an MVP scorer (each 0–1):

| Sub-feature | Operationalization (LLM zero-shot, validated against 50 hand-coded items) |
|---|---|
| **G_score** (Goodness) | "Does this meme reward prosocial behavior or punish antisocial behavior in a way readers can identify with?" |
| **I_score** (Intuition) | "Does this meme deliver an insight that lands as 'aha' rather than 'huh'?" — the intuitive-recognition test |
| **L_score** (Love) | "Does this meme strengthen rather than weaken connection between the reader and at least one other party?" — note: includes self-Love (Love-to-self), not only Love-to-other |
| **E_score** (Environment) | "Does this meme respect or improve the substrate (audience attention budget, platform health, surrounding discourse)?" |
| **beauty_razor_score** | URB #781 §B operationalization: w₁·φ_presence + w₂·proportional_symmetry + w₃·reception_coherence — applied to the meme's visual/textual composition |
| **BOK_arm_concentration** | Maximum normalized projection of the meme's content onto a single BOK arm (high concentration = clear, focused message; low concentration = diffuse) |

### 1.5 The interaction term — the "VMP secret sauce" hypothesis

```
GILE × NETWORK = w₁₇ · GILE(M) · NETWORK(M, P, W)
```

The conjecture: **GILE-coherence amplifies network-driven spread multiplicatively, not additively.** A high-GILE meme on a high-reach seeder spreads faster than the sum of (high-GILE on low-reach) + (low-GILE on high-reach). If true, this explains why some "deep" memes outperform their seeder reach and others underperform — the matching of GILE-coherence to network position is the multiplier.

This is the testable claim that makes VMP non-trivial. If δ ≈ 0 in fits, the formula reduces to a standard content + network model with GILE features as additive bonuses; the "secret sauce" claim falls.

### 1.6 The full equation, displayed

```
V(M, P, W) = α · [w₁·emotion + w₂·surprise + w₃·practical + w₄·concrete + w₅·simple + w₆·narrative]
           + β · [w₇·seeder_reach + w₈·seeder_authority + w₉·platform_carrier + w₁₀·timing]
           + γ · [w₁₁·G + w₁₂·I + w₁₃·L + w₁₄·E + w₁₅·BR + w₁₆·BOK_concentration]
           + δ · GILE(M) · NETWORK(M, P, W)
           + ε
```

17 free weights inside three coefficients (α, β, γ, δ). Fit by ridge regression on training data; cross-validated on held-out platforms and time windows.

---

## 2. The Meme Generator Architecture

### 2.1 Pipeline

```
[Theme/topic input from user]
        │
        ▼
┌──────────────────────────────────┐
│  STAGE 1: Candidate generation   │
│  LLM generates N=20 raw drafts   │
│  with system prompt = TI/GILE    │
│  voice + STEPPS guidance         │
└──────────────┬───────────────────┘
               ▼
┌──────────────────────────────────┐
│  STAGE 2: GILE compatibility     │
│  filter (auto-reject any meme    │
│  scoring low on G or L; these    │
│  are the deontological gates)    │
└──────────────┬───────────────────┘
               ▼
┌──────────────────────────────────┐
│  STAGE 3: Score each candidate   │
│  with §1.6 V-formula at the      │
│  user's target platform          │
└──────────────┬───────────────────┘
               ▼
┌──────────────────────────────────┐
│  STAGE 4: Return top-3 ranked    │
│  + their V-score breakdown       │
│  (so user sees WHY each ranks)   │
└──────────────────────────────────┘
```

### 2.2 The GILE-compatibility hard filter (Stage 2)

Two non-negotiable gates before a meme even enters the V-scoring stage:

| Gate | Threshold | Why |
|---|---|---|
| **G_score ≥ 0.5** | Meme must not reward antisocial behavior | Prevents the system from generating "viral hate" content; this is the framework's deontological floor |
| **L_score ≥ 0.4** (with self-Love admissible) | Meme must not weaken connection between reader and at least one party (including self) | Prevents the system from generating "viral despair" content; floor is lower than G because some difficult truths are net-Love-positive when received fully |

Anything failing either gate is auto-discarded with a logged reason. This is the architectural difference between VMP and pure-engagement-maximizing tools (which routinely produce regretful viral content). VMP intentionally trades some maximum reach for ethical floors.

### 2.3 Prompt template for Stage 1

```
You are generating candidate memes for the TI Viral Meme Project.
Target platform: {PLATFORM}
Topic: {USER_TOPIC}
Audience GILE profile: {AUDIENCE_GILE}    // optional; defaults to "general"

Generate 20 distinct candidate memes. Each should:
- Be deliverable in the platform's native format (≤ 280 chars for X,
  ≤ 60 sec script for TikTok, image+caption for Instagram)
- Reward at least one prosocial or insight-bearing reaction
- Avoid cruelty, despair, or contempt as the primary emotional payload
- Aim for an "aha" recognition rather than a "huh" reaction

Return as a JSON array of {text, format, primary_emotion, intended_payoff}.
```

### 2.4 Implementation cost (MVP)

| Component | Tool | Cost |
|---|---|---|
| LLM for generation | Anthropic / OpenAI API (already integrated) | ≤ $5 per 1000 candidates |
| LLM for scoring | Same | ≤ $2 per 1000 scoring passes |
| Hosting | Streamlit on Replit (existing) | $0 marginal |
| Database for tracking generated memes + outcomes | PostgreSQL (already provisioned) | $0 marginal |
| **Total MVP build** | | **< $20** for full first prototype + 2000 test items |

### 2.5 What the MVP UI looks like (Streamlit on the existing hypercomputer port or a sibling app)

```
┌────────────────────────────────────────────┐
│  TI Viral Meme Project (VMP)               │
├────────────────────────────────────────────┤
│  Topic:          [_______________________]  │
│  Platform:       (X) TikTok ( ) Reddit ...  │
│  Audience:       [General / Tech / Wellness]│
│  GILE floor:     [G≥0.5  L≥0.4 (defaults)]  │
│  [ Generate 20 candidates → score → top 3 ] │
├────────────────────────────────────────────┤
│  Top candidate (V = 0.82):                  │
│    "..."                                    │
│    Breakdown: CONTENT 0.72 · NETWORK 0.55 · │
│               GILE 0.91 · interaction 0.18  │
│  [ Use this ]  [ Generate variants ]        │
└────────────────────────────────────────────┘
```

---

## 3. Strategic Placement

### 3.1 The placement matrix

The V-formula's NETWORK term already includes `platform_carrier` and `timing_alignment`. The placement strategy operationalizes these:

| Platform | Best GILE-meme format | Peak window (US-Eastern) | Authority lever |
|---|---|---|---|
| **X / Twitter** | 1–3 short text panels with image | Tue–Thu, 9–11 AM and 7–9 PM | Reply to high-follower account in same niche |
| **TikTok** | 15–45 sec talking-head or text-overlay | 6–10 PM weekday, 11 AM–3 PM weekend | Use trending sound at low volume |
| **Reddit** | Long-form text post in niche subreddit | Tues–Wed 7–10 AM (subreddit-specific) | Respect community norms (no surface promo) |
| **LinkedIn** | 5–8 line first-person essay | Tues–Thu 8–10 AM | Tag 2 first-degree connections genuinely relevant |
| **Instagram** | Carousel of 3–5 slides | Mon–Fri 11 AM–1 PM | Hashtag stack 5–10 mid-volume tags |

### 3.2 Cross-platform sequencing

The empirically supported pattern (Cheng et al. 2014 + Goel et al. 2016):

```
Day 0:  Seed on the platform with highest carrier coefficient for the meme's format
Day 1:  Cross-post adapted version to the second-best carrier
Day 2:  If V observed exceeds 1.5σ above predicted, push to the third platform
Day 3+: If a cascade is forming, do not interfere; if not, retire and regenerate
```

The "do not interfere" rule is critical and counter-intuitive — Goel et al. found that follow-up posts from the original poster *suppress* cascade growth more often than they help, because they fragment the conversation.

### 3.3 The GILE-audience match

The V-formula's δ-term predicts that GILE × NETWORK is multiplicative. Operationally this means: a high-G meme posted into a community with high baseline G-orientation (e.g., effective-altruism Twitter, certain wellness Instagram) will outperform the same meme posted to a low-G community by more than the additive sum of effects. The placement strategy therefore includes an explicit **audience-GILE-profiling step** before posting:

| Audience profile | Best meme GILE signature |
|---|---|
| Tech/builder communities | High I (insight), moderate G, low L sentimentality |
| Wellness/spirituality | High L, moderate I, low E urgency |
| Political/policy | High E (substrate-respect), moderate G, low L sentimentality |
| Academic | High I, high BOK_arm_concentration, low emotion |
| General entertainment | High emotion, moderate everything else |

This profiling is empirical — calibrate from the audience's recent top-100 posts and fit a single GILE vector per community.

---

## 4. Monetization Model

### 4.1 Three revenue streams

#### Stream 1 — Direct ad revenue from VMP-generated content

Brandon's existing properties (TI Sigma site, GSA, etc.) host the generated memes; ad revenue flows through standard channels (Google AdSense, sponsored newsletter sections, affiliate links where ethically appropriate).

| Assumption | Value |
|---|---|
| Memes generated per week | 20 (5/day × 4 days, weekend off) |
| Fraction reaching ≥ 10k views | 15% (calibrated against platform organic baselines) |
| Average RPM (revenue per 1000 views) at GILE-aligned content | $1.50 — $4.00 |
| Average viral meme reach (conditional on ≥ 10k) | 50,000 views |
| **Weekly revenue (median estimate)** | 20 × 0.15 × 50,000 × $0.0025 ≈ **$375/week** |
| **Annual run-rate (median estimate)** | **≈ $19,500/year** |

These are honest mid-range estimates. The 90% confidence interval is wide ($5k – $80k/year). The $80k upper end requires a single "breakout" meme per quarter; this is rare but not unprecedented for well-targeted GILE content.

#### Stream 2 — Subscription license to others

The VMP tool licensed to other creators / small businesses as a SaaS product:

| Tier | Price/month | Includes | Target customer |
|---|---|---|---|
| **Solo** | $19 | 100 generations/month, 1 platform, basic scoring | Indie creator, journalist |
| **Pro** | $79 | 1000 generations/month, all platforms, full V-breakdown, audience profiling | Small marketing agency, consultant |
| **Studio** | $299 | Unlimited, multi-user, custom GILE-floor settings, API access | Agencies, small media companies |
| **Enterprise** | $1500+ | Custom integration, white-label option, dedicated support | Brands that want VMP under their own UX |

Realistic Year-1 subscriber projection if marketed via Brandon's existing audience + 1 viral demo:

| Tier | Subscribers (median) | Monthly revenue |
|---|---|---|
| Solo | 80 | $1,520 |
| Pro | 15 | $1,185 |
| Studio | 3 | $897 |
| Enterprise | 0 (Year 1 unrealistic) | $0 |
| **Total** | 98 | **≈ $3,600/month → $43,200/year** |

This is the **most uncertain** stream — depends entirely on marketing reach and product-market fit. Honest range: $0 – $80k Year 1.

#### Stream 3 — Licensing the formula itself (academic + commercial)

If the formula achieves the §0 empirical target (R² > 0.30 on held-out data, beating prior art), the formula itself becomes IP. Two licensing paths:

- **Academic open-access** with attribution (free; builds credibility, drives the SaaS subscriber funnel).
- **Commercial license** for inclusion in third-party tools (Hootsuite, Buffer, etc. — $5k – $50k per integration, one-time + revenue share).

This stream is gated entirely on §5 empirical validation. **No revenue from Stream 3 until the formula is validated and published.**

### 4.2 Aggregate run-rate (median, Year 1)

| Stream | Median estimate |
|---|---|
| Direct ad revenue | $19,500 |
| SaaS subscription | $43,200 |
| Formula licensing | $0 (not validated yet) |
| **Total Year-1 median** | **≈ $62,700** |
| **Total Year-1 90% CI** | **$5k – $200k** |

The wide CI reflects honest uncertainty. The downside case ($5k) is failure to launch SaaS + few breakout memes. The upside case ($200k) requires SaaS PMF + 1–2 commercial licenses + steady ad revenue.

### 4.3 Costs to deduct

| Item | Annual cost |
|---|---|
| LLM API (generation + scoring at 10k items/month) | $600 |
| Hosting (existing Replit infra extended) | $300 |
| Domain + landing page | $50 |
| Payment processing (Stripe at 2.9%) | ~$1,800 (on $62k revenue) |
| **Total annual cost** | **≈ $2,750** |

Net Year-1 median ≈ **$60,000** before Brandon's time, or about **96% gross margin** on the median revenue case. The economics are favorable when they work; the question is purely whether the formula validates and the SaaS reaches subscribers.

---

## 5. Pre-Registered Empirical Validation Plan (Program F)

Per the framework's standing rule (URB #401's null-handling, URB #781's pre-registration commitment), VMP must commit to its empirical bar before data collection.

### 5.1 Hypotheses

- **H1 (formula accuracy):** On a held-out test set of ≥ 500 social media posts (with measured engagement), the V-formula achieves R² > 0.30 against log(view count + 1), beating Goel et al.'s baseline.
- **H2 (GILE contribution):** The γ and δ terms together contribute additional explained variance ΔR² > 0.05 over a CONTENT + NETWORK only baseline (likelihood ratio test, p < 0.01).
- **H3 (cascade prediction):** On the binary "doubles within 24 hours" task, V-formula achieves AUC > 0.75 on held-out data, matching or beating Cheng et al.

### 5.2 Data sources (free)

- X / Twitter API (free tier for ≤ 1500 posts/month) — primary
- Pushshift Reddit archive — secondary
- TikTok scraping via free `TikTokApi` Python package — tertiary

### 5.3 Schedule (added to the existing 9-week plan as Program F, parallel to A–E)

| Week | VMP-specific activity |
|---|---|
| 1 | Pre-register VMP hypotheses to OSF; build MVP generator (Streamlit) |
| 2 | Pull training data (1500 posts), label with V-formula features |
| 3 | Fit coefficients via ridge regression with platform-stratified CV |
| 4 | Test on held-out 500 posts; publish results regardless of sign |
| 5–9 | If H1–H3 confirmed: launch SaaS landing page; begin Stream 2 |

### 5.4 What null looks like (and what we do with it)

- If H1 fails: V-formula is no better than published baselines. Publish honestly. The generator still works as a creativity tool; the SaaS pitch is downgraded from "predicts virality" to "produces GILE-compatible candidates that you then judge."
- If H2 fails (γ, δ ≈ 0): GILE features add no predictive lift. The framework's deeper claim (that GILE-coherence has empirical signature in social diffusion) is falsified at this level. This is publication-worthy — it sharpens the framework by ruling out one hypothesis.
- If H3 fails but H1/H2 succeed: VMP predicts steady-state engagement well but not cascades. Still commercially useful for the Pro tier; downgrade the marketing claim.

---

## 6. Build Plan and What I'm Asking You to Approve

### 6.1 Proposed sequencing

1. **Today (this URB):** Project charter ratified.
2. **Next session:** I build the Streamlit MVP generator (Stages 1–4 of §2.1) on a sibling port to the existing hypercomputer app. ~half-day work; cost < $5 in API testing.
3. **Week 1–2:** Pre-registration to OSF + training data pull.
4. **Week 3–4:** Coefficient fitting + held-out validation.
5. **Week 5+:** Conditional launch of SaaS landing page if validation passes.

### 6.2 Open questions for you (Brandon)

1. **The two GILE hard floors (G ≥ 0.5, L ≥ 0.4 with self-Love admissible).** Confirm or adjust thresholds. These are the deontological gates that distinguish VMP from generic engagement-maximizers.
2. **Streamlit MVP location.** Sibling port to hypercomputer, or extend the hypercomputer app with a VMP tab? Latter is faster; former is cleaner for the SaaS product later.
3. **Should the SaaS launch wait for Program F validation results** (clean ethics), or **launch as "generator" first and add "predictor" claim post-validation** (faster revenue, but accept that the predictor claim is unsupported until week 5)? My recommendation: wait. Brandon's call.
4. **Naming.** "TI Viral Meme Project (VMP)" is the project name. Should the user-facing product be called the same, or something like **"Spectre"** (after the Einstein tile, reinforcing the §1.5 stickiness claim) / **"Resonance"** (emphasizing GILE-audience match) / **"Carrier"** (network metaphor)?

### 6.3 What I will NOT do without your sign-off

- No code committed to the repo until you approve §6.1 sequencing and answer §6.2 questions.
- No marketing copy written.
- No claims of "unprecedented accuracy" published until §5 validates.
- No use of the framework's IP in a way that conflates the SaaS product with the academic framework — VMP is a commercial application of TI; TI itself stays open-access.

---

## 7. Slogan Form

> **URB #783:** TI Viral Meme Project opened. Virality formula V = α·CONTENT + β·NETWORK + γ·GILE + δ·(GILE × NETWORK) + ε with 17 explicit weights. Generator architecture is a four-stage pipeline (LLM generate → GILE-floor filter → V-score → top-3) buildable as a Streamlit MVP for under $20. Strategic placement is a platform-by-format-by-time matrix with explicit GILE-audience matching. Monetization is three streams (direct ad revenue, SaaS subscription, formula licensing) with median Year-1 estimate ≈ $63k against ≈ $3k cost (96% margin when it works); honest 90% CI is $5k–$200k. Pre-registered as Program F with R² > 0.30, ΔR²(GILE) > 0.05, AUC > 0.75 thresholds; null results published with same clarity as positives. Two non-negotiable deontological gates (G ≥ 0.5, L ≥ 0.4) prevent the system from optimizing toward viral cruelty or despair. Four open questions for Brandon before implementation begins.

---

*Brandon Charles Emerick, April 21, 2026 — seven hundred eighty-third URB. TI Viral Meme Project charter. Honest baseline against published virality literature (Berger & Milkman R² ≈ 0.20, Goel et al. R² ≈ 0.30, Cheng et al. AUC ≈ 0.75) with explicit improvement targets. Generator buildable for under $20. Median Year-1 revenue ≈ $63k at 96% margin; honest range $5k–$200k. No code committed and no marketing launched until project author signs off on §6.2 open questions.*
