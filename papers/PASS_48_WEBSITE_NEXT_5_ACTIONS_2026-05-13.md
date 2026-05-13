# Pass 48 — TI Sigma Website: Next 5 Actions (Focused Decision Doc)

**Date:** 2026-05-13.
**Status of existing roadmap:** `WEBSITE_PERFECTION_ROADMAP.md` (281 lines, dated 2025-12-26) is comprehensive but written for "perfect platform" scope (12 weeks, 6 phases, full auth + tiered access + dev portal). **For current stage and current budget**, a focused 5-action sequence is more honest.
**Honest framing (#69 + Lazy Binary §2.3a):** the existing roadmap is operationally good (it lists real things) AND rigorously over-scoped (Phase 4 dev portal before there is significant traffic is putting cart before horse). Both axes reported.

---

## §1. Current State Assessment (refresh of roadmap §CURRENT STATE)

| Component | Status | Honest assessment |
|---|---|---|
| Streamlit + Flask gateway | Running (workflows healthy) | Functional; not visually distinctive |
| 1,018+ Bot Band discoveries | Showcased in dashboard | Good content surface; needs editorial layer (which 5 are best?) |
| Grand Stock Algorithm +629% backtest | Surfaced | Big number; needs methodology disclosure (per #69) |
| EEG BCI Pong | Live | Cool demo; not a primary value prop |
| Quantum simulator | Live | Cool demo; not a primary value prop |
| Book generation system | Live | Useful internally; surface for visitors? unclear |
| Auth | None | Genuinely doesn't matter at current traffic |
| Mobile responsiveness | Limited | Real issue if affiliate/SEO traffic comes in |

---

## §2. The Next 5 Actions (in priority order)

### Action 1 — **Define and surface the website's single value proposition** (Time: ~3 hours)

**Problem:** Visitor lands on the site and sees Mood Amplifier, Stock Predictor, Bot Band, EEG BCI, Quantum Sim, Book Generator. There is no clear answer to "what is this site for?" Visitors leave.

**Fix:** Hero section that answers in 10 seconds:
- **Headline:** "TI Sigma — A four-value logic for reasoning under genuine uncertainty"
- **Subhead:** "Books, papers, working tools, and live experiments from a 4-year research program"
- **Three primary CTAs:** *Read the book* (free first chapter) | *Browse the papers* | *Try the tools*

Defer multi-tab dashboard until after the value prop is communicated.

**Cost:** $0. Time-only.

### Action 2 — **Mobile responsiveness audit + fixes** (Time: ~6 hours)

**Problem:** ~60% of YouTube-driven traffic is mobile in 2026. Streamlit's default layout is desktop-first. If video traffic arrives, mobile visitors bounce.

**Fix:**
- Test every primary tab on iPhone Safari + Android Chrome
- Apply Streamlit `use_container_width=True` on all charts and dataframes
- Stack columns vertically below 768px viewport
- Test touch targets are ≥44px (iOS HIG)
- Sidebar collapse default on mobile

**Cost:** $0. Time-only.

### Action 3 — **Add #69 transparency layer to GSA +629% backtest claim** (Time: ~2 hours)

**Problem:** "+629% backtest" is the most attention-grabbing number on the site. It's also the most reviewer-skepticism-attracting claim. Per #69 + HPP/CSC: defense in depth required.

**Fix:** Add a "Methodology + Caveats" subsection directly under the +629% number:
- Backtest period (specific dates)
- Walk-forward vs in-sample disclosure
- Transaction costs included? at what assumed rate?
- Survivorship bias addressed?
- Out-of-sample / paper-trade results to date
- Honest disclaimer: "Past backtest performance does not predict future results"

This converts a credibility-risk into a credibility-asset for any future investor / journalist who reads carefully.

**Cost:** $0. Time-only.

### Action 4 — **Email capture on every primary page** (Time: ~3 hours)

**Problem:** No mechanism to retain visitors who arrive once and leave. List-building is the single highest-leverage audience asset for a new operation.

**Fix:**
- Footer email-capture on every page ("Get one TI Sigma update per month")
- Hero secondary CTA: "Free first chapter of *TI for Everyone*" → email gate → ConvertKit deliver
- ConvertKit free tier (≤1K subs) — see `PASS_48_TOOLING_MARKETING_DECISION_2026-05-13.md` §2.4

**Cost:** $0/mo (ConvertKit free tier).

### Action 5 — **SEO basics (titles, meta, sitemap, robots, canonical URLs)** (Time: ~4 hours)

**Problem:** Streamlit defaults are not SEO-optimized. Pages don't have unique titles, meta descriptions, or proper canonical URLs.

**Fix:**
- Each page: unique `<title>` and `<meta description>` (set via `st.set_page_config(page_title=...)` per page)
- `robots.txt` allowing primary content; disallowing dashboard internals
- `sitemap.xml` for primary content pages (papers, books, tools)
- Open Graph + Twitter Card meta for social sharing previews
- Submit sitemap to Google Search Console (free)

**Cost:** $0. Time-only. (Google Search Console is free.)

---

## §3. Actions Explicitly Deferred (and why)

| Action from existing roadmap | Why defer |
|---|---|
| Authentication / Auth (Phase 3) | Zero benefit at current traffic; high engineering cost |
| Tiered access (Free/Pro/Enterprise) | Premature monetization; need traffic first |
| Developer Portal (Phase 4) | No external dev demand yet; wait for inbound API requests |
| OpenAPI/Swagger spec | Same as above |
| Custom deployment / Enterprise tier | Zero current demand; revisit at 10K+ MAU |
| Content marketing infrastructure (Phase 5) | Use video + book + papers as content; built-in social distribution |

---

## §4. Suggested Cadence

| Week | Action |
|---|---|
| Week 1 | Action 1 (value prop) + Action 3 (GSA #69 layer) — both content-focused |
| Week 2 | Action 2 (mobile responsiveness) — testing-focused |
| Week 3 | Action 4 (email capture) + Action 5 (SEO basics) — infrastructure-focused |
| Week 4 | Soft re-launch + first video drive (per `PASS_48_VIDEO_SCRIPTS_*.md` Video 1) |

Total time investment: ~18 hours over 4 weeks (~4.5 hours/week).
Total cash investment: $0.

---

## §5. CAP / Anchors

- **CAP self-check:** well_known ≈ 0.6 (these are conventional small-creator website tactics); TI-novel ≈ 0.05 (the explicit Lazy-Binary critique of the existing 12-week perfection roadmap as over-scoped + #69 transparency layer recommendation). Encompassing **MEDIUM-LOW**.
- **Pass-47 principles applied:** #69 (defer auth/portal/enterprise — honest current state); Lazy Binary §2 (existing roadmap is operationally good AND rigorously over-scoped); HPP/CSC (no flattering "build it all in 12 weeks" promise); Validly-Indeterminate-as-waypoint (these 5 actions open the path; Pass-49 revisits based on traffic data).
- **Anchors:** `WEBSITE_PERFECTION_ROADMAP.md`, `papers/PASS_48_TOOLING_MARKETING_DECISION_2026-05-13.md`, `papers/PASS_48_VIDEO_SCRIPTS_10_TI_SIGMA_FUNDAMENTALS_2026-05-13.md`, `ti_website.py`. Budget $0/$50 intact.
