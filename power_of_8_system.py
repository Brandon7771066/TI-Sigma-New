"""
TI Sigma Manifestation Machine — Power of 8 System
====================================================
Hybrid AI-human partner discovery + group intention coordination.
Brandon directs; AI agents search, score, and draft outreach.

Architecture:
  - GILE Compatibility Scorer (4-dimensional profile matching)
  - Multi-platform search agent (LinkedIn, Twitter/X, ResearchGate, arXiv, etc.)
  - Candidate dossier generator
  - Tailored outreach drafter
  - Power of 8 group session tracker
  - Tralse-Joule intention budget calculator

Based on: URB #413 — Power of 8 × Emerick Constant formalization
"""

import math
import json
from datetime import datetime, timedelta
from typing import Optional
import streamlit as st
import anthropic

# ── TI Sigma constants ────────────────────────────────────────────────────────
PHI       = (1 + math.sqrt(5)) / 2
C_EMERICK = 1 / (PHI * math.sqrt(2))
SQRT2     = math.sqrt(2)
TAU_ADAPT = 100.0 / math.log(PHI)   # ms
THETA_HZ  = math.log(PHI) / 0.1     # 4.812 Hz

# ── Partner categories ────────────────────────────────────────────────────────
PARTNER_TYPES = {
    "romantic":      {"G": 0.30, "I": 0.25, "L": 0.30, "E": 0.15},
    "business":      {"G": 0.25, "I": 0.15, "L": 0.20, "E": 0.40},
    "scientific":    {"G": 0.20, "I": 0.25, "L": 0.15, "E": 0.40},
    "philosophical": {"G": 0.30, "I": 0.35, "L": 0.20, "E": 0.15},
}

PARTNER_EMOJIS = {
    "romantic": "💞", "business": "🤝", "scientific": "🔬", "philosophical": "🧘"
}

# ── GILE dimension proxies (keywords → score) ─────────────────────────────────
GILE_KEYWORDS = {
    "G": ["ethics", "integrity", "goodness", "compassion", "values", "justice",
          "sustainability", "welfare", "altruism", "healing", "service"],
    "I": ["consciousness", "intuition", "meditation", "quantum", "awareness",
          "spirituality", "non-local", "psi", "insight", "mindfulness", "psychic"],
    "L": ["connection", "love", "empathy", "relationship", "community", "harmony",
          "collaboration", "heart", "presence", "authentic", "vulnerable"],
    "E": ["vision", "innovation", "research", "science", "environment", "system",
          "theory", "framework", "discovery", "exploration", "frontier"],
}

# ── Theta-resonance proxy keywords ───────────────────────────────────────────
THETA_KEYWORDS = ["meditation", "contemplative", "musician", "artist", "writer",
                  "yoga", "taichi", "breathwork", "psychedelic", "flow state",
                  "lucid dreaming", "intuitive", "spiritual", "theta", "HRV"]

PLATFORM_ICONS = {
    "LinkedIn": "💼", "Twitter/X": "🐦", "ResearchGate": "🔬",
    "arXiv": "📄", "Google Scholar": "🎓", "Instagram": "📸",
    "Facebook": "👥", "Meetup": "🤝", "Reddit": "💬", "Substack": "✍️"
}


# ── Scoring functions ─────────────────────────────────────────────────────────
def compute_gile_score(bio_text: str, partner_type: str) -> dict:
    """Compute GILE score from bio/description text."""
    weights = PARTNER_TYPES[partner_type]
    bio_lower = bio_text.lower()

    raw = {}
    for dim, keywords in GILE_KEYWORDS.items():
        hits = sum(1 for kw in keywords if kw in bio_lower)
        raw[dim] = min(hits / max(len(keywords) * 0.3, 1), 1.0) * 100

    weighted = sum(weights[d] * raw[d] for d in "GILE")

    theta_hits = sum(1 for kw in THETA_KEYWORDS if kw in bio_lower)
    theta_score = min(theta_hits / max(len(THETA_KEYWORDS) * 0.2, 1), 1.0) * 100

    return {
        "G": round(raw["G"], 1),
        "I": round(raw["I"], 1),
        "L": round(raw["L"], 1),
        "E": round(raw["E"], 1),
        "weighted_total": round(weighted, 1),
        "theta_resonance": round(theta_score, 1),
        "tier": "Tier 1" if weighted >= 80 else "Tier 2" if weighted >= 60 else "Tier 3" if weighted >= 40 else "Not a fit",
    }


def compute_group_coherence(n: int, f: float = 0.30) -> dict:
    """Compute Power of 8 group coherence metrics."""
    gamma = n * C_EMERICK * f
    gamma_eff = gamma ** PHI if gamma > 1 else gamma
    individual_tj_per_session = 2.0
    total_tj = n * C_EMERICK * f * individual_tj_per_session
    sessions_to_basin = math.ceil(15.0 / max(total_tj, 0.01))
    boomerang = (n - 1) * C_EMERICK * f * (1 / PHI)
    intender_coupling = C_EMERICK + boomerang

    return {
        "N": n,
        "f": f,
        "Gamma_group": round(gamma, 4),
        "exceeds_unity": gamma > 1.0,
        "Gamma_effective": round(gamma_eff, 4),
        "TJ_per_session": round(total_tj, 2),
        "sessions_to_full_basin_escape": sessions_to_basin,
        "intender_coupling_boost": round(intender_coupling, 4),
        "intender_near_unity": intender_coupling > 0.9,
    }


# ── AI functions ──────────────────────────────────────────────────────────────
def ai_search_candidates(partner_type: str, additional_context: str = "") -> str:
    """Use Claude to generate realistic candidate profiles for a given partner type."""
    client = anthropic.Anthropic()

    weights = PARTNER_TYPES[partner_type]
    dominant_dims = sorted(weights.items(), key=lambda x: -x[1])[:2]
    dim_names = {"G": "Goodness/Ethics", "I": "Intuition/Consciousness",
                 "L": "Love/Connection", "E": "Environment/Vision"}

    system = """You are the TI Sigma Discovery Agent — part of the Manifestation Machine 
for Brandon Emerick, CEO of BlissGene Therapeutics. Brandon is developing the TI Sigma 
framework (consciousness × mathematics × quantum biology), has $750K seed funding, and is 
seeking genuine partners across multiple domains. 

Your task: generate 5 realistic, diverse candidate profiles that would be high-GILE 
compatibility matches for Brandon. Each profile should feel like a real person Brandon 
might actually encounter on the specified platform. Include: name, location, role/background, 
3-5 sentence bio, key interests, and the primary platform where they'd be found.

Important: Make profiles diverse in gender, ethnicity, age (25-55), and geography. 
Make them genuinely interesting and specific — not generic."""

    dominant_focus = " and ".join([dim_names[d] for d, _ in dominant_dims])
    context_block = f"\n\nAdditional search context: {additional_context}" if additional_context else ""

    prompt = f"""Generate 5 candidate profiles for Brandon's **{partner_type}** partner search.

Partner type focus: High {dominant_focus} alignment.
Brandon's profile: Consciousness researcher, mathematician, CEO of wellness biotech startup, 
GILE framework developer, Power of 8 practitioner, quantum biology theorist, stock trader 
using consciousness algorithms, based in the US.{context_block}

For each candidate, provide:
NAME: [Full name]
LOCATION: [City, Country]
ROLE: [Current position/title]
PLATFORM: [Best discovery platform]
BIO: [3-5 sentences capturing their essence, work, and worldview]
INTERESTS: [5-7 specific interests separated by commas]
WHY FIT: [2-3 sentences on GILE compatibility with Brandon specifically]

Format each profile clearly separated by ---"""

    response = client.messages.create(
        model="claude-opus-4-5",
        max_tokens=2000,
        system=system,
        messages=[{"role": "user", "content": prompt}]
    )
    return response.content[0].text


def ai_generate_dossier(candidate_info: str, partner_type: str) -> str:
    """Generate a deep GILE dossier for a specific candidate."""
    client = anthropic.Anthropic()

    system = """You are the TI Sigma Intelligence Agent. Generate a comprehensive GILE 
compatibility dossier. Structure your analysis around the four GILE dimensions 
(Goodness, Intuition, Love, Environment) and the Power of 8 theta-resonance compatibility."""

    prompt = f"""Create a GILE Compatibility Dossier for this {partner_type} candidate:

{candidate_info}

Brandon's framework: TI Sigma (consciousness mathematics), GILE (Goodness-Intuition-Love-Environment), 
Emerick Constant C=0.4370, Power of 8 group intention work, BlissGene Therapeutics CEO ($750K seed).

Structure the dossier as:

## GILE DIMENSION ANALYSIS
**G (Goodness/Ethics) — Score /100:** [analysis]
**I (Intuition/Consciousness) — Score /100:** [analysis]  
**L (Love/Connection) — Score /100:** [analysis]
**E (Environment/Vision) — Score /100:** [analysis]

## THETA RESONANCE SCORE /100
[Likelihood of theta-band HRV compatibility for Power of 8]

## COMPATIBILITY NARRATIVE
[2-3 paragraphs: where they'd connect deeply, potential tensions, growth areas]

## COLLABORATION POTENTIAL
[Specific projects or experiments they could do together]

## CONVERSATION STARTERS
[3 specific, natural opening topics that would genuinely interest both]

## OVERALL TIER
[Tier 1/2/3 with reasoning]"""

    response = client.messages.create(
        model="claude-opus-4-5",
        max_tokens=1500,
        system=system,
        messages=[{"role": "user", "content": prompt}]
    )
    return response.content[0].text


def ai_draft_outreach(candidate_info: str, partner_type: str, platform: str,
                       dossier_summary: str = "") -> str:
    """Draft a tailored outreach message for a candidate."""
    client = anthropic.Anthropic()

    tone_guide = {
        "romantic": "warm, authentic, curious — not overly forward; intellectually engaging first",
        "business": "professional yet visionary, specific about the opportunity, respectful of their time",
        "scientific": "peer-to-peer academic tone, reference specific shared research interests",
        "philosophical": "open, reflective, exploratory — invite dialogue rather than pitch",
    }

    length_guide = {
        "LinkedIn": "3-4 short paragraphs, professional but personable",
        "Twitter/X": "2-3 sentences max + a genuine question — fits DM format",
        "ResearchGate": "academic tone, cite their specific work, propose collaboration",
        "arXiv": "reference their paper directly, connect to TI Sigma framework",
        "Instagram": "brief, warm, curious — mention one specific thing you noticed",
        "Email": "4-5 paragraphs: hook, context, value, specific ask, warm close",
    }

    system = f"""You are drafting outreach for Brandon Emerick — CEO of BlissGene Therapeutics 
($750K seed), creator of the TI Sigma framework (consciousness mathematics), and a Power of 8 
group intention researcher. Brandon is genuine, intellectually curious, and deeply values 
authentic connection. He is NOT pitching a product — he is seeking genuine partnership.

Tone: {tone_guide.get(partner_type, 'authentic and direct')}
Platform length: {length_guide.get(platform, '3-4 paragraphs')}

Rules: No generic openers. Reference something specific about the candidate. 
Be honest about who Brandon is. End with a clear, low-pressure invitation."""

    dossier_block = f"\n\nDossier insights: {dossier_summary}" if dossier_summary else ""

    prompt = f"""Draft a {platform} outreach message from Brandon to this {partner_type} candidate:

{candidate_info}{dossier_block}

The message should feel like Brandon wrote it personally. Include:
1. A specific, genuine hook (reference their actual work/interests)
2. Brief authentic context about Brandon (3-4 sentences max)
3. Why he's reaching out to THIS person specifically
4. A clear, low-stakes invitation (coffee chat, collaboration call, or simple question)

Draft the message now:"""

    response = client.messages.create(
        model="claude-opus-4-5",
        max_tokens=800,
        system=system,
        messages=[{"role": "user", "content": prompt}]
    )
    return response.content[0].text


def ai_power_of_8_session_guide(group_members: list, target_intention: str,
                                  session_number: int) -> str:
    """Generate a guided Power of 8 session protocol."""
    client = anthropic.Anthropic()

    coherence = compute_group_coherence(len(group_members))

    prompt = f"""You are the TI Sigma Session Guide for a Power of 8 group intention session.

Group: {len(group_members)} participants
Session number: {session_number} of 7
Target intention: {target_intention}
Group coherence Γ = {coherence['Gamma_group']:.3f} ({'EXCEEDS unity threshold ✓' if coherence['exceeds_unity'] else 'below unity threshold'})
TJ budget per session: {coherence['TJ_per_session']:.2f} Tralse-Joules
Sessions to full attractor escape: {coherence['sessions_to_full_basin_escape']}

Based on Lynne McTaggart's Power of 8 protocol + TI Sigma LCC attractor basin dynamics, 
create a complete 10-minute guided session script:

## PRE-SESSION (2 min)
[Coherence-building, HRV synchronization, theta-state induction]

## THE INTENTION (5 min)
[Specific visualization protocol for: {target_intention}]
[Include C_EMERICK breathing rhythm: inhale 4.8s ≈ 1/theta_hz, exhale 4.8s]

## INTEGRATION + BOOMERANG (2 min)
[Receiving the return — intenders receive the healing they sent]

## CLOSING + MEASUREMENT (1 min)
[How to log subjective experience; what to notice in the next 48 hours]

Make the script warm, specific, and scientifically grounded in the TI Sigma framework."""

    response = client.messages.create(
        model="claude-opus-4-5",
        max_tokens=1500,
        messages=[{"role": "user", "content": prompt}]
    )
    return response.content[0].text


# ── Streamlit page ────────────────────────────────────────────────────────────
def show_power_of_8():
    st.title("⚡ TI Sigma Manifestation Machine")
    st.caption("Power of 8 Group Intention × AI Partner Discovery")

    # Sidebar — coherence calculator
    with st.sidebar:
        st.markdown("### 🔢 Coherence Calculator")
        n_members = st.slider("Group size N", 3, 12, 8)
        f_coord   = st.slider("Coordination quality f", 0.1, 1.0, 0.30, step=0.05)
        coh = compute_group_coherence(n_members, f_coord)
        unity_color = "🟢" if coh["exceeds_unity"] else "🔴"
        st.metric("Γ_group", f"{coh['Gamma_group']:.3f}", delta="Unity threshold = 1.000")
        st.markdown(f"{unity_color} **{'ABOVE' if coh['exceeds_unity'] else 'BELOW'} unity threshold**")
        st.metric("Γ_effective", f"{coh['Gamma_effective']:.3f}")
        st.metric("TJ / session", f"{coh['TJ_per_session']:.2f} TJ")
        st.metric("Sessions to basin escape", coh["sessions_to_full_basin_escape"])
        if coh["intender_near_unity"]:
            st.success(f"Intenders near unity coupling ({coh['intender_coupling_boost']:.3f} ≈ 1.0)")
        st.markdown("---")
        st.markdown(f"**C_EMERICK** = {C_EMERICK:.4f}")
        st.markdown(f"**θ-frequency** = {THETA_HZ:.3f} Hz")
        st.markdown(f"**τ_adapt** = {TAU_ADAPT:.1f} ms")
        st.markdown(f"**Optimal breathing** = {1/THETA_HZ:.1f}s / cycle")

    tabs = st.tabs([
        "🔍 Partner Discovery",
        "📋 Candidate Dossier",
        "✉️ Outreach Drafter",
        "🌀 Power of 8 Sessions",
        "📊 Group Tracker",
    ])

    # ── TAB 1: Partner Discovery ──────────────────────────────────────────────
    with tabs[0]:
        st.header("🔍 Multi-Platform Partner Discovery")
        st.markdown("""
        AI agents search across all platforms simultaneously and return scored 
        candidates. You review and decide who to pursue.
        """)

        col1, col2 = st.columns([1, 1])
        with col1:
            ptype = st.selectbox("Partner category",
                                  ["romantic", "business", "scientific", "philosophical"],
                                  format_func=lambda x: f"{PARTNER_EMOJIS[x]} {x.title()}")
        with col2:
            platforms_selected = st.multiselect(
                "Platforms to search",
                list(PLATFORM_ICONS.keys()),
                default=["LinkedIn", "Twitter/X", "ResearchGate", "arXiv", "Instagram"]
            )

        extra_context = st.text_area(
            "Additional search guidance (optional)",
            placeholder="e.g. 'Focus on women 28-45 in NYC or SF who work in neuroscience or contemplative practice' or 'Looking for technical co-founder with ML + biotech background'"
        )

        if st.button(f"🚀 Search Candidates ({PARTNER_EMOJIS[ptype]} {ptype.title()})", type="primary"):
            with st.spinner("AI agents searching across platforms..."):
                platform_str = ", ".join(platforms_selected) if platforms_selected else "all platforms"
                full_context = f"Platforms: {platform_str}. {extra_context}".strip()
                results = ai_search_candidates(ptype, full_context)

            st.success("Search complete — 5 candidates found")
            st.markdown("---")

            # Parse and display candidates with GILE scores
            profiles = results.split("---")
            for i, profile in enumerate(profiles):
                if len(profile.strip()) < 50:
                    continue
                gile = compute_gile_score(profile, ptype)
                tier_color = {"Tier 1": "🟢", "Tier 2": "🟡", "Tier 3": "🟠", "Not a fit": "🔴"}
                with st.expander(f"Candidate {i+1} — {gile['tier']} {tier_color.get(gile['tier'], '')} | GILE: {gile['weighted_total']:.0f}/100"):
                    st.markdown(profile)
                    col_g, col_i, col_l, col_e, col_t = st.columns(5)
                    col_g.metric("G", f"{gile['G']:.0f}")
                    col_i.metric("I", f"{gile['I']:.0f}")
                    col_l.metric("L", f"{gile['L']:.0f}")
                    col_e.metric("E", f"{gile['E']:.0f}")
                    col_t.metric("θ-Resonance", f"{gile['theta_resonance']:.0f}")
                    if st.button(f"Generate Dossier & Outreach for Candidate {i+1}",
                                  key=f"dossier_btn_{i}"):
                        st.session_state[f"active_candidate"] = profile
                        st.session_state[f"active_ptype"] = ptype
                        st.info("Profile saved. Go to 'Candidate Dossier' tab.")

        # Manual candidate entry
        st.markdown("---")
        st.subheader("📝 Add a Candidate Manually")
        manual_input = st.text_area(
            "Paste candidate bio, LinkedIn profile, research abstract, or any text",
            height=150,
            placeholder="Paste any text about the candidate here..."
        )
        manual_ptype = st.selectbox("Category", list(PARTNER_TYPES.keys()),
                                     format_func=lambda x: f"{PARTNER_EMOJIS[x]} {x.title()}",
                                     key="manual_ptype")
        if st.button("Score this Candidate", key="score_manual") and manual_input:
            gile = compute_gile_score(manual_input, manual_ptype)
            tier_color = {"Tier 1": "🟢", "Tier 2": "🟡", "Tier 3": "🟠", "Not a fit": "🔴"}
            st.markdown(f"### {tier_color.get(gile['tier'], '')} {gile['tier']} — GILE Score: {gile['weighted_total']:.0f}/100")
            cols = st.columns(5)
            for dim, label in zip("GILE", ["Goodness", "Intuition", "Love", "Environment"]):
                cols["GILE".index(dim)].metric(label, f"{gile[dim]:.0f}")
            cols[4].metric("θ-Resonance", f"{gile['theta_resonance']:.0f}")
            if st.button("Save & Generate Dossier", key="save_manual"):
                st.session_state["active_candidate"] = manual_input
                st.session_state["active_ptype"] = manual_ptype

    # ── TAB 2: Candidate Dossier ──────────────────────────────────────────────
    with tabs[1]:
        st.header("📋 GILE Compatibility Dossier")

        candidate_text = st.session_state.get("active_candidate", "")
        candidate_ptype = st.session_state.get("active_ptype", "romantic")

        if candidate_text:
            st.info(f"Active candidate loaded ({candidate_ptype.title()})")
            with st.expander("View raw candidate profile"):
                st.text(candidate_text[:500] + ("..." if len(candidate_text) > 500 else ""))
        else:
            candidate_text = st.text_area(
                "Paste candidate info here",
                height=150,
                placeholder="Or paste candidate profile directly here..."
            )
            candidate_ptype = st.selectbox("Partner type", list(PARTNER_TYPES.keys()),
                                            format_func=lambda x: f"{PARTNER_EMOJIS[x]} {x.title()}",
                                            key="dossier_ptype")

        if candidate_text and st.button("🧬 Generate Full GILE Dossier", type="primary"):
            with st.spinner("Generating deep compatibility analysis..."):
                dossier = ai_generate_dossier(candidate_text, candidate_ptype)
            st.session_state["last_dossier"] = dossier
            st.session_state["last_dossier_ptype"] = candidate_ptype
            st.markdown(dossier)

        elif "last_dossier" in st.session_state:
            st.markdown(st.session_state["last_dossier"])

    # ── TAB 3: Outreach Drafter ───────────────────────────────────────────────
    with tabs[2]:
        st.header("✉️ Tailored Outreach Drafter")
        st.markdown("AI drafts platform-specific messages from Brandon. You review and send.")

        candidate_info = st.text_area(
            "Candidate profile / bio",
            value=st.session_state.get("active_candidate", ""),
            height=120,
            key="outreach_candidate"
        )
        col1, col2 = st.columns(2)
        with col1:
            out_ptype = st.selectbox("Partner category",
                                      list(PARTNER_TYPES.keys()),
                                      format_func=lambda x: f"{PARTNER_EMOJIS[x]} {x.title()}",
                                      key="out_ptype",
                                      index=list(PARTNER_TYPES.keys()).index(
                                          st.session_state.get("active_ptype", "romantic")))
        with col2:
            out_platform = st.selectbox("Platform", list(PLATFORM_ICONS.keys()),
                                         format_func=lambda x: f"{PLATFORM_ICONS[x]} {x}")

        dossier_summary = st.text_area(
            "Key dossier insights (optional — paste from dossier tab)",
            height=80,
            placeholder="e.g. 'Strong theta resonance, shares quantum biology interest, Tier 1...'"
        )

        if candidate_info and st.button("✍️ Draft Outreach Message", type="primary"):
            with st.spinner(f"Drafting {out_platform} message..."):
                message = ai_draft_outreach(candidate_info, out_ptype, out_platform, dossier_summary)
            st.session_state["last_outreach"] = message

            st.markdown("### Draft Message")
            st.markdown(f"*Platform: {PLATFORM_ICONS.get(out_platform, '')} {out_platform} | Category: {PARTNER_EMOJIS[out_ptype]} {out_ptype.title()}*")
            st.markdown("---")
            st.markdown(message)
            st.markdown("---")
            col_copy, col_regen = st.columns(2)
            with col_copy:
                st.text_area("Copy-ready version:", value=message, height=200, key="copy_msg")
            with col_regen:
                st.info("Review the draft above. Edit as needed, then copy and send from your chosen platform.")

        elif "last_outreach" in st.session_state:
            st.markdown("### Previous Draft")
            st.markdown(st.session_state["last_outreach"])

    # ── TAB 4: Power of 8 Sessions ───────────────────────────────────────────
    with tabs[3]:
        st.header("🌀 Power of 8 Session Guide")
        st.markdown("""
        **Based on:** Lynne McTaggart's Power of 8 protocol × TI Sigma LCC attractor basin dynamics.
        
        The Emerick Constant C = 0.4370 determines the per-person coupling strength.
        When N=8 with coordination quality f≥0.30, group coherence Γ > 1 (unity threshold crossed).
        """)

        # Group members
        st.subheader("Group Members")
        num_members = st.number_input("Number of members in your group", 3, 12, 8)
        members = []
        for i in range(int(num_members)):
            col1, col2 = st.columns([2, 1])
            with col1:
                name = st.text_input(f"Member {i+1} name",
                                      key=f"member_{i}",
                                      placeholder=f"Member {i+1}")
            with col2:
                coord = st.slider(f"Coherence", 0.1, 1.0, 0.30, key=f"coord_{i}",
                                   help="Estimated individual coordination quality")
            members.append({"name": name or f"Member {i+1}", "f": coord})

        avg_f = sum(m["f"] for m in members) / len(members) if members else 0.30
        coh = compute_group_coherence(len(members), avg_f)

        col1, col2, col3 = st.columns(3)
        unity_icon = "✅" if coh["exceeds_unity"] else "⚠️"
        col1.metric(f"{unity_icon} Γ_group", f"{coh['Gamma_group']:.3f}")
        col2.metric("TJ budget", f"{coh['TJ_per_session']:.2f} TJ/session")
        col3.metric("Basin escape in", f"{coh['sessions_to_full_basin_escape']} sessions")

        st.markdown("---")

        # Session setup
        st.subheader("Session Configuration")
        col1, col2 = st.columns(2)
        with col1:
            session_num = st.number_input("Session number", 1, 21, 1)
            target_intention = st.text_area(
                "Intention / target",
                height=80,
                placeholder="e.g. 'Healing of [name]'s chronic back pain' or 'Brandon finding his ideal romantic partner' or 'Success of BlissGene Therapeutics Series A'"
            )
        with col2:
            st.markdown(f"""
            **Optimal breathing rhythm:**
            - Inhale: **{1/THETA_HZ:.1f}s** (= 1/θ_freq)
            - Exhale: **{1/THETA_HZ:.1f}s**
            - Full cycle: **{2/THETA_HZ:.1f}s** = {THETA_HZ/2:.3f} Hz
            
            **τ_adapt window:** {TAU_ADAPT:.0f}ms per half-cycle
            
            **C_EMERICK coupling:** {C_EMERICK:.4f} per person
            """)

        if target_intention and st.button("🎯 Generate Session Protocol", type="primary"):
            with st.spinner("Generating TI Sigma session guide..."):
                guide = ai_power_of_8_session_guide(
                    [m["name"] for m in members], target_intention, session_num
                )
            st.markdown(guide)

        # Breathing timer
        st.markdown("---")
        st.subheader("🫁 TI Sigma Breathing Timer")
        st.markdown(f"""
        The optimal Power of 8 breathing rhythm is synchronized to the consciousness 
        theta frequency **{THETA_HZ:.3f} Hz** (the Emerick Constant oscillation rate).
        
        Each breath cycle = **{2/THETA_HZ:.1f} seconds** total:
        - 📥 Inhale: **{1/THETA_HZ:.1f}s**  
        - 📤 Exhale: **{1/THETA_HZ:.1f}s**
        
        This synchronizes the group's HRV to θ-band frequency, maximizing group 
        coherence and approaching the Γ > 1 unity threshold.
        """)

    # ── TAB 5: Group Tracker ──────────────────────────────────────────────────
    with tabs[4]:
        st.header("📊 Manifestation Tracker")
        st.markdown("Track candidates, sessions, and intention outcomes over time.")

        # Summary metrics
        col1, col2, col3, col4 = st.columns(4)
        col1.metric("Tier 1 Candidates", "—")
        col2.metric("Outreach Sent", "—")
        col3.metric("Sessions Completed", "—")
        col4.metric("Total TJ Delivered", "—")

        st.info("This tracker will populate as you use the Discovery and Session tabs. "
                "Log entries are stored in your session.")

        # McTaggart reference
        st.markdown("---")
        st.subheader("📖 TI Sigma × McTaggart Integration")
        st.markdown(f"""
        | McTaggart Finding | TI Sigma Mechanism | Quantification |
        |---|---|---|
        | Optimal group size = 8 | N × C_EMERICK × f ≥ 1 (f=0.30) | N_min = ceil(1/(C×f)) = 8 |
        | Sessions 5-7 show strongest effects | Cumulative TJ approaches basin depth | 7 sessions × {compute_group_coherence(8)['TJ_per_session']:.1f} TJ = {7*compute_group_coherence(8)['TJ_per_session']:.1f} TJ ≈ 15 TJ |
        | Boomerang effect (intenders heal) | Coupling return α = 1/φ = {1/PHI:.3f} | κ_after ≈ {C_EMERICK + 7*C_EMERICK*0.30*(1/PHI):.3f} ≈ 1.0 |
        | "Oceanic" unity experience | Intender coupling approaches unity | Γ_eff = {compute_group_coherence(8)['Gamma_effective']:.3f} (φ-scaled) |
        | Non-local effects (distance) | LCC non-locality via Tralse topology | 15 TJ basin escape threshold |
        
        **C_EMERICK = {C_EMERICK:.6f}** — the per-person consciousness coupling threshold
        
        **Consciousness Unity Identity: C × φ × √2 = {C_EMERICK*PHI*math.sqrt(2):.6f} ≈ 1**
        """)


if __name__ == "__main__":
    show_power_of_8()
