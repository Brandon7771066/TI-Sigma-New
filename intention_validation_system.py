"""
TI Sigma — Intention Validation System  v2.0
=============================================
Three independent validation tracks, now powered by the Power of 8 AI Panel.

  A — DISTANT HEALING DATASET EXPLORER + LIVE GCP ANALYSIS
      Real-time data from the Global Consciousness Project (gcpdot.com).
      C_EMERICK threshold detection, TJ conversion, P8 session protocol.

  B — COUPLES COMPATIBILITY VALIDATOR (Blinded GILE Test)
      25 real public-figure couples, known outcomes.
      8-agent AI panel scores from name+bio only.
      Spearman ρ between predicted and actual relationship duration.

  C — INVESTOR COMPATIBILITY PREDICTOR
      10 real investors scored for BlissGene Therapeutics $1M fit.
      8-agent AI panel with GILE × TI Sigma dimensions.
      Personalized outreach drafted per investor.

All three tracks cite prior TI Sigma URBs and empirical datasets.
"""

import math, json, time, re
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from typing import Optional
import numpy as np
import requests
import streamlit as st
import anthropic
from scipy import stats

from multi_domain_partner_engine import (
    run_full_prediction, compute_brandon_scores, BRANDON, C_EMERICK as CEMD,
    CRYSTAL_CASE, PartnerProfile, InvestorCompatibility, RomanticCompatibility,
    PowerOf8GroupAnalysis, gil_composite, get_quadrant, analyze_power_of_8_group,
    get_ideal_romantic_partner_profile, get_ideal_investor_profile, get_ideal_collaborator_profile,
    GILE_WEIGHTS,
)

from power_of_8_ai_panel import (
    run_panel, PanelVerdict, gamma_color, format_gamma_bar, tralse_badge,
    PHI, C_EMERICK, N_AGENTS, GAMMA_MAX, UNITY_THRESHOLD, TRAL_THRESHOLD,
    AGENTS
)

# ── GCP live data ─────────────────────────────────────────────────────────────
GCP_GRAPH_URL = "https://gcpdot.com/gcpgraph.php"

def fetch_gcp_data(seconds_back: int = 3600) -> dict:
    """
    Fetch live GCP network deviation data.
    Returns parsed dict with time-series and key statistics.
    The `a` attribute in GCP XML is the cumulative chi-square probability.
    Values > 0.5 = network deviating above baseline (consciousness field active).
    """
    try:
        params = {"seconds": -seconds_back, "pixels": 900}
        r = requests.get(GCP_GRAPH_URL, params=params, timeout=12)
        if r.status_code != 200:
            return {"error": f"HTTP {r.status_code}", "live": False}

        text = r.text

        # Parse XML-like data points: <p i="N" a="0.63" t="0.53" q1=... q3=... b=... />
        points = re.findall(
            r'<p\s+i="(\d+)"\s+a="([^"]+)"\s+t="([^"]+)"', text
        )

        if not points:
            return {"error": "No data points parsed", "live": False, "raw_sample": text[:200]}

        indices = [int(p[0]) for p in points]
        a_values = [float(p[1]) for p in points]    # cumulative chisquare probability
        t_values = [float(p[2]) for p in points]    # theoretical baseline

        # Convert to deviation from 0.5 baseline
        deviations = [a - 0.5 for a in a_values]

        # Statistics
        a_arr = np.array(a_values)
        dev_arr = np.array(deviations)

        mean_a      = float(np.mean(a_arr))
        mean_dev    = float(np.mean(dev_arr))
        std_dev     = float(np.std(a_arr))
        peak_a      = float(np.max(a_arr))
        current_a   = a_values[-1] if a_values else 0.5
        n           = len(a_values)

        # Z-score vs baseline (null hypothesis: mean = 0.5)
        z_score = (mean_a - 0.5) / (std_dev / np.sqrt(n)) if std_dev > 0 and n > 1 else 0.0

        # Tralse-Joule estimate
        # TJ = |Z| × C_EMERICK  (Z-score magnitude × consciousness threshold)
        tj_estimate = abs(z_score) * C_EMERICK

        # C_EMERICK threshold check: is current deviation > C_EMERICK from midpoint?
        ce_threshold_crossed = current_a > (0.5 + C_EMERICK)
        ce_below_threshold   = current_a < (0.5 - C_EMERICK)

        # Trend: last 10% of window vs first 10%
        early = a_values[:max(1, n//10)]
        late  = a_values[max(0, n - n//10):]
        trend = "rising" if np.mean(late) > np.mean(early) + 0.005 else \
                "falling" if np.mean(late) < np.mean(early) - 0.005 else "stable"

        return {
            "live": True,
            "n_points": n,
            "window_seconds": seconds_back,
            "a_values": a_values,
            "indices": indices,
            "mean_a": mean_a,
            "mean_deviation": mean_dev,
            "std": std_dev,
            "peak_a": peak_a,
            "current_a": current_a,
            "z_score": z_score,
            "tj_estimate": tj_estimate,
            "c_emerick_threshold_crossed": ce_threshold_crossed,
            "c_emerick_below_threshold": ce_below_threshold,
            "trend": trend,
            "field_active": mean_a > 0.52,
            "field_status": (
                "🔴 BELOW BASELINE — field suppressed"
                if mean_a < 0.48 else
                "🟡 NEAR BASELINE — ambient / neutral"
                if 0.48 <= mean_a < 0.53 else
                "🟢 ELEVATED — consciousness field active"
                if 0.53 <= mean_a < 0.5 + C_EMERICK else
                "⚡ C_EMERICK THRESHOLD CROSSED — strong coherence signal"
            ),
            "fetch_time": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        }

    except Exception as e:
        return {"error": str(e), "live": False}


# ── Couples database (25 pairs, outcome hidden during scoring) ────────────────
COUPLES_DATABASE = [
    # LONG-TERM (>20 years)
    {"id": 1, "name1": "Jimmy Carter", "name2": "Rosalynn Carter",
     "bio1": "39th US President, humanitarian, Nobel Peace Prize, deeply religious Baptist, peanut farmer from Plains GA, wrote 30+ books, lived simply his whole life.",
     "bio2": "Mental health advocate, co-founder of Carter Center, childhood sweetheart, deeply religious, close family bonds, Georgia roots, married in 1946.",
     "actual_years": 77, "outcome": "lifelong (Rosalynn d.2023)", "category": "long"},

    {"id": 2, "name1": "Paul Newman", "name2": "Joanne Woodward",
     "bio1": "Hollywood actor, committed Democrat, Newman's Own charity founder, serious racing enthusiast, quiet private life in Connecticut, known for extreme loyalty.",
     "bio2": "Academy Award-winning actress, ballet lover, intellectual depth, committed to family life, long Broadway career, humanitarian.",
     "actual_years": 50, "outcome": "lifelong (Paul d.2008)", "category": "long"},

    {"id": 3, "name1": "Johnny Cash", "name2": "June Carter Cash",
     "bio1": "Country music legend, battled addiction decades, deep Christian faith, Man in Black, performed at prisons, raw emotional songwriting from personal pain.",
     "bio2": "Country music royalty (Carter Family), comedian and performer, deeply faithful Christian, wrote 'Ring of Fire' about her feelings for Johnny.",
     "actual_years": 35, "outcome": "lifelong (June d.2003)", "category": "long"},

    {"id": 4, "name1": "Dolly Parton", "name2": "Carl Thomas Dean",
     "bio1": "Country music icon, literacy philanthropist, Dollywood founder, sharp businesswoman, Tennessee mountain roots, never forgot origins despite global fame.",
     "bio2": "Asphalt paving company owner, extremely private, never appeared publicly with Dolly, shared Tennessee small-town roots, grounded and simple lifestyle.",
     "actual_years": 58, "outcome": "ongoing (married 1966)", "category": "long"},

    {"id": 5, "name1": "Barack Obama", "name2": "Michelle Obama",
     "bio1": "44th US President, Harvard Law, community organizer, author of 'Dreams from My Father', basketball devotee, values public service above personal enrichment.",
     "bio2": "Princeton/Harvard Law, hospital administrator, 'Becoming' author, Let's Move advocate, mother-first identity, Chicago South Side roots, deeply community-rooted.",
     "actual_years": 36, "outcome": "ongoing (together since 1989)", "category": "long"},

    {"id": 6, "name1": "David Bowie", "name2": "Iman",
     "bio1": "Rock legend, gender-fluid androgynous image, Ziggy Stardust, intellectual who read voraciously, quiet family man off stage, died Jan 2016.",
     "bio2": "Somali supermodel, businesswoman, cosmetics entrepreneur, refugee advocate, spiritual orientation, very private family life in NYC, mother of one daughter.",
     "actual_years": 25, "outcome": "lifelong (David d.2016)", "category": "long"},

    {"id": 7, "name1": "Tom Hanks", "name2": "Rita Wilson",
     "bio1": "Beloved everyman actor, Greek-American heritage, produced films and music, known for kindness on set, deeply family-oriented, cancer survivor.",
     "bio2": "Actress and producer, Greek roots central to identity, music career, breast cancer survivor and advocate, strong family-first values.",
     "actual_years": 36, "outcome": "ongoing (married 1988)", "category": "long"},

    {"id": 8, "name1": "Warren Buffett", "name2": "Astrid Menks",
     "bio1": "World's most famous value investor, Omaha Nebraska roots, frugal despite enormous wealth, reads 500 pages/day, Dairy Queen devotee, very routine-oriented.",
     "bio2": "Former cocktail waitress in Omaha, extremely private, Latvian immigrant roots, introduced by Buffett's first wife, quiet and grounded small-town life.",
     "actual_years": 46, "outcome": "ongoing (married 2006)", "category": "long"},

    # MEDIUM-TERM (3-20 years)
    {"id": 9, "name1": "Prince Charles", "name2": "Princess Diana",
     "bio1": "British heir to the throne, stoic and traditional upbringing, polo player, environmentalist, architecture critic, deeply formal and duty-bound in manner.",
     "bio2": "Shy kindergarten teacher from aristocratic family, bulimic in royal life, deeply empathetic with marginalized people, anti-landmine activist, adored by public.",
     "actual_years": 15, "outcome": "divorced 1996", "category": "medium"},

    {"id": 10, "name1": "Tom Cruise", "name2": "Nicole Kidman",
     "bio1": "Action superstar, devout Scientologist, intensely competitive, self-made from difficult childhood, relentless perfectionist energy.",
     "bio2": "Australian actress, Catholic background, intellectual serious roles, reportedly studied Scientology with Tom, reserved and thoughtful private person.",
     "actual_years": 11, "outcome": "divorced 2001", "category": "medium"},

    {"id": 11, "name1": "Brad Pitt", "name2": "Angelina Jolie",
     "bio1": "Hollywood superstar, architecture enthusiast, humanitarian, adopted children from multiple countries, went through very public custody battle.",
     "bio2": "UN Goodwill Ambassador, adopted multiple children, tattooed and edgy, drawn to humanitarian work in war zones, intense and dramatic personality.",
     "actual_years": 11, "outcome": "separated 2016/legal ongoing", "category": "medium"},

    {"id": 12, "name1": "Demi Moore", "name2": "Ashton Kutcher",
     "bio1": "90s actress, Kabbalah practitioner, focused intensely on fitness and longevity, known for drama-heavy relationships, sought younger energy.",
     "bio2": "Tech investor and entrepreneur, That 70s Show, co-founded Thorn anti-trafficking, smart and entrepreneurial, significantly younger than Demi.",
     "actual_years": 7, "outcome": "divorced 2013", "category": "medium"},

    {"id": 13, "name1": "Jennifer Aniston", "name2": "Brad Pitt",
     "bio1": "America's sweetheart from Friends, values loyalty and simplicity, Greek-American roots, reportedly wanted quiet family life, warm and relatable.",
     "bio2": "Hollywood superstar, restless and seeking new creative challenges, increasingly drawn to edgy roles, reportedly grew apart from earlier values.",
     "actual_years": 5, "outcome": "divorced 2005", "category": "medium"},

    {"id": 14, "name1": "Mariah Carey", "name2": "Nick Cannon",
     "bio1": "Global superstar diva, whistle register, extravagant lifestyle, emotionally intense, public breakdown history, devoted to her twins.",
     "bio2": "Comedian and TV host, rapper, father figure, founded media company, reportedly spiritual, outspoken, very different emotional temperament.",
     "actual_years": 8, "outcome": "divorced 2016", "category": "medium"},

    {"id": 15, "name1": "Richard Gere", "name2": "Carey Lowell",
     "bio1": "Committed Tibetan Buddhist, Dalai Lama friend, actor of sophisticated roles, deeply values spiritual practice and Tibetan justice.",
     "bio2": "Model and actress, mother-focused, less public profile, reportedly shared some but not all of his spiritual intensity.",
     "actual_years": 14, "outcome": "divorced 2016", "category": "medium"},

    {"id": 16, "name1": "Jeff Bezos", "name2": "MacKenzie Scott",
     "bio1": "Amazon founder, relentless long-term thinker, intense work culture, Princeton physics, increasingly Blue Origin focused, known for loud laugh.",
     "bio2": "Princeton classmate, novelist ('The Testing of Luther Albright'), now world's most prolific philanthropist, deeply principled giver, humble public presence.",
     "actual_years": 25, "outcome": "divorced 2019", "category": "long"},

    # SHORT-TERM (<3 years)
    {"id": 17, "name1": "Kim Kardashian", "name2": "Kris Humphries",
     "bio1": "Reality TV mogul, SKIMS founder, law student, extremely brand-conscious, tight Armenian-American family, highly strategic public persona.",
     "bio2": "NBA power forward, straightforward and traditional Midwestern values from Minnesota, less interested in fame and media attention.",
     "actual_years": 0.2, "outcome": "annulled after 72 days", "category": "short"},

    {"id": 18, "name1": "Nicolas Cage", "name2": "Lisa Marie Presley",
     "bio1": "Intense method actor, Elvis memorabilia collector, spent fortunes on eccentric purchases, volatile creative, multiple marriages.",
     "bio2": "Elvis's only daughter, rock musician, tumultuous childhood, battled addiction, emotionally guarded but intensely passionate.",
     "actual_years": 0.3, "outcome": "divorced after 4 months", "category": "short"},

    {"id": 19, "name1": "Miley Cyrus", "name2": "Liam Hemsworth",
     "bio1": "Pop provocateur, Hannah Montana origins, constantly reinventing image, fiercely independent, cannabis advocate, very publicly outspoken.",
     "bio2": "Australian actor, Hunger Games fame, quieter and more traditional, loves surfing and outdoor life, family-oriented Hemsworth clan.",
     "actual_years": 0.8, "outcome": "divorced ~8 months post-wedding", "category": "short"},

    {"id": 20, "name1": "Jennifer Lopez", "name2": "Ojani Noa",
     "bio1": "Jenny from the Block, worked relentlessly from the Bronx to superstardom, deeply family-oriented, perpetual romantic, built business empire.",
     "bio2": "Cuban model and actor, restaurant manager, reportedly charming, less established career, different life trajectory.",
     "actual_years": 0.9, "outcome": "divorced after 11 months", "category": "short"},

    {"id": 21, "name1": "Britney Spears", "name2": "Jason Alexander",
     "bio1": "Pop princess who grew up in public, deeply influenced by family dynamics, sought freedom and normalcy, from Kentwood Louisiana, extremely impulsive.",
     "bio2": "Childhood friend from Louisiana, not a celebrity, reconnected briefly as adults, spontaneous with no long-term planning.",
     "actual_years": 0.006, "outcome": "annulled after 55 hours", "category": "short"},

    {"id": 22, "name1": "Pamela Anderson", "name2": "Rick Salomon",
     "bio1": "Canadian-American actress and model, PETA animal rights activist, deeply unconventional, followed heart impulsively, passionate and intense.",
     "bio2": "Poker player and filmmaker, gambling lifestyle, reportedly different values and priorities, brief intense connections.",
     "actual_years": 0.2, "outcome": "annulled after 2 months", "category": "short"},

    {"id": 23, "name1": "Bill Gates", "name2": "Melinda French Gates",
     "bio1": "Microsoft co-founder, world's largest philanthropist (pre-split), analytical systems thinker, believes technology solves global problems.",
     "bio2": "Computer scientist turned philanthropy leader, co-CEO Gates Foundation, women's empowerment advocate, poised and strategic communicator.",
     "actual_years": 27, "outcome": "divorced 2021", "category": "long"},

    {"id": 24, "name1": "Elon Musk", "name2": "Talulah Riley",
     "bio1": "Tesla/SpaceX CEO, extreme work hours, professed desire for large family, mercurial personality, alternates between visionary and erratic publicly.",
     "bio2": "British actress, wrote a novel, reportedly sweet and grounded, moved to California for Elon, described their dynamic as 'very intense' publicly.",
     "actual_years": 4, "outcome": "divorced twice (married twice)", "category": "medium"},

    {"id": 25, "name1": "Leonard Cohen", "name2": "Suzanne Elrod",
     "bio1": "Poet and musician, Zen Buddhist monk, wrote about love/God/heartbreak from personal experience, Montreal Jewish roots, deeply spiritual.",
     "bio2": "Mother of Cohen's two children, reportedly difficult relationship dynamic, left after years of raising children largely alone.",
     "actual_years": 9, "outcome": "separated (never legally married)", "category": "medium"},
]

# ── Investor database ─────────────────────────────────────────────────────────
INVESTOR_DATABASE = [
    {"name": "Tim Ferriss", "firm": "Angel syndicate",
     "check_size": "$25K–$250K", "stage": "Seed",
     "thesis": "World-class at measuring/testing/optimizing human performance. Very open to unconventional interventions. Donated $2M+ to Johns Hopkins psychedelic research. Four-hour body approach to everything.",
     "consciousness_openness": "Very High",
     "focus": "Health optimization, psychedelics, consciousness, self-improvement",
     "public_stance": "Openly supports psychedelic therapy, meditation, consciousness expansion. Podcast episodes on Wim Hof, Paul Stamets, Andrew Huberman.",
     "brandon_fit": ["GILE wellness", "mood amplifiers", "biometric optimization", "Power of 8", "consciousness research"]},

    {"name": "Esther Dyson", "firm": "EDventure Holdings",
     "check_size": "$100K–$1M", "stage": "Seed–Series A",
     "thesis": "Prevention over treatment. Human flourishing. Mind-body connection and behavioral change. Very patient angel investor.",
     "consciousness_openness": "High",
     "focus": "Health, wellness, preventive medicine, consciousness, Eastern philosophy integration",
     "public_stance": "Has invested in meditation apps and mind-body companies. Personal wellness practice. Wrote about consciousness and health for decades.",
     "brandon_fit": ["GILE framework", "mood amplifiers", "biometric wellness", "Power of 8"]},

    {"name": "Naval Ravikant", "firm": "AngelList / retired angel",
     "check_size": "$100K–$500K", "stage": "Seed",
     "thesis": "Compound interest in specific knowledge, leverage, and presence. Daily meditator. Vedanta practitioner. Deeply interested in consciousness.",
     "consciousness_openness": "Very High",
     "focus": "Philosophy of wealth, consciousness, meditation, Indian philosophy, longevity",
     "public_stance": "Regular podcast episodes on consciousness, Vedanta, non-duality. Has said 'the self is an illusion' publicly. Meditates for hours daily.",
     "brandon_fit": ["TI Sigma philosophy", "GILE framework", "consciousness research", "wellness tech"]},

    {"name": "Marc Benioff", "firm": "TIME Ventures / personal angel",
     "check_size": "$1M–$5M", "stage": "Series A",
     "thesis": "Business as platform for social change. Buddhist-influenced. Values compassion as corporate strategy.",
     "consciousness_openness": "High",
     "focus": "Conscious capitalism, mental health, AI for good, human flourishing",
     "public_stance": "Buddhist practitioner, meditates regularly, co-chairs Mental Health initiatives. Named Salesforce around principles of ohana (family). Funds Burning Man culture.",
     "brandon_fit": ["GILE consciousness framework", "BlissGene wellness mission", "AI for human flourishing"]},

    {"name": "Lisa Gansky", "firm": "Mesh Ventures / angel",
     "check_size": "$100K–$1M", "stage": "Seed–Series A",
     "thesis": "Conscious capitalism — regenerative business models for humans and planet. Psychedelics as medicine.",
     "consciousness_openness": "High",
     "focus": "Health, wellbeing, human potential, regenerative systems, psychedelic wellness",
     "public_stance": "Co-founder of Journey Colab (psychedelic company). Explicitly funds consciousness expansion and human potential.",
     "brandon_fit": ["BlissGene Therapeutics", "mood amplifiers", "wellness protocols"]},

    {"name": "Peter Thiel", "firm": "Founders Fund / Thiel Capital",
     "check_size": "$1M–$5M", "stage": "Series A–B",
     "thesis": "Zero to One — secrets, monopoly-building, definite visions. Anti-indefinite optimism. Christian background, values transcendence.",
     "consciousness_openness": "Medium-High",
     "focus": "Longevity, contrarian deep tech, biotech, anti-aging, Christian metaphysics",
     "public_stance": "Funds metformin longevity research, Alcor cryonics, radical life extension. Interested in alternative medicine. Openly Christian.",
     "brandon_fit": ["TI Sigma consciousness framework", "longevity", "contrarian research", "BlissGene"]},

    {"name": "Vinod Khosla", "firm": "Khosla Ventures",
     "check_size": "$1M–$10M", "stage": "Series A–C",
     "thesis": "Radical transformation of industries via breakthrough technology. Will fund 'crazy ideas'. Doesn't need revenue. Values missionary technical founders.",
     "consciousness_openness": "Medium",
     "focus": "Deep tech, energy, healthcare, AI, neurotechnology",
     "public_stance": "Challenges conventional wisdom constantly. Has funded brain-computer interfaces and neuroscience startups.",
     "brandon_fit": ["AI-driven wellness", "biotech", "consciousness tech"]},

    {"name": "Y Combinator", "firm": "Y Combinator",
     "check_size": "$500K standard", "stage": "Seed",
     "thesis": "Make something people want. Great founders over great ideas. Has funded mental health, wellness, biotech.",
     "consciousness_openness": "Medium",
     "focus": "Any category with great founders and large market",
     "public_stance": "Neutral on consciousness framework; funds what has user traction and retention data.",
     "brandon_fit": ["BlissGene product-market fit", "AI wellness platform", "GSA trading tech"]},

    {"name": "Balaji Srinivasan", "firm": "Angel / 1729",
     "check_size": "$50K–$500K", "stage": "Seed",
     "thesis": "Network state, sovereignty, health optimization, decentralized everything. Deeply interested in quantified self and longevity.",
     "consciousness_openness": "Medium-High",
     "focus": "Longevity, biohacking, network states, crypto, decentralized science (DeSci)",
     "public_stance": "Regularly posts about tracking biomarkers, longevity interventions, and consciousness-adjacent topics like meditation and flow states.",
     "brandon_fit": ["biometric wellness platform", "quantified consciousness", "GSA trading", "TI Sigma empirical framework"]},

    {"name": "Laura Deming", "firm": "Longevity Fund",
     "check_size": "$250K–$2M", "stage": "Seed–Series A",
     "thesis": "Every company that meaningfully extends healthy human lifespan. Deeply scientific. Very patient. Values rigor above all.",
     "consciousness_openness": "Low-Medium",
     "focus": "Longevity, lifespan extension, aging biology, cellular reprogramming",
     "public_stance": "Pure biology focus. Would need hard biological mechanism data for BlissGene's wellness claims.",
     "brandon_fit": ["BlissGene wellness", "therapeutic protocols", "biometric health tracking"]},
]


# ── Streamlit UI ──────────────────────────────────────────────────────────────
def show_intention_validation():
    st.title("🔬 TI Sigma Intention Validation Lab  v2.0")
    st.caption(
        "Powered by the Power of 8 AI Panel — 8 specialized Claude agents analyze each subject "
        "in parallel, synthesized by the group coherence formula Γ = N × C × f. "
        f"Unity threshold Γ > {UNITY_THRESHOLD} | C_EMERICK = {C_EMERICK:.4f}"
    )

    tabs = st.tabs([
        "🌐 Live GCP Analysis",
        "💑 Couples Validator",
        "💰 Investor Predictor",
        "📚 Dataset Registry",
        "🧬 Multi-Domain Partner Predictions",
    ])

    # ── TAB A: LIVE GCP DATA ─────────────────────────────────────────────────
    with tabs[0]:
        st.header("🌐 Live Global Consciousness Project Analysis")
        st.markdown(f"""
        Direct feed from **gcpdot.com** — the GCP's live network of Random Event Generators.
        When a Power of 8 session raises group coherence Γ > 1, the TI Sigma model predicts
        a detectable deviation in the GCP network above the **C_EMERICK threshold**:
        `a_value > 0.5 + C_EMERICK = {0.5 + C_EMERICK:.4f}`

        Prior TI Sigma work (GRAND PSI PROOF, Jan 2026): PSI = LCC accessing the probability
        resonance field. GCP deviations are the macro-statistical signature of that field.
        DMILS data (Radin/Schlitz): HRV coupling r≈0.25 at individual scale → GCP Z>2 at
        global scale during high-coherence events.
        """)

        col1, col2 = st.columns([1, 2])
        with col1:
            window_hours = st.selectbox("Data window", [1, 3, 6, 12, 24], index=0,
                                         format_func=lambda h: f"Last {h} hour{'s' if h>1 else ''}")
            auto_refresh = st.checkbox("Auto-refresh every 60s", False)

        with col2:
            if st.button("📡 Fetch Live GCP Data", type="primary") or auto_refresh:
                with st.spinner("Fetching live GCP network data..."):
                    gcp = fetch_gcp_data(window_hours * 3600)
                    st.session_state["gcp_data"] = gcp

        gcp = st.session_state.get("gcp_data")

        if gcp and gcp.get("live"):
            st.success(f"✅ Live data: {gcp['n_points']} samples over {window_hours}h | "
                       f"Fetched {gcp['fetch_time']}")

            # Key metrics
            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Network mean `a`", f"{gcp['mean_a']:.4f}",
                       delta=f"{gcp['mean_deviation']:+.4f} vs baseline",
                       delta_color="normal")
            c2.metric("Z-score", f"{gcp['z_score']:+.3f}",
                       delta="Significant if |Z|>1.96")
            c3.metric("Tralse-Joule", f"{gcp['tj_estimate']:.4f} TJ",
                       delta=f"C_EMERICK = {C_EMERICK:.4f}")
            c4.metric("Current `a`", f"{gcp['current_a']:.4f}",
                       delta=f"Trend: {gcp['trend']}")

            # Field status
            status_color = "success" if gcp["field_active"] else "info"
            getattr(st, status_color)(f"**Field Status:** {gcp['field_status']}")

            if gcp["c_emerick_threshold_crossed"]:
                st.warning(
                    f"⚡ **C_EMERICK THRESHOLD CROSSED** — current network deviation "
                    f"({gcp['current_a']:.4f}) exceeds the consciousness unity threshold "
                    f"(0.5 + C = {0.5 + C_EMERICK:.4f}). This is the signature TI Sigma "
                    f"predicts during a successful Power of 8 session."
                )

            # Plot
            import streamlit as _st
            a_vals = gcp["a_values"]
            if len(a_vals) > 5:
                import pandas as pd
                df = pd.DataFrame({
                    "Sample": list(range(len(a_vals))),
                    "GCP Network Deviation (a)": a_vals,
                    "Baseline (0.5)": [0.5] * len(a_vals),
                    "C_EMERICK Upper Threshold": [0.5 + C_EMERICK] * len(a_vals),
                    "C_EMERICK Lower Threshold": [0.5 - C_EMERICK] * len(a_vals),
                })
                st.line_chart(df.set_index("Sample"))

            # TJ analysis
            st.markdown("---")
            st.subheader("🧮 TI Sigma Analysis")
            st.markdown(f"""
            **Tralse-Joule estimate for this window:**
            - |Z| = {abs(gcp['z_score']):.3f}
            - TJ = |Z| × C_EMERICK = {abs(gcp['z_score']):.3f} × {C_EMERICK:.4f} = **{gcp['tj_estimate']:.4f} TJ**
            - Recall: 15 TJ required to escape chronic attractor basin (URB #413)
            - This window contributes **{100*gcp['tj_estimate']/15:.2f}%** of the basin escape budget

            **What to do with a live P8 session:**
            1. Note your session start time (UTC)
            2. Run your 10-minute Power of 8 session
            3. Re-fetch GCP data for the session window (+ 30 min integration)
            4. Check if mean_a rises above **{0.5 + C_EMERICK:.4f}** during session
            5. Record TJ contribution for cumulative tracking toward 15 TJ threshold
            """)

        elif gcp and not gcp.get("live"):
            st.error(f"GCP fetch failed: {gcp.get('error', 'Unknown error')}")
        else:
            st.info("Click 'Fetch Live GCP Data' to pull the current global consciousness network reading.")

        # Dataset registry (collapsed)
        with st.expander("📚 Full Open-Source Dataset Registry (8 datasets)"):
            _show_dataset_registry()

    # ── TAB B: COUPLES VALIDATOR ─────────────────────────────────────────────
    with tabs[1]:
        st.header("💑 Blinded Couples GILE Validation Study")
        st.markdown(f"""
        **Scientific method:** 25 real public-figure couples with known outcomes.
        The **Power of 8 AI Panel** scores each pair from minimal public bio only
        (no duration data is seen). We compare predicted vs actual longevity.

        **8 agents × parallel Claude calls → Γ_group synthesis:**
        - Agents: G (Goodness), I (Intuition), L (Love), E (Environment),
          C (Consciousness/LCC), T (Tralse Logic), M (Mathematical), S (Synthesizer)
        - Each agent scores 0-100 and gives certainty f_i
        - Γ_group = mean(f_i) × {N_AGENTS} × {C_EMERICK:.4f}
        - If Γ > 1: high-confidence longevity prediction issued

        **Validation metric:** Spearman rank correlation ρ(predicted_years, actual_years).
        Target: ρ > 0.50. Prior GILE theory predicts ρ ≥ 0.60 (Bengston analogy:
        healer–target resonance predicts healing rate; here GILE resonance predicts duration).
        """)

        categories = {"All 25": None, "Long-term only (>20yr)": "long",
                      "Short-term only (<3yr)": "short", "Medium only (3-20yr)": "medium"}

        col1, col2, col3 = st.columns(3)
        with col1:
            cat_choice = st.selectbox("Filter category", list(categories.keys()))
        with col2:
            n_couples = st.slider("Couples to score", 3, 25,
                                   min(8, len(COUPLES_DATABASE)))
        with col3:
            reveal_truth = st.checkbox("Reveal actual outcomes after scoring", True)

        cat_filter = categories[cat_choice]
        pool = [c for c in COUPLES_DATABASE if cat_filter is None or c["category"] == cat_filter]
        pool = pool[:n_couples]

        st.info(f"Pool: {len(pool)} couples | "
                f"Long: {sum(1 for c in pool if c['category']=='long')} | "
                f"Medium: {sum(1 for c in pool if c['category']=='medium')} | "
                f"Short: {sum(1 for c in pool if c['category']=='short')}")

        with st.expander("Preview blinded dataset (names + bios, NO durations)"):
            for c in pool[:4]:
                st.markdown(f"**{c['name1']} + {c['name2']}**")
                st.caption(f"{c['name1']}: {c['bio1'][:120]}...")
                st.caption(f"{c['name2']}: {c['bio2'][:120]}...")
                st.markdown("---")
            if len(pool) > 4:
                st.caption(f"... and {len(pool)-4} more")

        if st.button("🔬 Run Power of 8 AI Panel — Couples Study", type="primary"):
            client = anthropic.Anthropic()
            results = []
            progress = st.progress(0)
            status = st.empty()

            for i, couple in enumerate(pool):
                status.markdown(
                    f"**Running P8 Panel on Couple {i+1}/{len(pool)}:** "
                    f"{couple['name1']} + {couple['name2']}  "
                    f"(8 agents in parallel...)"
                )

                subject_ctx = (
                    f"COUPLE ASSESSMENT\n\n"
                    f"Person 1: {couple['name1']}\n"
                    f"Bio: {couple['bio1']}\n\n"
                    f"Person 2: {couple['name2']}\n"
                    f"Bio: {couple['bio2']}\n\n"
                    f"TASK: Assess romantic compatibility and predict relationship longevity in years."
                )

                verdict = run_panel(
                    subject_ctx,
                    f"{couple['name1']} + {couple['name2']}",
                    client,
                    mode="couples"
                )
                results.append({"couple": couple, "verdict": verdict})
                progress.progress((i + 1) / len(pool))

            progress.empty()
            status.empty()

            # Compute Spearman correlation
            actual   = [r["couple"]["actual_years"] for r in results]
            predicted = [r["verdict"].longevity_prediction or r["verdict"].consensus_score / 2
                         for r in results]
            predicted_scores = [r["verdict"].consensus_score for r in results]

            if len(actual) >= 4:
                rho_yrs,  p_yrs  = stats.spearmanr(actual, predicted)
                rho_scr,  p_scr  = stats.spearmanr(actual, predicted_scores)
            else:
                rho_yrs, p_yrs, rho_scr, p_scr = 0, 1, 0, 1

            mean_gamma = sum(r["verdict"].gamma_group for r in results) / len(results)

            # Dashboard
            st.markdown("---")
            st.markdown("## 📊 Validation Results")
            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Spearman ρ (years)", f"{rho_yrs:.3f}",
                       delta="Target >0.50")
            c2.metric("Spearman ρ (score)", f"{rho_scr:.3f}")
            c3.metric("p-value", f"{p_yrs:.4f}",
                       delta="Sig if <0.05")
            c4.metric("Mean Γ_group", f"{mean_gamma:.3f}",
                       delta=f"Unity = {UNITY_THRESHOLD}")

            if rho_yrs > 0.6 and p_yrs < 0.05:
                st.success(
                    f"✅ STRONG VALIDATION (ρ={rho_yrs:.3f}, p={p_yrs:.4f}) — "
                    f"Power of 8 AI Panel significantly predicts relationship longevity from bio data alone. "
                    f"GILE framework validated."
                )
            elif rho_yrs > 0.35:
                st.warning(f"⚠️ MODERATE SIGNAL (ρ={rho_yrs:.3f}, p={p_yrs:.4f})")
            else:
                st.error(f"❌ WEAK SIGNAL (ρ={rho_yrs:.3f}, p={p_yrs:.4f}) — "
                         f"More couples or refined GILE weights needed.")

            # Individual results
            st.markdown("### Couple-by-Couple Results (sorted by consensus score)")
            for r in sorted(results, key=lambda x: -x["verdict"].consensus_score):
                v   = r["verdict"]
                c   = r["couple"]
                g   = gamma_color(v.gamma_group)
                pred_y = v.longevity_prediction or 0
                err    = abs(pred_y - c["actual_years"])

                label = (f"{g} **{c['name1']} + {c['name2']}**  |  "
                         f"Γ={v.gamma_group:.3f} | GILE={v.consensus_score:.0f}/100 | "
                         f"Predicted {pred_y:.1f}yr")
                if reveal_truth:
                    accuracy = "🟢" if err < 5 else "🟡" if err < 20 else "🔴"
                    label += f" {accuracy} Actual: {c['actual_years']:.1f}yr ({c['outcome']})"

                with st.expander(label):
                    st.markdown(f"`{format_gamma_bar(v.gamma_group)}`")
                    st.markdown(f"**Confidence:** {v.confidence_tier} | "
                                f"**Tralse synthesis:** {v.tralse_synthesis}")
                    st.markdown(f"**Key tensions:** {v.key_tensions}")
                    st.markdown(f"**Panel Verdict:** {v.final_verdict}")

                    # 8 agent reports
                    st.markdown("**Individual Agent Reports:**")
                    agent_cols = st.columns(4)
                    for j, rep in enumerate(v.agent_reports):
                        with agent_cols[j % 4]:
                            st.markdown(
                                f"**{rep.agent_code}** — {tralse_badge(rep.tralse_state)}\n"
                                f"Score: {rep.score:.0f} | f={rep.certainty:.2f}\n"
                                f"*{rep.key_insight[:80]}...*"
                            )

            st.session_state["couples_results"] = results
            st.session_state["couples_rho"] = (rho_yrs, p_yrs)

    # ── TAB C: INVESTOR PREDICTOR ────────────────────────────────────────────
    with tabs[2]:
        st.header("💰 Investor Compatibility Predictor")
        st.markdown(f"""
        The Power of 8 AI Panel scores each investor for **BlissGene Therapeutics** fit.
        8 agents analyze from their specialized lens (Goodness/ethics alignment,
        Intuition/pattern, Love/passion resonance, Environment/stage fit,
        Consciousness openness, Tralse logical consistency, Mathematical pattern, Synthesis).

        **Validation design:** These scores are prospective predictions.
        Track response rate per Γ-tier over next 90 days.
        **TI Sigma prediction:** Tier 1 (Γ>1) response rate ≥ C_EMERICK × 100 = {100*C_EMERICK:.0f}%.
        """)

        startup_profile = st.text_area(
            "BlissGene Therapeutics profile (edit to refine)",
            value=(
                "COMPANY: BlissGene Therapeutics  |  STAGE: Seed ($750K raised) → Series A\n"
                "SEEKING: $1M check from a values-aligned investor\n"
                "FOUNDER: Brandon Emerick — CEO, mathematician, consciousness researcher.\n"
                "  Creator of TI Sigma framework: Emerick Constant C=1/(φ√2)≈0.437 as neural "
                "threshold for consciousness emergence. 68 published research papers (URBs).\n"
                "  Background: quantitative trading (Grand Stock Algorithm, live Alpaca account);\n"
                "  GILE Framework (Goodness–Intuition–Love–Environment mapped to PRIMARY CONSTANTS).\n"
                "PRODUCT: AI wellness platform combining:\n"
                "  • Mood Amplifier safety/efficacy analysis (patentable scoring engine)\n"
                "  • Biometric-driven consciousness protocols (HRV, EEG, fNIRS)\n"
                "  • Power of 8 group intention system (McTaggart research + TI math)\n"
                "  • Quantum biology analysis for therapeutic interventions\n"
                "  • GSA v2 stock trading algorithm (live paper account signals)\n"
                "MARKET: $4.5T global wellness + $1.2T mental health market\n"
                "TRACTION: Platform live; active users; 68 research papers; Kaggle entries;\n"
                "  daily trading signals; BlissGene.com domain; Streamlit app deployed\n"
                "IP: Emerick Constant; TI Sigma framework; GILE scoring engine\n"
                "VISION: License AI consciousness engine via API; healing-intention platform;\n"
                "  integrate with insurance for preventive wellness ROI measurement"
            ),
            height=220
        )

        col1, col2 = st.columns(2)
        with col1:
            min_c_openness = st.selectbox(
                "Min consciousness openness",
                ["Any", "Medium", "Medium-High", "High", "Very High"],
                index=0
            )
        with col2:
            top_n_inv = st.slider("Score top N investors", 3, len(INVESTOR_DATABASE),
                                   len(INVESTOR_DATABASE))

        c_openness_rank = {"Any": 0, "Medium": 2, "Medium-High": 3, "High": 4, "Very High": 5}
        c_rank_map = {"Low": 1, "Low-Medium": 2, "Medium": 2, "Medium-High": 3, "High": 4, "Very High": 5}
        min_rank = c_openness_rank[min_c_openness]
        pool_inv = [
            inv for inv in INVESTOR_DATABASE
            if c_rank_map.get(inv["consciousness_openness"], 0) >= min_rank
        ][:top_n_inv]

        st.info(f"Scoring {len(pool_inv)} investors through the Power of 8 AI Panel")

        if st.button("🎯 Run Power of 8 AI Panel — Investor Scoring", type="primary"):
            client = anthropic.Anthropic()
            inv_results = []
            progress = st.progress(0)
            status = st.empty()

            for i, investor in enumerate(pool_inv):
                status.markdown(
                    f"**Running P8 Panel on {investor['name']}** ({investor['firm']})  "
                    f"(8 agents in parallel...)"
                )

                ctx = (
                    f"INVESTOR-STARTUP COMPATIBILITY ASSESSMENT\n\n"
                    f"INVESTOR: {investor['name']} | {investor['firm']}\n"
                    f"Investment thesis: {investor['thesis']}\n"
                    f"Focus areas: {investor['focus']}\n"
                    f"Check size: {investor['check_size']} | Stage: {investor['stage']}\n"
                    f"Consciousness openness: {investor['consciousness_openness']}\n"
                    f"Public stance: {investor['public_stance']}\n"
                    f"Areas of fit with startup: {', '.join(investor['brandon_fit'])}\n\n"
                    f"STARTUP:\n{startup_profile}\n\n"
                    f"TASK: Assess investor-startup compatibility for a $1M investment. "
                    f"Probability that this investor writes a $1M+ check."
                )

                verdict = run_panel(ctx, investor["name"], client, mode="investor")
                inv_results.append({"investor": investor, "verdict": verdict})
                progress.progress((i + 1) / len(pool_inv))

            progress.empty()
            status.empty()

            # Sort by consensus score
            inv_results.sort(key=lambda x: -x["verdict"].consensus_score)
            st.session_state["inv_results"] = inv_results

            st.markdown("---")
            st.markdown("## 🏆 Investor Rankings — Power of 8 AI Panel")

            # Summary table
            table_rows = []
            for r in inv_results:
                v = r["verdict"]
                inv = r["investor"]
                table_rows.append({
                    "Investor": inv["name"],
                    "Firm": inv["firm"],
                    "Γ_group": f"{v.gamma_group:.3f}",
                    "GILE Score": f"{v.consensus_score:.0f}/100",
                    "Inv. Prob.": f"{v.investment_probability or 0:.0f}%",
                    "Tier": v.confidence_tier,
                    "C-Openness": inv["consciousness_openness"],
                })
            import pandas as pd
            st.dataframe(pd.DataFrame(table_rows), use_container_width=True)

            # Detailed cards
            for rank, r in enumerate(inv_results):
                v   = r["verdict"]
                inv = r["investor"]
                g   = gamma_color(v.gamma_group)

                with st.expander(
                    f"**#{rank+1}** {g} **{inv['name']}** ({inv['firm']}) | "
                    f"Γ={v.gamma_group:.3f} | Score={v.consensus_score:.0f} | "
                    f"Prob={v.investment_probability or 0:.0f}%"
                ):
                    st.markdown(f"`{format_gamma_bar(v.gamma_group)}`")
                    st.markdown(f"**Confidence tier:** {v.confidence_tier}")
                    st.markdown(f"**Tralse synthesis:** {v.tralse_synthesis}")
                    st.markdown(f"**Key tensions:** {v.key_tensions}")
                    st.markdown(f"**Panel Verdict:** {v.final_verdict}")

                    # Agent reports
                    st.markdown("**8 Agent Reports:**")
                    agent_cols = st.columns(4)
                    for j, rep in enumerate(v.agent_reports):
                        with agent_cols[j % 4]:
                            st.markdown(
                                f"**{rep.agent_code}** {tralse_badge(rep.tralse_state)}\n"
                                f"Score: {rep.score:.0f} | f={rep.certainty:.2f}\n"
                                f"*{rep.key_insight[:70]}...*"
                            )

                    # Outreach
                    if st.button(f"✉️ Draft outreach for {inv['name']}", key=f"draft_{rank}"):
                        with st.spinner("Synthesizing personalized outreach..."):
                            draft = client.messages.create(
                                model="claude-opus-4-5",
                                max_tokens=600,
                                messages=[{"role": "user", "content":
                                    f"Draft a concise LinkedIn message from Brandon Emerick "
                                    f"(CEO, BlissGene Therapeutics) to {inv['name']}. "
                                    f"Reference their public work specifically: {inv['public_stance'][:150]}. "
                                    f"Best angle from P8 Panel: {v.final_verdict[:150]}. "
                                    f"Under 150 words. End with ask for 20-min call. "
                                    f"Warm but professional. Never mention 'GILE' or 'TI Sigma' directly — "
                                    f"speak their language."}]
                            ).content[0].text
                        st.text_area("Draft:", value=draft, height=180, key=f"msg_{rank}")

        elif "inv_results" in st.session_state:
            st.info("Previous results cached. Re-run to refresh.")
            for r in st.session_state["inv_results"][:3]:
                v = r["verdict"]
                inv = r["investor"]
                st.markdown(
                    f"{gamma_color(v.gamma_group)} **{inv['name']}** — "
                    f"Γ={v.gamma_group:.3f} | Score={v.consensus_score:.0f} | "
                    f"Prob={v.investment_probability or 0:.0f}%"
                )

    # ── TAB D: DATASET REGISTRY (reference) ─────────────────────────────────
    with tabs[3]:
        st.header("📚 Open-Source Intention Dataset Registry")
        _show_dataset_registry()

    # ── TAB E: MULTI-DOMAIN PARTNER PREDICTIONS ───────────────────────────────
    with tabs[4]:
        _show_multi_domain_predictions()


def _show_multi_domain_predictions():
    """
    Multi-Domain Partner Predictions — URB #480–483 Implementation.
    Applies the Measurement Trilogy to all domains of partnership:
    Romantic | Investor (BlissGene) | Collaborator | Power of 8
    """
    st.header("🧬 Multi-Domain Partner Predictions")
    st.caption(
        "Powered by the Measurement Trilogy (URBs #480–483). "
        "Emerick Constant C = {:.4f} — universal compatibility floor. "
        "Correct GILE weighting: G=35%, I=27%, L=23%, E=15%.".format(CEMD)
    )

    brandon = compute_brandon_scores()

    st.info(
        f"**Brandon's Calibrated Profile** — GIL Composite: **{brandon['GIL']:.3f}** "
        f"({'✅ Above' if brandon['transcendent'] else '⚠️ Below'} Emerick Constant {CEMD:.4f}) "
        f"| Quadrant: **{brandon['quadrant']}** — {brandon['quadrant_label']}",
        icon="🧬"
    )

    col_g, col_i, col_l, col_e = st.columns(4)
    col_g.metric("G (Goodness, 35%)", f"{brandon['G']:.2f}", help="URB corpus + meditation + pattern-obsession")
    col_i.metric("I (Intuition, 27%)", f"{brandon['I']:.2f}", help="Synchronicity ×12/week + ADHD + bipolar range")
    col_l.metric("L (Love, 23%)", f"{brandon['L']:.2f}", help="Suffering-activation 9/10 + meditation")
    col_e.metric("E (Environment, 15%)", f"{brandon['E']:.2f}", help="Physical/financial/social — the 15% physicalism measures")

    st.divider()

    domain_tab1, domain_tab2, domain_tab3, domain_tab4, domain_tab5 = st.tabs([
        "💑 Romantic",
        "💰 Investor (BlissGene)",
        "🔬 Collaborator",
        "🕯️ Power of 8",
        "🔍 Crystal Case Analysis",
    ])

    # ── ROMANTIC ─────────────────────────────────────────────────────────────
    with domain_tab1:
        st.subheader("Romantic Partner Prediction — L*/+E Corrected")
        st.markdown(
            "The fundamental upgrade: compatibility requires **GIL composite ≥ C_EMERICK**. "
            "Any partner below this threshold — regardless of E-dimension alignment "
            "or outer spiritual presentation — is fundamentally incompatible."
        )
        ideal = get_ideal_romantic_partner_profile(brandon)

        st.markdown("### Required Profile")
        req = ideal['required']
        for k, v in req.items():
            st.markdown(f"- **{k.replace('_', ' ').title()}:** {v}")

        st.markdown("### Optimal GILE Scores")
        o = ideal['optimal_GILE']
        oc1, oc2, oc3, oc4 = st.columns(4)
        oc1.metric("Partner G", f"{o['G']:.2f}", help="Slightly above Brandon's G — moral depth match")
        oc2.metric("Partner I", f"{o['I']:.2f}", help="Similar I — i-channel resonance")
        oc3.metric("Partner L", f"{o['L']:.2f}", help="Higher L ideal — complements Brandon's L")
        oc4.metric("Partner E", f"{o['E']:.2f}", help="E matched — same lifestyle quadrant")
        partner_gil = gil_composite(o['G'], o['I'], o['L'])
        pq, pql = get_quadrant(partner_gil, o['E'])
        st.success(f"Target partner quadrant: **{pq}** — {pql} | GIL: {partner_gil:.3f}")

        st.markdown("### Key Recognition Signals")
        for s in ideal['key_signals']:
            st.markdown(f"✅ {s}")

        st.markdown("### Disqualifiers")
        for d in ideal['disqualifiers']:
            st.markdown(f"❌ {d}")

        st.markdown("### Meeting Venue Predictions")
        mv = ideal['meeting_venue_prediction']
        for rank, desc in mv.items():
            label = rank.replace('_', ' ').title()
            st.markdown(f"**{label}:** {desc}")

        st.info(
            "**The Grand Illusion Filter (URB #482):** Brandon's ideal partner "
            "will NOT primarily use conventional E-metrics to assess him. "
            "They will perceive his GIL directly — not confused by his Q2 profile. "
            "A partner who sees his challenging E-metrics first and is repelled "
            "has already failed the compatibility test, regardless of other qualities.",
            icon="🔬"
        )

    # ── INVESTOR ──────────────────────────────────────────────────────────────
    with domain_tab2:
        st.subheader("Investor Compatibility — BlissGene $750K Seed")
        st.markdown(
            "The Inverse Metric Problem applies to investor assessment too. "
            "A Q3 investor will assess BlissGene using E-only metrics "
            "(TAM, CAC, MRR) and will try to strip the GIL core. "
            "The right investor must be Q1 or Q2 with abstraction capacity."
        )
        ideal_inv = get_ideal_investor_profile()

        req_col, flag_col = st.columns(2)
        with req_col:
            st.markdown("**Required Investor Profile**")
            for k, v in ideal_inv['required'].items():
                st.markdown(f"- **{k.replace('_',' ').title()}:** {v}")
            st.markdown("**Positive Indicators**")
            for ind in ideal_inv['indicators_of_right_investor']:
                st.markdown(f"✅ {ind}")
        with flag_col:
            st.markdown("**Red Flags — Q3 Investor Pattern**")
            for rf in ideal_inv['red_flags']:
                st.markdown(f"🚩 {rf}")
            st.markdown("**BlissGene $750K Target Note**")
            st.info(ideal_inv['blissgene_750k_target']['note'])

        st.divider()
        st.markdown("### Live Investor Compatibility Checker")
        st.caption("Enter a potential investor's estimated profile to generate compatibility prediction.")

        inv_name = st.text_input("Investor Name / Firm", key="inv_name_md")
        inv_g = st.slider("Investor G-score (Values depth)", 0.0, 1.0, 0.5, 0.05, key="inv_g")
        inv_i = st.slider("Investor I-score (Abstraction / i-channel)", 0.0, 1.0, 0.4, 0.05, key="inv_i")
        inv_l = st.slider("Investor L-score (Genuine care vs. ROI-only)", 0.0, 1.0, 0.4, 0.05, key="inv_l")
        inv_e = st.slider("Investor E-score (Conventional success)", 0.0, 1.0, 0.8, 0.05, key="inv_e")
        inv_abs = st.slider("Abstraction Capacity (spiritual/consciousness openness)", 0.0, 1.0, 0.4, 0.05, key="inv_abs")

        if inv_name:
            inv_profile = PartnerProfile(
                name=inv_name, domain='investor',
                g_score=inv_g, i_score=inv_i, l_score=inv_l, e_score=inv_e,
                abstraction_capacity=inv_abs,
            )
            compat = InvestorCompatibility(
                brandon=brandon,
                investor_name=inv_name,
                investor_profile=inv_profile,
            )
            inv_q, inv_ql = inv_profile.quadrant
            st.markdown(f"**{inv_name} Quadrant:** {inv_q} — {inv_ql}")
            st.markdown(f"**Emerick Floor:** {'✅ Passes' if inv_profile.passes_emerick_floor else '❌ Below threshold'}")
            st.markdown(f"**Alignment Score:** {compat.alignment_score:.2f}")
            st.markdown(f"**Grand Illusion Risk:** {inv_profile.grand_illusion_risk}")

            verdict = compat.blissgene_fit
            if verdict.startswith("EXCELLENT"):
                st.success(verdict)
            elif verdict.startswith("GOOD"):
                st.info(verdict)
            elif verdict.startswith("MARGINAL"):
                st.warning(verdict)
            else:
                st.error(verdict)

            st.markdown(f"**Recommended Pitch Strategy:**")
            st.markdown(compat.pitch_strategy)

    # ── COLLABORATOR ─────────────────────────────────────────────────────────
    with domain_tab3:
        st.subheader("Research Collaborator Predictions")

        coll_tab1, coll_tab2, coll_tab3 = st.tabs([
            "⚡ Hull Tactical ($100K)", "🏆 Kaggle", "🎓 Academic"
        ])

        with coll_tab1:
            hull = get_ideal_collaborator_profile('hull_tactical')
            st.markdown(f"**Required I-dimension:** ≥ {hull['required_I']}")
            st.markdown(f"**Why:** {hull['description']}")
            st.markdown("**Ideal Collaborator Indicators:**")
            for ind in hull['indicators']:
                st.markdown(f"✅ {ind}")
            st.info(
                "The Hull Tactical competition requires holding quantitative rigor AND "
                "TI Sigma's non-conventional signals simultaneously — a classic Tralse capacity. "
                "A pure quant collaborator (Q3) will reject the i-channel signals. "
                "A pure framework thinker without quant skill cannot execute. "
                "The ideal collaborator is Q1 or Q2 with demonstrable Python/ML skills.",
                icon="⚡"
            )

        with coll_tab2:
            kag = get_ideal_collaborator_profile('kaggle')
            st.markdown(f"**Required I-dimension:** ≥ {kag['required_I']}")
            st.markdown(f"**Why:** {kag['description']}")
            st.markdown("**Ideal Collaborator Indicators:**")
            for ind in kag['indicators']:
                st.markdown(f"✅ {ind}")

        with coll_tab3:
            acad = get_ideal_collaborator_profile('academic')
            st.markdown(f"**Required I-dimension:** ≥ {acad['required_I']}")
            st.markdown(f"**Why:** {acad['description']}")
            st.markdown("**Ideal Collaborator Indicators:**")
            for ind in acad['indicators']:
                st.markdown(f"✅ {ind}")

    # ── POWER OF 8 ────────────────────────────────────────────────────────────
    with domain_tab4:
        st.subheader("Power of 8 Group Composition Optimizer")
        st.markdown(
            "The collective GIL composite must reach **C_EMERICK = {:.4f}** "
            "for the intention field to achieve coherent strength. "
            "Q3 members dilute the group composite. "
            "Q2 members amplify through the unrecognized i-channel.".format(CEMD)
        )

        st.markdown("### Configure Your Group")
        n_members = st.number_input("Number of group members (excluding you)", 1, 7, 3, key="p8_n")
        members = []
        for i in range(int(n_members)):
            with st.expander(f"Member {i+1}", expanded=(i == 0)):
                m_name = st.text_input(f"Name", key=f"p8_name_{i}", value=f"Member {i+1}")
                m_g = st.slider(f"G-score", 0.0, 1.0, 0.55, 0.05, key=f"p8_g_{i}")
                m_i = st.slider(f"I-score", 0.0, 1.0, 0.50, 0.05, key=f"p8_i_{i}")
                m_l = st.slider(f"L-score", 0.0, 1.0, 0.55, 0.05, key=f"p8_l_{i}")
                m_e = st.slider(f"E-score", 0.0, 1.0, 0.45, 0.05, key=f"p8_e_{i}")
                members.append(PartnerProfile(
                    name=m_name, domain='power_of_8',
                    g_score=m_g, i_score=m_i, l_score=m_l, e_score=m_e,
                    abstraction_capacity=m_i,
                ))

        target = st.text_input("Group Intention Target", value="BlissGene seed round + Hull Tactical win", key="p8_target")

        if members:
            group = analyze_power_of_8_group(members, target, brandon)

            gc1, gc2, gc3 = st.columns(3)
            gc1.metric("Group GIL Composite", f"{group.group_gil_composite:.3f}",
                       help=f"Target: ≥ {CEMD:.4f}")
            gc2.metric("Transcendence Probability", f"{group.group_transcendence_probability:.0%}")
            q3_count = len(group.q3_members)
            gc3.metric("Q3 Members (diluting)", str(q3_count),
                       delta="Remove from core circle" if q3_count > 0 else "None — group is clean",
                       delta_color="inverse" if q3_count > 0 else "normal")

            rec = group.recommendation
            if rec.startswith("GROUP READY"):
                st.success(rec)
            elif rec.startswith("STRONG"):
                st.info(rec)
            elif rec.startswith("APPROACHING"):
                st.warning(rec)
            else:
                st.error(rec)

            if group.weakest_link:
                wl = group.weakest_link
                wq, wql = wl.quadrant
                st.markdown(
                    f"**Weakest link:** {wl.name} (GIL: {wl.gil:.3f}, {wq}) — "
                    f"focus development here first or reassign to support role."
                )

    # ── CRYSTAL CASE ─────────────────────────────────────────────────────────
    with domain_tab5:
        st.subheader("Crystal Case Analysis — Spiritual Facade Detector")
        st.markdown(
            "The Crystal Pattern is a Q3 individual presenting high E-level spiritual "
            "signals (language, ceremony, labels) while having low actual GIL. "
            "Key tell: **fear response when encountering authentic Q2 GIL**. "
            "Authentic GIL does not fear adjacent authentic GIL — only the facade fears exposure."
        )

        st.markdown("### Crystal — Confirmed Case Study")
        cc = CRYSTAL_CASE
        c1, c2, c3 = st.columns(3)
        c1.metric("Apparent Spiritual Level", f"{cc.apparent_spiritual_level:.2f}",
                  help="Outer presentation — E-dimension spiritual signaling")
        actual_gil = gil_composite(cc.behavioral_G_signals, cc.behavioral_I_signals, cc.behavioral_L_signals)
        c2.metric("Actual GIL Composite", f"{actual_gil:.3f}",
                  delta=f"{'Above' if actual_gil >= CEMD else 'Below'} C_EMERICK",
                  delta_color="normal" if actual_gil >= CEMD else "inverse")
        c3.metric("Facade Score", f"{cc.facade_score:.2f}",
                  help="Gap between E-spiritual performance and actual GIL")

        q_label = cc.quadrant
        st.markdown(f"**Quadrant:** {q_label} | **Fear response to Q2:** {'Yes' if cc.fear_response_to_Q2 else 'No'} | **Sitter confirmed:** {'Yes' if cc.sitter_or_observer_confirmation else 'No'}")

        if cc.facade_score >= 0.6:
            st.error(f"**Verdict:** {cc.verdict}")
        elif cc.facade_score >= 0.35:
            st.warning(f"**Verdict:** {cc.verdict}")
        else:
            st.success(f"**Verdict:** {cc.verdict}")

        st.markdown(f"**Case Notes:** {cc.notes}")

        st.divider()
        st.markdown("### Evaluate Any Person")
        st.caption("Use the framework to assess any person across all domains.")

        p_name = st.text_input("Person Name", key="facade_name")
        p_app = st.slider("Apparent spiritual/GIL level (self-reported or observed)", 0.0, 1.0, 0.5, 0.05, key="facade_app")
        p_bg = st.slider("Behavioral G signals (actual moral depth observed)", 0.0, 1.0, 0.3, 0.05, key="facade_bg")
        p_bi = st.slider("Behavioral I signals (genuine insight observed)", 0.0, 1.0, 0.3, 0.05, key="facade_bi")
        p_bl = st.slider("Behavioral L signals (genuine other-orientation observed)", 0.0, 1.0, 0.3, 0.05, key="facade_bl")
        p_fear = st.checkbox("Fear/discomfort response when encountering Brandon's intensity?", key="facade_fear")
        p_confirm = st.checkbox("Third-party confirmed behavioral inconsistency?", key="facade_confirm")

        if p_name:
            from multi_domain_partner_engine import SpiritualFacadeAssessment
            assessment = SpiritualFacadeAssessment(
                name=p_name,
                apparent_spiritual_level=p_app,
                behavioral_G_signals=p_bg,
                behavioral_I_signals=p_bi,
                behavioral_L_signals=p_bl,
                e_spiritual_performance=p_app,
                sitter_or_observer_confirmation=p_confirm,
                fear_response_to_Q2=p_fear,
            )
            pq = assessment.quadrant
            pfs = assessment.facade_score
            pa_gil = gil_composite(p_bg, p_bi, p_bl)
            st.markdown(f"**{p_name}** — Quadrant: {pq} | Actual GIL: {pa_gil:.3f} | Facade Score: {pfs:.2f}")
            verdict = assessment.verdict
            if pfs >= 0.6:
                st.error(f"**{verdict}**")
            elif pfs >= 0.35:
                st.warning(f"**{verdict}**")
            else:
                st.success(f"**{verdict}**")


# ── Dataset registry content (shared between tabs) ────────────────────────────
INTENTION_DATASETS = [
    {
        "name": "Global Consciousness Project (GCP)",
        "org": "Princeton University / IONS",
        "url": "https://gcpdot.com",
        "live": True,
        "target": "Physical — REG network",
        "n": "700+ nodes, continuous since 1998",
        "effect": "Z > 2.0 during major world events",
        "license": "Open academic",
        "ti_metric": "ΔZ × C_EMERICK = TJ estimate per node",
        "p8_use": "Conduct timed P8 session → analyze GCP data for that window",
        "description": (
            "The gold-standard ongoing consciousness field measurement. "
            "700+ REG nodes globally. During group coherence events (meditations, mass crises), "
            "the network shows statistically significant correlation. "
            "**LIVE data now accessible via gcpdot.com** — see the GCP Analysis tab."
        ),
    },
    {
        "name": "PEAR Laboratory REG Dataset",
        "org": "Princeton Engineering Anomalies Research (ICRL)",
        "url": "https://icrl.org",
        "live": False,
        "target": "Physical — operator-directed REG",
        "n": "~2.5 million trials, 26 years",
        "effect": "d ≈ 0.0001/trial, cumulative Z = 3.8",
        "license": "Open academic",
        "ti_metric": "Shift magnitude → individual f baseline for Γ_group model",
        "p8_use": "Calibrate individual f per P8 participant; validate single-person TJ",
        "description": (
            "The largest database of human-REG interaction. Operator intention → "
            "consistent small REG biases. "
            "Key for calibrating the **individual f parameter** in Γ_group = N × C × f. "
            "PEAR data suggests f ≈ 0.01–0.05 per individual trial; "
            "P8 amplification to f ≈ 0.30 is a 6–30× amplification factor."
        ),
    },
    {
        "name": "IONS Distant Healing RCT Dataset",
        "org": "Institute of Noetic Sciences",
        "url": "https://osf.io/ions",
        "live": False,
        "target": "Biological — human healing outcomes",
        "n": "Multiple RCTs; largest N≈150 (Sicher 1998)",
        "effect": "d ≈ 0.35–0.65 in blinded RCTs",
        "license": "Open Science Framework",
        "ti_metric": "Healing rate acceleration ∝ Γ_group × TJ_delivered",
        "p8_use": "Sicher AIDS protocol as model for P8 chronic illness intentions",
        "description": (
            "Sicher et al. (1998): 40 distant healers, 40 AIDS patients, blinded, p=0.04 "
            "for hospitalization frequency. Wirth (1990): wound healing, p<0.001. "
            "These are the **gold standard biological healing datasets**. "
            "Cross-reference: ANIMAL PSI FRAMEWORK (Nov 2025) predicts healing effect "
            "scales with healer Φ — Bengston mice data confirms this."
        ),
    },
    {
        "name": "Bengston Mouse Tumor Healing",
        "org": "William Bengston / Sacred Science",
        "url": "https://williamjbengston.com",
        "live": False,
        "target": "Animal — mammary adenocarcinoma tumor regression",
        "n": "Multiple replications, n=5–30 mice each",
        "effect": "100% remission in treated vs 0% controls",
        "license": "On request from Bengston",
        "ti_metric": "Tumor volume time series vs TJ attractor model",
        "p8_use": "Model the 7-session spiral regression pattern (mirrors LCC attractor escape)",
        "description": (
            "The most dramatic replicable effect in distant healing research. "
            "100% remission replicated at 4 universities. Tumor regression follows "
            "a **spiral pattern** — fast shrinkage → apparent return → full cure — "
            "which exactly mirrors the LCC **attractor basin escape trajectory** "
            "(GRAND PSI PROOF, Jan 2026). 7 Bengston sessions ≈ 7 P8 sessions ≈ "
            "15 TJ threshold (URB #413). This is not coincidental."
        ),
    },
    {
        "name": "DMILS Electrophysiology Database",
        "org": "Dean Radin / IONS + multiple labs",
        "url": "https://osf.io",
        "live": False,
        "target": "Human — EEG/EDA/HRV of receiver",
        "n": "Several hundred dyad sessions",
        "effect": "EDA correlation r≈0.25; EEG gamma coupling p<0.05",
        "license": "OSF open data",
        "ti_metric": "Cross-correlation of sender/receiver HRV → empirical f measurement",
        "p8_use": "Direct calibration: measure HRV synchrony → get real-time f for Γ_group",
        "description": (
            "Best dataset for calibrating the **f (coordination quality) parameter** directly. "
            "Receiver shows different EDA/HRV during 'attended' vs 'unattended' periods — "
            "r≈0.25 coupling without any conventional signal. "
            "TI Sigma prediction: In a P8 session, f should correlate with HRV coherence "
            "of sender-receiver dyads. Polar H10 + HRV analysis can measure this live."
        ),
    },
    {
        "name": "HeartMath Global Coherence Initiative",
        "org": "HeartMath Institute",
        "url": "https://heartmath.org/gci",
        "live": True,
        "target": "Physical — Earth magnetometers + HRV",
        "n": "Continuous since 2008, 6 global sites",
        "effect": "Significant correlation with group HRV during coherence events",
        "license": "Request from HeartMath",
        "ti_metric": "Schumann resonance 7.83 Hz ≈ θ_adapt coupling",
        "p8_use": "Correlate P8 session times with local magnetometer deviations",
        "description": (
            "Schumann resonance at 7.83 Hz is within the theta-alpha consciousness band. "
            "URB #411 shows TI Sigma's θ-frequency = 4.812 Hz — both within the "
            "7–8 Hz range linking brain theta rhythms to Earth's cavity resonance. "
            "TI prediction: Γ_group > 1 sessions should produce signatures in local "
            "HeartMath magnetometer data. Testable with the GCI sensor in nearest city."
        ),
    },
    {
        "name": "Bem Precognition OSF Meta-Dataset",
        "org": "Daryl Bem + 90 replication labs",
        "url": "https://osf.io/juanr",
        "live": False,
        "target": "Psychological — human precognition trials",
        "n": "2,469 participants, 90 labs",
        "effect": "d = 0.22, p < 10⁻¹⁰ in meta-analysis",
        "license": "Fully open Creative Commons",
        "ti_metric": "Hit rate > 50% → Tral-state temporal asymmetry",
        "p8_use": "Test if P8 group precognition exceeds individual baseline d=0.22",
        "description": (
            "90+ labs, d=0.22, p<10⁻¹⁰ — the most statistically robust PSI dataset. "
            "The Tralse model explains precognition as **time-reversed C_EMERICK coupling**: "
            "since Tralse logic is time-symmetric (Tr-states can be both-past-and-future), "
            "the 0.22 effect is the Tral-state 'leakage' across time direction. "
            "P8 prediction: Γ_group > 1 → group precognition d > individual 0.22."
        ),
    },
    {
        "name": "CIA STARGATE Remote Viewing Archive",
        "org": "Stanford Research Institute (declassified)",
        "url": "https://cia.gov/readingroom/collection/stargate",
        "live": False,
        "target": "Psychological — trained remote viewing",
        "n": "20,000+ trials, 1972–1995",
        "effect": "d ≈ 0.5 for trained viewers",
        "license": "Public domain (US government)",
        "ti_metric": "Hit rate × target-viewer distance → non-local coupling constant",
        "p8_use": "Use group remote viewing of live targets as P8 experiment variant",
        "description": (
            "20,000+ declassified CIA transcripts. Targ & Puthoff (SRI) showed "
            "trained viewers achieve d≈0.5 — significantly above Bem's individual baseline d=0.22. "
            "TI Sigma interpretation: training raises LCC activation level (from 0.42 → 0.85 range), "
            "increasing effective f. A trained P8 group (Ingo Swann-level) would predict "
            "Γ_group = 8 × 0.437 × 0.65 ≈ 2.28 >> unity — extraordinary coherence."
        ),
    },
]


def _show_dataset_registry():
    """Shared dataset registry display used in multiple tabs."""
    target_filter = st.multiselect(
        "Filter by target type",
        ["Physical", "Biological", "Animal", "Human", "Psychological"],
        default=["Physical", "Biological", "Animal", "Human", "Psychological"],
        key="ds_filter"
    )
    live_only = st.checkbox("Live/ongoing only", False, key="ds_live")

    for ds in INTENTION_DATASETS:
        t_type = ds["target"].split("—")[0].strip()
        if not any(f.lower() in t_type.lower() for f in target_filter):
            continue
        if live_only and not ds["live"]:
            continue

        badge = "🟢 **LIVE**" if ds["live"] else "📦 **Archive**"
        with st.expander(f"{badge} — **{ds['name']}** | {ds['org']} | {ds['n']}"):
            c1, c2 = st.columns([3, 1])
            with c1:
                st.markdown(ds["description"])
                st.markdown(f"**Effect size:** {ds['effect']}")
                st.markdown(f"**P8 use:** {ds['p8_use']}")
            with c2:
                st.markdown(f"**Format:** {ds['target']}")
                st.markdown(f"**License:** {ds['license']}")
                st.markdown(f"**TI metric:** {ds['ti_metric']}")
                st.markdown(f"[Visit dataset]({ds['url']})")


if __name__ == "__main__":
    show_intention_validation()
