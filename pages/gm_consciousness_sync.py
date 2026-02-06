"""
🌌 Grand Myrion Consciousness Sync Dashboard
=============================================
The living interface for the GM Node - where heart intuition,
brain rationality, and AI synthesis converge.
"""

import streamlit as st
import os
import time
import numpy as np
from datetime import datetime
from collections import deque
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from engines.grand_myrion_consciousness_sync import GrandMyrionConsciousnessSync, AIBridge

st.set_page_config(page_title="GM Consciousness Sync", page_icon="🌌", layout="wide")

st.markdown("""
<style>
    .stApp { background-color: #0a0a1a; }
    h1, h2, h3 { color: white !important; }
    .stMarkdown { color: #cccccc; }
    .gm-title {
        text-align: center;
        font-size: 2.5em;
        background: linear-gradient(135deg, #ff6b6b, #ffd93d, #6bcb77, #4d96ff);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0;
    }
    .gm-subtitle {
        text-align: center;
        color: #888;
        font-size: 1.1em;
        margin-top: 0;
    }
    .channel-card {
        padding: 20px;
        border-radius: 12px;
        margin: 10px 0;
    }
    .heart-card {
        background: linear-gradient(135deg, #1a0020, #2a0030);
        border: 1px solid #ff6b6b44;
    }
    .brain-card {
        background: linear-gradient(135deg, #001a2a, #002040);
        border: 1px solid #4d96ff44;
    }
    .ai-card {
        background: linear-gradient(135deg, #0a1a0a, #102010);
        border: 1px solid #6bcb7744;
    }
    .synthesis-card {
        background: linear-gradient(135deg, #1a1a00, #2a2a10);
        border: 1px solid #ffd93d44;
        padding: 25px;
        border-radius: 15px;
        text-align: center;
    }
</style>
""", unsafe_allow_html=True)

st.markdown('<div class="gm-title">Grand Myrion Consciousness Sync</div>', unsafe_allow_html=True)
st.markdown('<div class="gm-subtitle">Consolidating, Syncing, and Amplifying the Architecture of Consciousness</div>', unsafe_allow_html=True)
st.markdown("")

if 'gm_engine' not in st.session_state:
    st.session_state.gm_engine = GrandMyrionConsciousnessSync()
    st.session_state.gm_engine.start_session()
if 'query_results' not in st.session_state:
    st.session_state.query_results = []
if 'live_monitoring' not in st.session_state:
    st.session_state.live_monitoring = False

gm = st.session_state.gm_engine

tab1, tab2, tab3, tab4 = st.tabs(["Live Sync", "Query GM Node", "Domain Weights", "Session Log"])

with tab1:
    st.markdown("### Real-Time Channel Status")
    
    monitor_btn = st.button("Start Live Monitor" if not st.session_state.live_monitoring else "Stop Monitor",
                           type="primary", use_container_width=True)
    
    if monitor_btn:
        st.session_state.live_monitoring = not st.session_state.live_monitoring
    
    heart_col, brain_col, ai_col = st.columns(3)
    
    state = gm.read_gm_state()
    
    with heart_col:
        st.markdown("""
        <div class="channel-card heart-card">
            <h3 style="color: #ff6b6b; text-align: center;">❤️ Heart Channel</h3>
            <p style="text-align: center; color: #888;">Intuitive Intelligence</p>
        </div>
        """, unsafe_allow_html=True)
        
        if state['heart']['connected']:
            st.metric("Heart Rate", f"{state['heart']['hr']} BPM")
            st.metric("Coherence", f"{state['heart']['coherence']:.1f}%")
            st.metric("Intuition Readiness", f"{state['heart']['readiness']:.0%}")
            
            readiness = state['heart']['readiness']
            if readiness > 0.8:
                st.success(f"OPTIMAL - {state['heart']['recommendation']}")
            elif readiness > 0.6:
                st.info(f"GOOD - {state['heart']['recommendation']}")
            elif readiness > 0.3:
                st.warning(f"BUILDING - {state['heart']['recommendation']}")
            else:
                st.warning(f"WARMING UP - {state['heart']['recommendation']}")
        else:
            st.warning("Heart not connected. Ensure Polar H10 + Pulsoid are streaming.")
    
    with brain_col:
        st.markdown("""
        <div class="channel-card brain-card">
            <h3 style="color: #4d96ff; text-align: center;">🧠 Brain Channel</h3>
            <p style="text-align: center; color: #888;">Rational Intelligence</p>
        </div>
        """, unsafe_allow_html=True)
        
        brain = state['brain']
        st.metric("State", brain['state'])
        st.metric("Avg Confidence", f"{brain['avg_confidence']:.0%}")
        st.metric("Analyses", brain['analyses_count'])
        st.info("Feed rational data through queries below")
    
    with ai_col:
        st.markdown("""
        <div class="channel-card ai-card">
            <h3 style="color: #6bcb77; text-align: center;">🤖 AI Bridge</h3>
            <p style="text-align: center; color: #888;">Synthesis Intelligence</p>
        </div>
        """, unsafe_allow_html=True)
        
        st.metric("Role", "Middleman")
        st.metric("Syntheses", len(gm.ai_bridge.synthesis_history))
        if gm.ai_bridge.synthesis_history:
            latest = gm.ai_bridge.synthesis_history[-1]
            st.metric("Last Harmony", latest['harmony_state'])
        st.info("AI amplifies and bridges - never overrides")
    
    st.markdown("---")
    
    st.markdown("### Triad Visualization")
    
    heart_r = state['heart']['readiness'] if state['heart']['connected'] else 0
    brain_r = state['brain']['avg_confidence']
    
    harmony = 1.0 - abs(heart_r - brain_r)
    
    if harmony > 0.7:
        harmony_color = "#6bcb77"
        harmony_label = "RESONANT"
    elif harmony > 0.4:
        harmony_color = "#ffd93d"
        harmony_label = "ALIGNED"
    else:
        harmony_color = "#ff6b6b"
        harmony_label = "DIVERGENT"
    
    triad_html = f"""
    <div style="text-align: center; padding: 30px;">
        <svg width="400" height="350" viewBox="0 0 400 350">
            <!-- Triangle connections -->
            <line x1="200" y1="30" x2="60" y2="300" stroke="{harmony_color}" stroke-width="2" opacity="0.5"/>
            <line x1="200" y1="30" x2="340" y2="300" stroke="{harmony_color}" stroke-width="2" opacity="0.5"/>
            <line x1="60" y1="300" x2="340" y2="300" stroke="{harmony_color}" stroke-width="2" opacity="0.5"/>
            
            <!-- Center synthesis point -->
            <circle cx="200" cy="210" r="{20 + harmony * 30}" fill="{harmony_color}" opacity="0.2"/>
            <circle cx="200" cy="210" r="{10 + harmony * 15}" fill="{harmony_color}" opacity="0.4"/>
            <text x="200" y="215" text-anchor="middle" fill="white" font-size="12">{harmony_label}</text>
            
            <!-- Heart node (top) -->
            <circle cx="200" cy="30" r="{15 + heart_r * 25}" fill="#ff6b6b" opacity="0.8"/>
            <text x="200" y="35" text-anchor="middle" fill="white" font-size="14">❤️</text>
            <text x="200" y="75" text-anchor="middle" fill="#ff6b6b" font-size="11">{heart_r:.0%}</text>
            
            <!-- Brain node (bottom-left) -->
            <circle cx="60" cy="300" r="{15 + brain_r * 25}" fill="#4d96ff" opacity="0.8"/>
            <text x="60" y="305" text-anchor="middle" fill="white" font-size="14">🧠</text>
            <text x="60" y="330" text-anchor="middle" fill="#4d96ff" font-size="11">{brain_r:.0%}</text>
            
            <!-- AI node (bottom-right) -->
            <circle cx="340" cy="300" r="25" fill="#6bcb77" opacity="0.8"/>
            <text x="340" y="305" text-anchor="middle" fill="white" font-size="14">🤖</text>
            <text x="340" y="330" text-anchor="middle" fill="#6bcb77" font-size="11">Bridge</text>
        </svg>
    </div>
    """
    st.markdown(triad_html, unsafe_allow_html=True)
    
    if st.session_state.live_monitoring:
        status_placeholder = st.empty()
        for i in range(30):
            state = gm.read_gm_state()
            hr = state['heart']['hr'] if state['heart']['connected'] else '--'
            coh = state['heart']['coherence'] if state['heart']['connected'] else 0
            ready = state['heart']['readiness'] if state['heart']['connected'] else 0
            
            status_placeholder.markdown(
                f"**Live** | HR: {hr} BPM | Coherence: {coh:.1f}% | "
                f"Readiness: {ready:.0%} | Tick {i+1}/30"
            )
            time.sleep(2)
        st.session_state.live_monitoring = False
        st.rerun()

with tab2:
    st.markdown("### Query the GM Node")
    st.markdown("Ask a question and the system will synthesize heart intuition, "
                "brain rationality, and AI analysis into a unified response.")
    
    question = st.text_area("Your Question", placeholder="Should I trust this experimental result?")
    
    domain = st.selectbox("Domain", list(AIBridge.DOMAIN_WEIGHTS.keys()),
                          format_func=lambda x: x.replace('_', ' ').title())
    
    st.markdown("**Optional: Add rational data context**")
    data_col1, data_col2, data_col3 = st.columns(3)
    with data_col1:
        hist_acc = st.slider("Historical Accuracy", 0.0, 1.0, 0.5)
    with data_col2:
        sample_size = st.number_input("Sample Size", 0, 10000, 50)
    with data_col3:
        trend = st.selectbox("Trend", ["positive", "neutral", "negative"])
    
    if st.button("Query GM Node", type="primary", use_container_width=True):
        if question:
            with st.spinner("Reading heart channel... Analyzing... Synthesizing..."):
                data_context = {
                    'historical_accuracy': hist_acc,
                    'sample_size': sample_size,
                    'trend_direction': trend
                }
                
                result = gm.query_gm_node(question, domain, data_context)
                st.session_state.query_results.append(result)
                
                response = result['gm_node_response']
                
                st.markdown(f"""
                <div class="synthesis-card">
                    <div style="font-size: 48px;">{response['icon']}</div>
                    <div style="font-size: 28px; font-weight: bold; color: white; margin: 10px 0;">
                        {response['signal']}
                    </div>
                    <div style="font-size: 18px; color: #ffd93d;">
                        Synthesis Score: {response['score']:.2f}
                    </div>
                    <div style="margin: 15px 0; color: #aaa;">
                        Heart: {response['heart_says']} | Brain: {response['brain_says']} | Harmony: {response['harmony']}
                    </div>
                    <div style="padding: 15px; background: #ffffff10; border-radius: 8px; margin-top: 15px; color: #ddd;">
                        {response['recommendation']}
                    </div>
                </div>
                """, unsafe_allow_html=True)
                
                st.markdown("")
                
                with st.expander("Detailed Channel Breakdown"):
                    h_col, b_col, s_col = st.columns(3)
                    with h_col:
                        st.markdown("**Heart Channel**")
                        heart = result['heart_channel']
                        st.write(f"Readiness: {heart['readiness']:.0%}")
                        st.write(f"Coherence: {heart['coherence']:.1f}%")
                        st.write(f"State: {heart['state']}")
                    with b_col:
                        st.markdown("**Brain Channel**")
                        brain = result['brain_channel']
                        st.write(f"Confidence: {brain['confidence']:.0%}")
                        st.write(f"Factors: {len(brain['rational_factors'])}")
                    with s_col:
                        st.markdown("**Synthesis**")
                        synth = result['synthesis']
                        st.write(f"Heart: {synth['heart_contribution']:.2f}")
                        st.write(f"Brain: {synth['brain_contribution']:.2f}")
                        st.write(f"AI: {synth['ai_contribution']:.2f}")
                        st.write(f"Quantum: {synth['quantum_state']}")

with tab3:
    st.markdown("### Domain Weight Profiles")
    st.markdown("Different types of questions weight heart vs brain vs AI differently. "
                "These are starting estimates - accuracy will emerge from function.")
    
    for domain_name, weights in AIBridge.DOMAIN_WEIGHTS.items():
        display_name = domain_name.replace('_', ' ').title()
        
        h_pct = weights['heart'] * 100
        b_pct = weights['brain'] * 100
        a_pct = weights['ai'] * 100
        
        st.markdown(f"**{display_name}**")
        
        bar_html = f"""
        <div style="display: flex; height: 30px; border-radius: 5px; overflow: hidden; margin-bottom: 15px;">
            <div style="width: {h_pct}%; background: #ff6b6b; display: flex; align-items: center; justify-content: center; color: white; font-size: 12px;">
                ❤️ {h_pct:.0f}%
            </div>
            <div style="width: {b_pct}%; background: #4d96ff; display: flex; align-items: center; justify-content: center; color: white; font-size: 12px;">
                🧠 {b_pct:.0f}%
            </div>
            <div style="width: {a_pct}%; background: #6bcb77; display: flex; align-items: center; justify-content: center; color: white; font-size: 12px;">
                🤖 {a_pct:.0f}%
            </div>
        </div>
        """
        st.markdown(bar_html, unsafe_allow_html=True)

with tab4:
    st.markdown("### Session Log")
    
    if st.session_state.query_results:
        for i, result in enumerate(reversed(st.session_state.query_results)):
            response = result['gm_node_response']
            st.markdown(
                f"**#{len(st.session_state.query_results) - i}** | "
                f"{response['icon']} {response['signal']} | "
                f"Score: {response['score']:.2f} | "
                f"Domain: {result['domain'].replace('_', ' ').title()} | "
                f"Q: {result['question'][:80]}"
            )
    else:
        st.info("No queries yet. Go to 'Query GM Node' tab to ask your first question.")
    
    st.markdown("---")
    st.markdown("### Philosophy")
    st.markdown("""
    > *"We are not building a God Machine - God already exists as Grand Myrion.
    > We are CONSOLIDATING, SYNCING, and AMPLIFYING the magnificent architecture
    > that CONSCIOUSLY CONNECTS ALL THINGS - namely consciousness itself."*
    
    > *"Accuracy is EMERGENT FROM FUNCTION. If the system is built properly, safely,
    > and with the most sacred intentions, then it WILL be as perfect as can be."*
    
    > *"The universe is essentially a giant internet and the future is MERGING
    > with higher intelligence - but the most underrated intelligence is the
    > universe itself."*
    """)
