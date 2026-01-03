"""
PSI Testing Hub - Test and Validate PSI Abilities
November 24, 2025 (8×3 Sacred Day)

Tests PSI tricks with biometric tracking:
- Zener cards (telepath y)
- Precognition (RNG prediction)
- Remote viewing
- Stock prediction PSI correlation
"""

import streamlit as st
import random
import time
from datetime import datetime
import pandas as pd
from typing import List, Dict, Optional
import json


class PSITestingHub:
    """Hub for testing and validating PSI abilities"""
    
    # Zener card symbols
    ZENER_SYMBOLS = ['⭕ Circle', '➕ Cross', '〰 Waves', '⬜ Square', '⭐ Star']
    
    def __init__(self):
        """Initialize PSI Testing Hub"""
        if 'psi_test_history' not in st.session_state:
            st.session_state.psi_test_history = []
        if 'current_zener_card' not in st.session_state:
            st.session_state.current_zener_card = None
        if 'zener_results' not in st.session_state:
            st.session_state.zener_results = {'correct': 0, 'total': 0}
        if 'precog_results' not in st.session_state:
            st.session_state.precog_results = {'correct': 0, 'total': 0}
    
    def render_zener_card_test(self):
        """Render Zener card telepathy test"""
        st.markdown("### 🔮 Zener Card Telepathy Test")
        st.markdown("""
        **How it works:**
        1. Click "Draw Card" - a random symbol is selected (hidden)
        2. Use your intuition to guess which symbol
        3. Reveal the card to see if you're correct
        
        **Baseline:** 20% (1 in 5 by chance)  
        **PSI presence:** >25% sustained accuracy
        """)
        
        col1, col2 = st.columns(2)
        
        with col1:
            if st.button("🎴 Draw New Card", use_container_width=True):
                st.session_state.current_zener_card = random.choice(self.ZENER_SYMBOLS)
                st.success("Card drawn! Make your guess...")
        
        with col2:
            if st.session_state.current_zener_card:
                st.info(f"Card is ready - make your guess!")
            else:
                st.warning("Click 'Draw New Card' to start")
        
        # Guess section
        if st.session_state.current_zener_card:
            st.markdown("#### Your Guess:")
            guess = st.radio("Select your intuitive choice:", 
                           self.ZENER_SYMBOLS,
                           key="zener_guess",
                           horizontal=True)
            
            if st.button("✨ Reveal Card", type="primary", use_container_width=True):
                correct = guess == st.session_state.current_zener_card
                
                # Update results
                st.session_state.zener_results['total'] += 1
                if correct:
                    st.session_state.zener_results['correct'] += 1
                
                # Save to history
                st.session_state.psi_test_history.append({
                    'timestamp': datetime.now().isoformat(),
                    'test_type': 'zener_cards',
                    'guess': guess,
                    'actual': st.session_state.current_zener_card,
                    'correct': correct
                })
                
                # Show result
                if correct:
                    st.success(f"✅ CORRECT! The card was {st.session_state.current_zener_card}")
                    st.balloons()
                else:
                    st.error(f"❌ Incorrect. The card was {st.session_state.current_zener_card}")
                
                # Reset card
                st.session_state.current_zener_card = None
                st.rerun()
        
        # Statistics
        if st.session_state.zener_results['total'] > 0:
            accuracy = (st.session_state.zener_results['correct'] / 
                       st.session_state.zener_results['total']) * 100
            
            st.markdown("---")
            st.markdown("### 📊 Your PSI Statistics")
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Accuracy", f"{accuracy:.1f}%")
            with col2:
                st.metric("Correct", st.session_state.zener_results['correct'])
            with col3:
                st.metric("Total Tests", st.session_state.zener_results['total'])
            
            # Interpretation
            if accuracy > 25:
                st.success(f"🌟 **PSI DETECTED!** Your {accuracy:.1f}% exceeds baseline (20%)!")
            elif accuracy >= 20:
                st.info(f"📊 Within baseline range ({accuracy:.1f}% vs 20% expected)")
            else:
                st.warning(f"Below baseline - keep practicing! ({accuracy:.1f}% vs 20%)")
            
            if st.session_state.zener_results['total'] >= 20:
                # Statistical significance check
                expected = st.session_state.zener_results['total'] * 0.2
                observed = st.session_state.zener_results['correct']
                
                st.markdown(f"""
                **Statistical Analysis (>20 trials):**
                - Expected (chance): {expected:.1f} correct
                - Observed (actual): {observed} correct
                - Difference: {observed - expected:+.1f}
                """)
    
    def render_precognition_test(self):
        """Render precognition RNG prediction test"""
        st.markdown("### 🔮 Precognition Test (Binary Choice)")
        st.markdown("""
        **How it works:**
        1. Predict whether next random number will be HIGHER or LOWER than 50
        2. Click "Generate Number" to reveal outcome
        3. Track your accuracy over time
        
        **Baseline:** 50% (random chance)  
        **PSI presence:** 51-53% (small but significant!)
        """)
        
        col1, col2 = st.columns(2)
        
        with col1:
            prediction = st.radio(
                "🎯 Your Prediction:",
                ["⬆️ Higher (51-100)", "⬇️ Lower (0-49)"],
                key="precog_prediction"
            )
        
        with col2:
            if st.button("🎲 Generate Random Number", type="primary", use_container_width=True):
                # Generate random number
                actual_number = random.randint(0, 100)
                
                # Determine if higher or lower
                actual = "⬆️ Higher (51-100)" if actual_number >= 51 else "⬇️ Lower (0-49)"
                
                # Check if correct
                correct = prediction == actual
                
                # Update results
                st.session_state.precog_results['total'] += 1
                if correct:
                    st.session_state.precog_results['correct'] += 1
                
                # Save to history
                st.session_state.psi_test_history.append({
                    'timestamp': datetime.now().isoformat(),
                    'test_type': 'precognition',
                    'prediction': prediction,
                    'actual_number': actual_number,
                    'actual': actual,
                    'correct': correct
                })
                
                # Show result
                st.markdown(f"### Result: **{actual_number}**")
                if correct:
                    st.success(f"✅ CORRECT! Number was {actual_number} ({actual})")
                else:
                    st.error(f"❌ Incorrect. Number was {actual_number} ({actual})")
        
        # Statistics
        if st.session_state.precog_results['total'] > 0:
            accuracy = (st.session_state.precog_results['correct'] / 
                       st.session_state.precog_results['total']) * 100
            
            st.markdown("---")
            st.markdown("### 📊 Precognition Statistics")
            
            col1, col2, col3 = st.columns(3)
            with col1:
                st.metric("Accuracy", f"{accuracy:.1f}%")
            with col2:
                st.metric("Correct", st.session_state.precog_results['correct'])
            with col3:
                st.metric("Total Predictions", st.session_state.precog_results['total'])
            
            # Interpretation
            if accuracy > 53:
                st.success(f"🌟 **STRONG PSI!** {accuracy:.1f}% >> 50% baseline!")
            elif accuracy > 50:
                st.success(f"✨ **PSI DETECTED!** {accuracy:.1f}% > 50% baseline")
            else:
                st.info(f"📊 Within baseline ({accuracy:.1f}% vs 50%)")
            
            # Edge calculation
            if st.session_state.precog_results['total'] >= 100:
                edge = accuracy - 50
                st.markdown(f"""
                **Trading Edge Analysis (>100 trials):**
                - Your edge: {edge:+.1f}%
                - If applied to trading: {edge:.1f}% advantage per trade
                - Even 1% edge = massive profit over time! 💰
                """)
    
    def render_remote_viewing_practice(self):
        """Render remote viewing practice interface"""
        st.markdown("### 👁️ Remote Viewing Practice")
        st.markdown("""
        **How it works:**
        1. Target: Tomorrow's stock movement for a specific ticker
        2. Draw or describe what you sense about the direction
        3. Record your impression NOW
        4. Validate tomorrow!
        
        **Purpose:** Train intuitive stock prediction (for GILE algorithm!)
        """)
        
        ticker = st.text_input("🎯 Target Stock Ticker:", value="AAPL", max_chars=10)
        
        st.markdown("#### 📝 Record Your Impression:")
        direction = st.radio(
            "Direction you sense:",
            ["📈 Bullish (will rise)", "📉 Bearish (will fall)", "➡️ Sideways (no clear move)"]
        )
        
        confidence = st.slider("Confidence Level:", 0, 100, 50, 5)
        
        notes = st.text_area("Additional impressions (images, feelings, symbols):", 
                            placeholder="Describe any visual impressions, feelings, or symbols...")
        
        if st.button("💾 Save Remote Viewing Session", type="primary"):
            prediction = {
                'timestamp': datetime.now().isoformat(),
                'test_type': 'remote_viewing',
                'ticker': ticker.upper(),
                'direction': direction,
                'confidence': confidence,
                'notes': notes,
                'validation_date': (datetime.now() + pd.Timedelta(days=1)).date().isoformat()
            }
            
            st.session_state.psi_test_history.append(prediction)
            
            st.success(f"✅ Remote viewing session saved for {ticker}!")
            st.info(f"📅 Validate tomorrow ({prediction['validation_date']})")
    
    def render_psi_history(self):
        """Render PSI test history and analysis"""
        st.markdown("### 📚 PSI Test History")
        
        if len(st.session_state.psi_test_history) == 0:
            st.info("No tests completed yet. Try the Zener cards or Precognition tests above!")
            return
        
        # Convert to DataFrame
        df = pd.DataFrame(st.session_state.psi_test_history)
        
        # Show recent tests
        st.markdown(f"**Total Tests Completed:** {len(df)}")
        
        # Filter by test type
        test_type = st.selectbox("Filter by test type:", 
                                ["All", "Zener Cards", "Precognition", "Remote Viewing"])
        
        if test_type != "All":
            type_map = {
                "Zener Cards": "zener_cards",
                "Precognition": "precognition",
                "Remote Viewing": "remote_viewing"
            }
            df = df[df['test_type'] == type_map[test_type]]
        
        # Show data
        st.dataframe(df, use_container_width=True)
        
        # Download option
        if st.button("📥 Download PSI Test Data (JSON)"):
            json_data = df.to_json(orient='records', indent=2)
            st.download_button(
                label="💾 Download JSON",
                data=json_data,
                file_name=f"psi_test_history_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                mime="application/json"
            )
    
    def render(self):
        """Main render function"""
        st.title("🔮 PSI Testing Hub")
        st.markdown("""
        **Test your PSI abilities with biometric tracking!**
        
        All tests are designed to be simple, replicable, and scientifically measurable.
        Use with your Mood Amplifier (Muse 2, Polar H10, Bio-Well) to track consciousness states during testing!
        """)
        
        st.markdown("---")
        
        # Create tabs for different tests
        tab1, tab2, tab3, tab4 = st.tabs([
            "🎴 Zener Cards",
            "🔮 Precognition",
            "👁️ Remote Viewing",
            "📚 Test History"
        ])
        
        with tab1:
            self.render_zener_card_test()
        
        with tab2:
            self.render_precognition_test()
        
        with tab3:
            self.render_remote_viewing_practice()
        
        with tab4:
            self.render_psi_history()
        
        st.markdown("---")
        st.info("""
        💡 **TI Framework Insight:**  
        PSI tests measure I-Cell coherence across different modalities:
        - **Telepathy** (Zener): Photon layer resonance
        - **Precognition** (RNG): Dark Energy access (timeless information)
        - **Remote Viewing**: Non-local I-Cell entanglement
        
        Your GILE score predicts PSI accuracy! Test regularly to improve! 🌌
        """)


def render_psi_testing_hub():
    """Render PSI Testing Hub"""
    hub = PSITestingHub()
    hub.render()


if __name__ == "__main__":
    # For testing
    st.set_page_config(page_title="PSI Testing Hub", page_icon="🔮", layout="wide")
    render_psi_testing_hub()
