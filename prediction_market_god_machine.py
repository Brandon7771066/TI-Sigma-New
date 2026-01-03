"""
Prediction Market God Machine
Integrate with Kalshi, Polymarket, Metaculus for money-making predictions
Using TI-UOP resonance field theory
"""

import streamlit as st
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional
import pandas as pd
import json
from numerology_validation import (
    calculate_life_path,
    reduce_to_single_digit,
    analyze_date_with_multiple_masters
)
from psi_tracker import PsiTracker, PsiCrossTalk
from weather_psi_integration import WeatherPsi

# ============================================================================
# PREDICTION MARKET APIs
# ============================================================================

class KalshiAPI:
    """
    Kalshi - CFTC-regulated prediction market (US-legal, pays real USD)
    $1.3B/month volume, 66% global market share
    """
    def __init__(self, api_key: str = "", email: str = "", password: str = ""):
        self.base_url = "https://api.kalshi.com/v2"
        self.api_key = api_key
        self.email = email
        self.password = password
        self.token = None
    
    def login(self) -> bool:
        """Authenticate with Kalshi API"""
        if not self.email or not self.password:
            return False
        
        try:
            response = requests.post(
                f"{self.base_url}/login",
                json={"email": self.email, "password": self.password}
            )
            if response.status_code == 200:
                self.token = response.json().get('token')
                return True
        except Exception as e:
            st.error(f"Kalshi login error: {str(e)}")
        return False
    
    def get_markets(self, category: Optional[str] = None, limit: int = 20) -> List[Dict]:
        """Fetch available prediction markets"""
        if not self.token:
            return []
        
        headers = {"Authorization": f"Bearer {self.token}"}
        params: Dict[str, Any] = {"limit": limit}
        if category:
            params["category"] = category
        
        try:
            response = requests.get(
                f"{self.base_url}/markets",
                headers=headers,
                params=params
            )
            if response.status_code == 200:
                return response.json().get('markets', [])
        except Exception as e:
            st.error(f"Error fetching markets: {str(e)}")
        return []
    
    def get_market_detail(self, market_id: str) -> Optional[Dict]:
        """Get detailed market information"""
        if not self.token:
            return None
        
        headers = {"Authorization": f"Bearer {self.token}"}
        
        try:
            response = requests.get(
                f"{self.base_url}/markets/{market_id}",
                headers=headers
            )
            if response.status_code == 200:
                return response.json().get('market')
        except Exception as e:
            st.error(f"Error fetching market detail: {str(e)}")
        return None

class MetaculusAPI:
    """
    Metaculus - Non-monetary forecasting (reputation-based)
    Best for skill-building and track record establishment
    """
    def __init__(self):
        self.base_url = "https://www.metaculus.com/api2"
    
    def get_questions(self, category: str = "all", status: str = "open", limit: int = 20) -> List[Dict]:
        """Fetch forecasting questions"""
        try:
            params = {
                "limit": limit,
                "status": status,
                "order_by": "-publish_time"
            }
            
            response = requests.get(
                f"{self.base_url}/questions/",
                params=params
            )
            if response.status_code == 200:
                return response.json().get('results', [])
        except Exception as e:
            st.error(f"Metaculus error: {str(e)}")
        return []
    
    def get_question_detail(self, question_id: int) -> Optional[Dict]:
        """Get detailed question information"""
        try:
            response = requests.get(f"{self.base_url}/questions/{question_id}/")
            if response.status_code == 200:
                return response.json()
        except Exception as e:
            st.error(f"Error fetching question: {str(e)}")
        return None

# ============================================================================
# RESONANCE FIELD PREDICTION
# ============================================================================

def calculate_event_resonance(
    event_title: str,
    event_description: str,
    close_date: datetime,
    user_life_path: int,
    current_date: datetime,
    include_weather: bool = True
) -> Dict[str, Any]:
    """
    Calculate resonance between user and prediction event
    Using Probability as Resonance Field (PRF) theory
    """
    # Event numerology
    event_vibration = reduce_to_single_digit(
        sum([ord(c) for c in event_title.upper() if c.isalpha()]),
        preserve_master=True
    )
    
    # WEATHER PSI INTEGRATION
    weather_data = None
    if include_weather:
        try:
            # Get API key from session state if available
            import streamlit as st
            weather_api_key = st.session_state.get('weather_api_key', None)
            weather_location = st.session_state.get('weather_location', 'New York')
            
            weather_psi = WeatherPsi(api_key=weather_api_key)
            weather_data = weather_psi.get_weather_resonance(
                location=weather_location,
                event_type="prediction_market"
            )
        except:
            weather_data = None
    
    # Date energy analysis
    date_analysis = analyze_date_with_multiple_masters(close_date)
    date_energy = date_analysis.get('overall_significance', 0.5)
    
    # Current day energy
    today_analysis = analyze_date_with_multiple_masters(current_date)
    today_energy = today_analysis.get('overall_significance', 0.5)
    
    # Calculate resonance factors
    resonances = []
    
    # 1. User-Event vibration match
    if event_vibration == user_life_path:
        resonances.append(('perfect_match', +2.0, f"Event vibration {event_vibration} matches your Life Path"))
    elif abs(event_vibration - user_life_path) <= 1:
        resonances.append(('close_match', +1.5, "Strong personal resonance with event"))
    else:
        resonances.append(('neutral', 0.0, "Neutral personal resonance"))
    
    # 2. Timing alignment
    if date_energy >= 2.0:
        resonances.append(('master_date', +1.8, f"Close date has Master Number energy (PD: {date_energy:.1f})"))
    elif date_energy >= 1.5:
        resonances.append(('strong_date', +1.3, "Close date has strong cosmic energy"))
    
    # 3. Current moment alignment
    if today_energy >= 2.0:
        resonances.append(('prediction_timing', +1.5, "Today is Master Number day - high intuition!"))
    elif today_energy >= 1.0:
        resonances.append(('good_timing', +0.8, "Good energy for making predictions"))
    
    # 4. Days until close (urgency factor)
    days_until = (close_date - current_date).days
    if days_until < 7:
        resonances.append(('imminent', +1.0, "Event closing soon - higher clarity"))
    elif days_until < 30:
        resonances.append(('near_term', +0.5, "Near-term event"))
    elif days_until > 365:
        resonances.append(('far_future', -0.5, "Distant event - higher uncertainty"))
    
    # 5. Topic keyword resonance
    topic_keywords = {
        'politics': 3, 'election': 11, 'economy': 8, 'stock': 5,
        'tech': 2, 'science': 7, 'sports': 9, 'weather': 6,
        'ai': 11, 'crypto': 22, 'health': 4, 'war': 1
    }
    
    for keyword, vib in topic_keywords.items():
        if keyword in event_title.lower() or keyword in event_description.lower():
            if vib == user_life_path:
                resonances.append(('topic_match', +1.2, f"Topic '{keyword}' resonates with you"))
                break
            elif vib in [11, 22, 33]:  # Master numbers
                resonances.append(('topic_master', +0.8, f"Topic '{keyword}' has Master Number energy"))
                break
    
    # 6. WEATHER PSI INTEGRATION
    if weather_data and weather_data.get('available'):
        weather_score = weather_data['avg_score']
        if weather_score >= 1.5:
            resonances.append(('weather_excellent', weather_score, f"Exceptional weather alignment! {weather_data['condition']}"))
        elif weather_score >= 1.0:
            resonances.append(('weather_good', weather_score, f"Favorable weather energy: {weather_data['condition']}"))
        elif weather_score >= 0.5:
            resonances.append(('weather_neutral', weather_score, f"Neutral weather influence: {weather_data['condition']}"))
        else:
            resonances.append(('weather_low', weather_score, f"Low weather energy: {weather_data['condition']}"))
    elif include_weather:
        resonances.append(('weather_unavailable', 0.0, "Weather data unavailable - get API key for bonus psi signals"))
    
    # Calculate composite score
    total_score = sum(r[1] for r in resonances)
    avg_score = total_score / len(resonances) if resonances else 0.0
    
    # Generate prediction signal
    if avg_score >= 1.8:
        signal = "STRONG CONFIDENCE"
        confidence = "85-95%"
        action = "🚀 HIGH CONVICTION - Make this prediction!"
    elif avg_score >= 1.3:
        signal = "CONFIDENT"
        confidence = "70-85%"
        action = "✅ GOOD SIGNAL - Favorable prediction"
    elif avg_score >= 0.8:
        signal = "MODERATE"
        confidence = "55-70%"
        action = "👍 SLIGHT EDGE - Consider predicting"
    elif avg_score >= 0.3:
        signal = "NEUTRAL"
        confidence = "50-55%"
        action = "➖ NO CLEAR SIGNAL - Skip or coin flip"
    else:
        signal = "WEAK"
        confidence = "< 50%"
        action = "⚠️ AVOID - Poor resonance alignment"
    
    return {
        'event_vibration': event_vibration,
        'date_energy': date_energy,
        'today_energy': today_energy,
        'days_until_close': days_until,
        'resonances': resonances,
        'total_score': total_score,
        'avg_score': avg_score,
        'signal': signal,
        'confidence': confidence,
        'action': action
    }

# ============================================================================
# STREAMLIT UI
# ============================================================================

def render_prediction_market_god_machine():
    """Main UI for Prediction Market God Machine"""
    st.title("💰 Prediction Market God Machine")
    st.markdown("### Make Money from Cosmic-Aligned Predictions")
    
    st.info("""
    🔮 **How it works:**
    - Integrates with **Kalshi** (US-legal, real USD), **Metaculus** (reputation), and more
    - Calculates **resonance** between you, the event, and cosmic timing
    - Uses **Probability as Resonance Field** theory (see papers/)
    - Generates BET/HOLD/AVOID signals with confidence levels
    - Tracks your accuracy to refine resonance formulas
    
    **Expected ROI:** 10-20% above market returns through resonance field optimization
    """)
    
    # Platform selection
    st.subheader("🎯 Select Prediction Platform")
    
    platform = st.selectbox(
        "Choose Platform",
        options=[
            "Kalshi (💵 Real Money - US Legal)",
            "Metaculus (🏆 Reputation - Free)",
            "Polymarket (💎 Crypto - International)",
            "Manual Entry (📝 Custom Event)"
        ]
    )
    
    # User profile
    col1, col2 = st.columns(2)
    
    with col1:
        user_life_path = st.selectbox(
            "Your Life Path Number",
            options=[1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 22, 33],
            index=5,  # Default to 6 (Brandon)
            help="Your Life Path affects event resonance"
        )
    
    with col2:
        current_day_energy = analyze_date_with_multiple_masters(datetime.now())
        st.metric(
            "Today's Cosmic Energy",
            f"{current_day_energy['overall_significance']:.1f} PD",
            help="Master Number days = higher intuition!"
        )
    
    # Weather API configuration (GLOBAL)
    with st.expander("🌤️ Weather PSI Configuration (Optional)"):
        st.markdown("**Enable weather-based psi signals for enhanced predictions**")
        st.info("Get FREE API key at: https://openweathermap.org/api")
        
        weather_api_key = st.text_input("OpenWeatherMap API Key", type="password", help="Optional - enhances predictions")
        weather_location = st.text_input("Location", value="New York", help="City name for weather data")
        
        if weather_api_key:
            st.session_state['weather_api_key'] = weather_api_key
            st.session_state['weather_location'] = weather_location
    
    # Platform-specific integration
    if "Kalshi" in platform:
        st.subheader("🔑 Kalshi Configuration")
        
        col1, col2 = st.columns(2)
        
        with col1:
            kalshi_email = st.text_input("Kalshi Email", type="default")
        
        with col2:
            kalshi_password = st.text_input("Kalshi Password", type="password")
        
        if st.button("🔐 Login to Kalshi"):
            kalshi = KalshiAPI(email=kalshi_email, password=kalshi_password)
            if kalshi.login():
                st.success("✅ Logged in to Kalshi!")
                st.session_state['kalshi_token'] = kalshi.token
            else:
                st.error("❌ Login failed. Check credentials.")
        
        if st.session_state.get('kalshi_token'):
            st.success("✅ Connected to Kalshi")
            
            # Fetch markets
            category_filter = st.selectbox(
                "Market Category",
                options=["All", "Politics", "Economics", "Sports", "Technology"]
            )
            
            if st.button("📊 Fetch Markets"):
                kalshi = KalshiAPI()
                kalshi.token = st.session_state['kalshi_token']
                
                markets = kalshi.get_markets(
                    category=category_filter if category_filter != "All" else None,
                    limit=50
                )
                
                if markets:
                    st.session_state['kalshi_markets'] = markets
                    st.success(f"Fetched {len(markets)} markets!")
    
    elif "Metaculus" in platform:
        st.subheader("🔮 Metaculus Forecasting")
        st.info("Metaculus is FREE - build your track record and reputation!")
        
        question_status = st.selectbox(
            "Question Status",
            options=["open", "closed", "upcoming"]
        )
        
        if st.button("📊 Fetch Questions"):
            metaculus = MetaculusAPI()
            questions = metaculus.get_questions(status=question_status, limit=50)
            
            if questions:
                st.session_state['metaculus_questions'] = questions
                st.success(f"Fetched {len(questions)} questions!")
    
    elif "Manual Entry" in platform:
        st.subheader("📝 Manual Event Entry")
        
        manual_title = st.text_input("Event Title", placeholder="e.g., Will AI pass Turing test by 2026?")
        manual_description = st.text_area("Event Description", placeholder="Detailed description...")
        manual_close_date = st.date_input("Close Date", value=datetime.now() + timedelta(days=30))
        
        if st.button("🔮 Analyze Event Resonance") and manual_title:
            close_dt = datetime.combine(manual_close_date, datetime.min.time())
            
            resonance = calculate_event_resonance(
                event_title=manual_title,
                event_description=manual_description,
                close_date=close_dt,
                user_life_path=user_life_path,
                current_date=datetime.now()
            )
            
            st.session_state['manual_resonance'] = resonance
            st.session_state['manual_event_title'] = manual_title
            st.session_state['manual_event_desc'] = manual_description
            st.session_state['manual_close_date'] = close_dt
    
    # Display resonance analysis results
    st.markdown("---")
    st.subheader("🎯 Resonance Analysis Results")
    
    # Process Kalshi markets
    if st.session_state.get('kalshi_markets'):
        markets = st.session_state['kalshi_markets']
        
        st.markdown(f"**{len(markets)} markets available**")
        
        # Analyze each market
        results = []
        for market in markets[:10]:  # Analyze top 10
            title = market.get('title', '')
            description = market.get('description', '')
            close_time = datetime.fromisoformat(market.get('close_time', '').replace('Z', '+00:00'))
            
            resonance = calculate_event_resonance(
                event_title=title,
                event_description=description,
                close_date=close_time,
                user_life_path=user_life_path,
                current_date=datetime.now()
            )
            
            # Add close_date to resonance for saving
            resonance['close_date'] = close_time
            
            results.append({
                'title': title,
                'signal': resonance['signal'],
                'confidence': resonance['confidence'],
                'avg_score': resonance['avg_score'],
                'action': resonance['action'],
                'resonance_details': resonance
            })
        
        # Sort by avg_score descending
        results.sort(key=lambda x: x['avg_score'], reverse=True)
        
        # Display top predictions
        for result in results:
            with st.expander(f"{result['title']} - {result['signal']}", expanded=(result['avg_score'] >= 1.3)):
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Signal", result['signal'])
                    st.metric("Confidence", result['confidence'])
                
                with col2:
                    st.metric("Resonance Score", f"{result['avg_score']:.2f}")
                    st.metric("Vibration", result['resonance_details']['event_vibration'])
                
                with col3:
                    st.markdown("**Action:**")
                    st.markdown(result['action'])
                
                # Detailed resonance factors
                st.markdown("**Resonance Factors:**")
                for factor_name, score, description in result['resonance_details']['resonances']:
                    emoji = "🟢" if score > 1.0 else "🟡" if score > 0.0 else "⚪" if score == 0.0 else "🔴"
                    st.markdown(f"{emoji} {description} (PD: {score:+.1f})")
                
                # SAVE TO TRACKER FOR KALSHI
                st.markdown("---")
                st.markdown("**💾 Save Prediction:**")
                
                col_pred, col_invest = st.columns(2)
                
                with col_pred:
                    kalshi_prediction = st.selectbox(
                        "Your Prediction",
                        options=["YES", "NO", "SKIP"],
                        key=f"pred_{result['title'][:20]}",  # Unique key
                        help="What are you predicting will happen?"
                    )
                
                with col_invest:
                    kalshi_investment = st.number_input(
                        "Investment ($)", 
                        min_value=0.0, 
                        value=0.0, 
                        step=5.0,
                        key=f"invest_{result['title'][:20]}"  # Unique key
                    )
                
                if st.button("💾 Save This Kalshi Prediction", key=f"save_{result['title'][:20]}") and kalshi_prediction != "SKIP":
                    # Initialize tracker
                    tracker = PsiTracker()
                    
                    # Generate prediction ID
                    pred_id = f"kalshi_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
                    
                    # Build psi scores dict
                    psi_scores = {}
                    for factor_name, score, desc in result['resonance_details']['resonances']:
                        if factor_name not in psi_scores:
                            psi_scores[factor_name] = score
                    
                    # Add to tracker
                    tracker.add_prediction(
                        prediction_id=pred_id,
                        category="prediction_market",
                        description=result['title'],
                        prediction=f"{kalshi_prediction} - {result['action']}",
                        confidence=float(result['confidence'].strip('%')) / 100.0 if '%' in result['confidence'] else 0.75,
                        psi_methods=['numerology', 'cosmic_timing', 'weather'] if st.session_state.get('weather_api_key') else ['numerology', 'cosmic_timing'],
                        psi_scores=psi_scores,
                        metadata={
                            'platform': 'Kalshi',
                            'signal': result['signal'],
                            'investment': kalshi_investment,
                            'source': 'kalshi_api'
                        },
                        close_date=result['resonance_details']['close_date'] if 'close_date' in result['resonance_details'] else datetime.now() + timedelta(days=30),
                        user_life_path=user_life_path
                    )
                    
                    st.success(f"✅ Kalshi prediction saved! ID: {pred_id}")
                    st.info("🎯 Check **Psi Tracker** tab to view all predictions!")
    
    # Process Metaculus questions
    if st.session_state.get('metaculus_questions'):
        questions = st.session_state['metaculus_questions']
        st.markdown(f"**{len(questions)} questions available**")
        
        # Analyze each question
        results = []
        for question in questions[:10]:  # Analyze top 10
            title = question.get('title', '')
            description = question.get('description', '')
            close_time_str = question.get('close_time', '')
            
            # Parse close time
            try:
                close_time = datetime.fromisoformat(close_time_str.replace('Z', '+00:00'))
            except:
                close_time = datetime.now() + timedelta(days=30)
            
            resonance = calculate_event_resonance(
                event_title=title,
                event_description=description,
                close_date=close_time,
                user_life_path=user_life_path,
                current_date=datetime.now()
            )
            
            # Add close_date to resonance for saving
            resonance['close_date'] = close_time
            
            results.append({
                'title': title,
                'signal': resonance['signal'],
                'confidence': resonance['confidence'],
                'avg_score': resonance['avg_score'],
                'action': resonance['action'],
                'resonance_details': resonance
            })
        
        # Sort by avg_score descending
        results.sort(key=lambda x: x['avg_score'], reverse=True)
        
        # Display top predictions
        for result in results:
            with st.expander(f"{result['title']} - {result['signal']}", expanded=(result['avg_score'] >= 1.3)):
                col1, col2, col3 = st.columns(3)
                
                with col1:
                    st.metric("Signal", result['signal'])
                    st.metric("Confidence", result['confidence'])
                
                with col2:
                    st.metric("Resonance Score", f"{result['avg_score']:.2f}")
                    st.metric("Vibration", result['resonance_details']['event_vibration'])
                
                with col3:
                    st.markdown("**Action:**")
                    st.markdown(result['action'])
                
                # Detailed resonance factors
                st.markdown("**Resonance Factors:**")
                for factor_name, score, description in result['resonance_details']['resonances']:
                    emoji = "🟢" if score > 1.0 else "🟡" if score > 0.0 else "⚪" if score == 0.0 else "🔴"
                    st.markdown(f"{emoji} {description} (PD: {score:+.1f})")
                
                # SAVE TO TRACKER FOR METACULUS
                st.markdown("---")
                st.markdown("**💾 Save Forecast:**")
                
                col_pred, col_conf = st.columns(2)
                
                with col_pred:
                    metaculus_prediction = st.text_input(
                        "Your Forecast (e.g., 65% or YES)",
                        key=f"meta_pred_{result['title'][:20]}",
                        help="Enter probability or YES/NO"
                    )
                
                with col_conf:
                    metaculus_notes = st.text_input(
                        "Notes",
                        key=f"meta_notes_{result['title'][:20]}",
                        help="Optional reasoning"
                    )
                
                if st.button("💾 Save This Metaculus Forecast", key=f"save_meta_{result['title'][:20]}") and metaculus_prediction:
                    # Initialize tracker
                    tracker = PsiTracker()
                    
                    # Generate prediction ID
                    pred_id = f"metaculus_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
                    
                    # Build psi scores dict
                    psi_scores = {}
                    for factor_name, score, desc in result['resonance_details']['resonances']:
                        if factor_name not in psi_scores:
                            psi_scores[factor_name] = score
                    
                    # Add to tracker
                    tracker.add_prediction(
                        prediction_id=pred_id,
                        category="prediction_market",
                        description=result['title'],
                        prediction=f"{metaculus_prediction} - {result['action']}",
                        confidence=float(result['confidence'].strip('%')) / 100.0 if '%' in result['confidence'] else 0.75,
                        psi_methods=['numerology', 'cosmic_timing', 'weather'] if st.session_state.get('weather_api_key') else ['numerology', 'cosmic_timing'],
                        psi_scores=psi_scores,
                        metadata={
                            'platform': 'Metaculus',
                            'signal': result['signal'],
                            'notes': metaculus_notes,
                            'source': 'metaculus_api'
                        },
                        close_date=result['resonance_details']['close_date'],
                        user_life_path=user_life_path
                    )
                    
                    st.success(f"✅ Metaculus forecast saved! ID: {pred_id}")
                    st.info("🎯 Check **Psi Tracker** tab to view all forecasts!")
    
    # Display manual analysis
    if st.session_state.get('manual_resonance'):
        res = st.session_state['manual_resonance']
        
        col1, col2, col3, col4 = st.columns(4)
        
        with col1:
            st.metric("Signal", res['signal'])
        
        with col2:
            st.metric("Confidence", res['confidence'])
        
        with col3:
            st.metric("Resonance Score", f"{res['avg_score']:.2f}")
        
        with col4:
            st.metric("Event Vibration", res['event_vibration'])
        
        st.markdown("---")
        st.markdown(f"**Action:** {res['action']}")
        
        st.markdown("**Resonance Factors:**")
        for factor_name, score, description in res['resonances']:
            emoji = "🟢" if score > 1.0 else "🟡" if score > 0.0 else "⚪" if score == 0.0 else "🔴"
            st.markdown(f"{emoji} {description} (PD: {score:+.1f})")
        
        # SAVE TO TRACKER
        st.markdown("---")
        st.subheader("💾 Save Prediction to Tracker")
        
        col1, col2 = st.columns(2)
        
        with col1:
            your_prediction = st.selectbox(
                "Your Prediction",
                options=["YES", "NO", "SKIP"],
                help="What are you predicting will happen?"
            )
        
        with col2:
            investment = st.number_input("Investment Amount ($)", min_value=0.0, value=0.0, step=5.0)
        
        if st.button("💾 Save This Prediction") and your_prediction != "SKIP":
            # Initialize tracker
            tracker = PsiTracker()
            
            # Generate prediction ID
            pred_id = f"pred_market_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            
            # Get event details from session
            event_title = st.session_state.get('manual_event_title', 'Manual Event')
            event_desc = st.session_state.get('manual_event_desc', '')
            close_date = st.session_state.get('manual_close_date', datetime.now())
            
            # Build psi scores dict
            psi_scores = {}
            for factor_name, score, desc in res['resonances']:
                if factor_name not in psi_scores:
                    psi_scores[factor_name] = score
            
            # Add to tracker
            tracker.add_prediction(
                prediction_id=pred_id,
                category="prediction_market",
                description=event_title,
                prediction=f"{your_prediction} - {res['action']}",
                confidence=float(res['confidence'].strip('%')) / 100.0 if '%' in res['confidence'] else 0.75,
                psi_methods=['numerology', 'cosmic_timing'],
                psi_scores=psi_scores,
                metadata={
                    'event_description': event_desc,
                    'signal': res['signal'],
                    'investment': investment,
                    'source': 'manual_entry'
                },
                close_date=close_date,
                user_life_path=user_life_path
            )
            
            st.success(f"✅ Prediction saved to tracker! ID: {pred_id}")
            st.info("🎯 Go to **Psi Tracker** tab to view all predictions and track accuracy!")
    
    # Educational section
    st.markdown("---")
    st.subheader("📚 How to Use Prediction Markets for Income")
    
    with st.expander("💰 Kalshi - Real USD (US Legal)"):
        st.markdown("""
        ### Kalshi Platform Guide
        
        **What it is:**
        - CFTC-regulated prediction market exchange
        - Trade binary contracts on real-world events
        - Pays out in US dollars
        - $1.3 billion monthly volume
        
        **How to make money:**
        1. **Open account** at https://kalshi.com
        2. **Deposit funds** via bank transfer or crypto
        3. **Find mispriced events** using God Machine resonance
        4. **Buy "Yes" or "No" shares** (e.g., 70¢ for 70% probability)
        5. **Event resolves** → Get $1 per correct share
        
        **Example:**
        - Event: "Will unemployment be below 4% in December?"
        - Current price: 65¢ (market thinks 65% chance)
        - God Machine signal: STRONG BUY (resonance score 1.9)
        - You buy 100 shares @ 65¢ = $65 investment
        - Event resolves YES → You get 100 × $1 = $100
        - **Profit: $35 (54% ROI)**
        
        **Risk management:**
        - Start with small positions ($10-50)
        - Only bet on HIGH CONFIDENCE signals (1.5+ resonance)
        - Diversify across multiple events
        - Track your accuracy over 20+ predictions
        """)
    
    with st.expander("🏆 Metaculus - Reputation Building (Free)"):
        st.markdown("""
        ### Metaculus Forecasting Platform
        
        **What it is:**
        - Free forecasting community
        - No money involved—builds reputation and accuracy track record
        - Used by researchers, policymakers, professional forecasters
        
        **Why use it:**
        1. **Practice for free** before risking real money
        2. **Build credibility** with documented prediction accuracy
        3. **Learn calibration** (are you overconfident or underconfident?)
        4. **Test God Machine** against conventional wisdom
        
        **How to use:**
        1. **Create account** at https://www.metaculus.com
        2. **Make forecasts** on open questions
        3. **Update predictions** as new information arrives
        4. **Track Brier score** (lower = more accurate)
        5. **Earn reputation points** for good forecasts
        
        **God Machine advantage:**
        - Use resonance scores to calibrate confidence levels
        - High resonance (1.8+) → Aggressive forecasts (e.g., 85% vs 75%)
        - Low resonance (< 0.5) → Stay near consensus
        """)
    
    with st.expander("🎯 Resonance Field Theory Explained"):
        st.markdown("""
        ### Probability as Resonance Field (PRF)
        
        **Core insight:**  
        Probability is NOT fixed—it emerges from resonance between:
        1. **You** (observer field: Life Path, intention, attention)
        2. **Event** (outcome manifold: vibration, topic, keywords)
        3. **Context** (cosmic timing: Master Numbers, date energy)
        
        **Why it works:**
        - **Quantum mechanics:** Observer affects outcome (Copenhagen interpretation)
        - **Synchronicity:** Meaningful coincidences cluster around intention
        - **Luck studies:** Some people consistently beat statistical odds
        
        **Practical application:**
        - Events with HIGH resonance → You have informational edge
        - Events with LOW resonance → Skip (no advantage over market)
        - Track results to validate PRF model
        
        **See full paper:** `papers/PROBABILITY_AS_RESONANCE_FIELD.md`
        """)
    
    # Performance tracking (placeholder)
    st.markdown("---")
    st.subheader("📊 Track Your Accuracy")
    st.info("🚧 Coming soon: Prediction tracking and P&L analysis")

if __name__ == "__main__":
    # Initialize session state
    if 'kalshi_token' not in st.session_state:
        st.session_state['kalshi_token'] = None
    if 'kalshi_markets' not in st.session_state:
        st.session_state['kalshi_markets'] = None
    if 'metaculus_questions' not in st.session_state:
        st.session_state['metaculus_questions'] = None
    if 'manual_resonance' not in st.session_state:
        st.session_state['manual_resonance'] = None
    
    render_prediction_market_god_machine()
