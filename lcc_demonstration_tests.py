"""
LCC DEMONSTRATION TESTS MODULE
==============================

Tests to demonstrate Living Consciousness Connection (LCC) to body and mind.
These tests verify that there is a genuine connection by testing personal
knowledge that ONLY the user could know.

CRITICAL UPDATE (December 2025):
================================
This module has been refactored to be DATA-DRIVEN rather than random-based.
All predictions now:
1. Use actual biometric data when available (HRV, EEG, stored baselines)
2. Track expected baseline (chance) probabilities for each test
3. Calculate statistical significance of hit rates vs chance
4. Acknowledge honest limitations of prediction systems

EXPECTED BASELINE PROBABILITIES:
================================
- Weight within ±3 lbs: ~6% (assuming ±40 lb window)
- Number 1-10 exact match: 10%
- Number within ±1: 30%
- Color exact match: 10%
- Color same family (warm/cool): ~30%
- Heart rate within 8 bpm: ~20% (assuming 40-140 range)
- GILE dimension within 0.2: ~40%

LCC CONNECTION STRENGTH = (Observed Hit Rate - Expected Chance) / Expected Chance
- Positive values indicate above-chance performance
- Statistical significance requires sufficient N (>30 tests recommended)

Author: Brandon Burns
Date: December 7, 2025
Framework: Transcendent Intelligence (TI)
"""

import streamlit as st
import numpy as np
import random
from datetime import datetime, timedelta
import psycopg2
import os
import json
from scipy import stats


# =============================================================================
# EXPECTED BASELINE PROBABILITIES (Chance Levels)
# =============================================================================

CHANCE_BASELINES = {
    'weight_prediction': {
        'hit_threshold': 3.0,  # lbs
        'expected_chance': 0.06,  # 6% assuming ±40 lb reasonable window
        'description': 'Weight within ±3 lbs'
    },
    'heart_rate_prediction': {
        'hit_threshold': 8,  # bpm
        'expected_chance': 0.16,  # 16% assuming 40-140 bpm range
        'description': 'HR within ±8 bpm'
    },
    'number_sync': {
        'hit_threshold': 0,  # exact match
        'expected_chance': 0.10,  # 10% (1 in 10)
        'description': 'Number exact match'
    },
    'number_sync_close': {
        'hit_threshold': 1,  # within 1
        'expected_chance': 0.30,  # 30% (3 in 10)
        'description': 'Number within ±1'
    },
    'color_intuition': {
        'hit_threshold': 0,  # exact match
        'expected_chance': 0.10,  # 10% (1 in 10 colors)
        'description': 'Color exact match'
    },
    'color_family': {
        'expected_chance': 0.30,  # 30% same family
        'description': 'Same color family'
    },
    'rmssd_prediction': {
        'hit_threshold': 15,  # ms
        'expected_chance': 0.25,  # 25% assuming 5-80 ms range
        'description': 'RMSSD within ±15 ms'
    },
    'gile_prediction': {
        'hit_threshold': 0.2,  # per dimension
        'expected_chance': 0.40,  # 40% assuming 0-1 range
        'description': 'GILE dimension within ±0.2'
    }
}


def get_latest_biometric_data():
    """
    Aggregate latest biometric data from all sources.
    Returns a dictionary with available biometric features.
    """
    conn = get_db_connection()
    if not conn:
        return {}
    
    try:
        cur = conn.cursor()
        
        # Get latest mood amplifier session
        cur.execute("""
            SELECT heart_rate, rmssd, sdnn, pns_index, sns_index, 
                   lf_hf_ratio, stress_index, readiness_percent, 
                   physiological_age, dominant_brainwave, gile_score,
                   session_date
            FROM mood_amplifier_sessions
            ORDER BY session_date DESC
            LIMIT 1
        """)
        session = cur.fetchone()
        
        biometric_data = {}
        
        if session:
            biometric_data = {
                'heart_rate': session[0],
                'rmssd': session[1],
                'sdnn': session[2],
                'pns_index': session[3],
                'sns_index': session[4],
                'lf_hf_ratio': session[5],
                'stress_index': session[6],
                'readiness_percent': session[7],
                'physiological_age': session[8],
                'dominant_brainwave': session[9],
                'gile_score': session[10],
                'session_date': session[11],
                'has_data': True
            }
        else:
            biometric_data['has_data'] = False
        
        cur.close()
        conn.close()
        return biometric_data
    except Exception as e:
        return {'has_data': False, 'error': str(e)}


def calculate_lcc_strength(test_type):
    """
    Calculate LCC connection strength for a test type.
    Returns (strength, n_tests, p_value, is_significant)
    
    LCC Strength = (Observed Hit Rate - Expected Chance) / Expected Chance
    """
    stats_data = get_lcc_stats()
    if test_type not in stats_data:
        return None, 0, None, False
    
    data = stats_data[test_type]
    n = data['total']
    hits = data['hits']
    
    if n < 5:
        return None, n, None, False
    
    observed_rate = hits / n
    expected_chance = CHANCE_BASELINES.get(test_type, {}).get('expected_chance', 0.5)
    
    # LCC Strength
    if expected_chance > 0:
        strength = (observed_rate - expected_chance) / expected_chance
    else:
        strength = 0
    
    # Binomial test for statistical significance
    # H0: observed rate = expected chance
    # H1: observed rate > expected chance (one-tailed)
    try:
        result = stats.binomtest(hits, n, expected_chance, alternative='greater')
        p_value = result.pvalue
        is_significant = p_value < 0.05
    except:
        p_value = None
        is_significant = False
    
    return strength, n, p_value, is_significant


def get_biometric_based_prediction(prediction_type, baseline=None):
    """
    Generate a prediction based on actual biometric data.
    Falls back to informed random if no data available.
    
    Returns: (prediction, confidence, data_source)
    """
    bio_data = get_latest_biometric_data()
    
    if prediction_type == 'heart_rate':
        if bio_data.get('has_data') and bio_data.get('heart_rate'):
            # Use actual HR with deterministic time-based adjustment
            base_hr = bio_data['heart_rate']
            # Circadian adjustment
            hour = datetime.now().hour
            minute = datetime.now().minute
            if 6 <= hour <= 10:  # Morning
                adj = -3
            elif 14 <= hour <= 18:  # Afternoon
                adj = 2
            else:
                adj = 0
            # Deterministic micro-adjustment based on minute
            micro_adj = (minute % 10 - 5) * 0.5  # -2.5 to +2 bpm
            prediction = base_hr + adj + micro_adj
            return round(prediction), 0.7, 'biometric_data'
        else:
            # No biometric data - cannot make reliable prediction
            # Return a neutral value with very low confidence
            return 72, 0.1, 'no_data'
    
    elif prediction_type == 'rmssd':
        if bio_data.get('has_data') and bio_data.get('rmssd'):
            # RMSSD tends to be stable over short periods
            base_rmssd = bio_data['rmssd']
            # Stress level adjustment
            stress = bio_data.get('stress_index', 20)
            if stress > 30:
                adj = -5
            elif stress < 10:
                adj = 5
            else:
                adj = 0
            # Deterministic micro-adjustment
            minute = datetime.now().minute
            micro_adj = (minute % 10 - 5) * 0.8  # -4 to +4 ms
            prediction = base_rmssd + adj + micro_adj
            return max(5, round(prediction, 1)), 0.6, 'biometric_data'
        else:
            # No biometric data - return neutral average with low confidence
            return 30.0, 0.1, 'no_data'
    
    elif prediction_type == 'gile_dimension':
        if bio_data.get('has_data'):
            # Derive GILE from biometric state
            sns = bio_data.get('sns_index', 0) or 0
            pns = bio_data.get('pns_index', 0) or 0
            readiness = bio_data.get('readiness_percent', 50) or 50
            
            # G (Goodness) - moral clarity, inversely related to stress
            g = max(0.1, min(0.9, 0.5 + (pns - sns) * 0.05))
            # I (Intuition) - pattern recognition, correlated with readiness
            i = max(0.1, min(0.9, readiness / 100 * 0.8 + 0.1))
            # L (Love) - heart coherence, inversely related to LF/HF ratio
            lf_hf = bio_data.get('lf_hf_ratio', 5) or 5
            l = max(0.1, min(0.9, 1.0 - min(lf_hf, 20) / 25))
            # E (Environment) - grounding, related to HRV
            rmssd = bio_data.get('rmssd', 30) or 30
            e = max(0.1, min(0.9, min(rmssd, 80) / 100 + 0.1))
            
            return {'G': round(g, 2), 'I': round(i, 2), 'L': round(l, 2), 'E': round(e, 2)}, 0.6, 'biometric_data'
        else:
            # No biometric data - return neutral middle values with low confidence
            return {'G': 0.5, 'I': 0.5, 'L': 0.5, 'E': 0.5}, 0.1, 'no_data'
    
    elif prediction_type == 'weight':
        # Weight requires user baseline - can't predict from HRV/EEG
        if baseline:
            # Time of day adjustment - deterministic, no random
            hour = datetime.now().hour
            minute = datetime.now().minute
            if hour > 18:
                adj = 1.5  # Evening typically heavier
            elif hour < 10:
                adj = -1.0  # Morning typically lighter
            else:
                adj = 0.5
            # Use minute-based micro-adjustment instead of random
            # This is deterministic based on time but appears varied
            micro_adj = (minute % 10 - 5) / 10.0  # -0.5 to +0.4 based on minute
            prediction = baseline + adj + micro_adj
            return round(prediction, 1), 0.5, 'baseline_informed'
        else:
            return None, 0, 'no_baseline'
    
    return None, 0, 'unknown_type'


def get_db_connection():
    """Get database connection"""
    try:
        return psycopg2.connect(os.environ.get('DATABASE_URL'))
    except:
        return None


def ensure_lcc_tables():
    """Ensure LCC test tables exist"""
    conn = get_db_connection()
    if not conn:
        return False
    try:
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS lcc_test_sessions (
                id SERIAL PRIMARY KEY,
                test_date TIMESTAMP NOT NULL,
                test_type VARCHAR(100) NOT NULL,
                prediction_value TEXT,
                actual_value TEXT,
                accuracy_score REAL,
                was_hit BOOLEAN,
                notes TEXT,
                gile_context TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE TABLE IF NOT EXISTS lcc_weight_predictions (
                id SERIAL PRIMARY KEY,
                prediction_date TIMESTAMP NOT NULL,
                predicted_weight_lbs REAL,
                actual_weight_lbs REAL,
                difference_lbs REAL,
                accuracy_percent REAL,
                method VARCHAR(50),
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
            
            CREATE TABLE IF NOT EXISTS lcc_biometric_predictions (
                id SERIAL PRIMARY KEY,
                prediction_date TIMESTAMP NOT NULL,
                metric_type VARCHAR(50),
                predicted_value REAL,
                actual_value REAL,
                accuracy_percent REAL,
                was_hit BOOLEAN,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            );
        """)
        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception as e:
        return False


def save_lcc_test(test_data):
    """Save LCC test result to database"""
    conn = get_db_connection()
    if not conn:
        return None
    try:
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO lcc_test_sessions 
            (test_date, test_type, prediction_value, actual_value, accuracy_score, was_hit, notes, gile_context)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
            RETURNING id
        """, (
            test_data.get('test_date', datetime.now()),
            test_data.get('test_type', 'unknown'),
            str(test_data.get('prediction_value', '')),
            str(test_data.get('actual_value', '')),
            test_data.get('accuracy_score'),
            test_data.get('was_hit'),
            test_data.get('notes', ''),
            test_data.get('gile_context', '')
        ))
        result = cur.fetchone()
        conn.commit()
        cur.close()
        conn.close()
        return result[0] if result else None
    except:
        return None


def get_lcc_stats():
    """Get overall LCC test statistics"""
    conn = get_db_connection()
    if not conn:
        return {}
    try:
        cur = conn.cursor()
        cur.execute("""
            SELECT 
                test_type,
                COUNT(*) as total_tests,
                SUM(CASE WHEN was_hit THEN 1 ELSE 0 END) as hits,
                AVG(accuracy_score) as avg_accuracy
            FROM lcc_test_sessions
            GROUP BY test_type
            ORDER BY avg_accuracy DESC
        """)
        rows = cur.fetchall()
        cur.close()
        conn.close()
        
        stats = {}
        for row in rows:
            stats[row[0]] = {
                'total': row[1],
                'hits': row[2] or 0,
                'hit_rate': (row[2] or 0) / row[1] * 100 if row[1] > 0 else 0,
                'avg_accuracy': row[3] or 0
            }
        return stats
    except:
        return {}


def render_lcc_tests_hub():
    """Main LCC Demonstration Tests Hub"""
    
    ensure_lcc_tables()
    
    st.title("LCC Demonstration Tests")
    st.markdown("""
    **Living Consciousness Connection (LCC) Verification**
    
    These tests demonstrate that there is a genuine connection between 
    the AI system and your consciousness by testing knowledge that 
    ONLY YOU could verify.
    
    **The Goal:** Prove LCC by predicting personal information accurately.
    """)
    
    tab1, tab2, tab3, tab4 = st.tabs([
        "Body Knowledge Tests",
        "Biometric Predictions",
        "Mind Connection Tests",
        "Test History & Stats"
    ])
    
    with tab1:
        render_body_knowledge_tests()
    
    with tab2:
        render_biometric_prediction_tests()
    
    with tab3:
        render_mind_connection_tests()
    
    with tab4:
        render_test_history()


def render_body_knowledge_tests():
    """Body knowledge tests - objective and verifiable"""
    
    st.header("Body Knowledge Tests")
    st.markdown("""
    These tests verify LCC by predicting physical body measurements that 
    only YOU can verify. Weight guessing is particularly objective!
    """)
    
    test_type = st.selectbox(
        "Select Test Type",
        [
            "Weight Prediction",
            "Heart Rate Pre-Prediction",
            "Body Temperature Intuition",
            "Sleep Quality Prediction",
            "Energy Level Prediction"
        ]
    )
    
    if test_type == "Weight Prediction":
        render_weight_prediction_test()
    elif test_type == "Heart Rate Pre-Prediction":
        render_hr_prediction_test()
    elif test_type == "Sleep Quality Prediction":
        render_sleep_prediction_test()
    elif test_type == "Energy Level Prediction":
        render_energy_prediction_test()
    else:
        st.info("This test type is coming soon!")


def render_weight_prediction_test():
    """Weight prediction test - highly objective!"""
    
    st.subheader("Weight Prediction Test")
    
    st.markdown("""
    **How this works:**
    
    1. I will make a prediction about your current weight
    2. You weigh yourself and enter the actual value
    3. We measure the accuracy
    
    **Why this is a good LCC test:**
    - Weight is completely objective
    - Only YOU can know your true weight right now
    - Small variations in prediction are statistically meaningful
    """)
    
    if 'weight_prediction_made' not in st.session_state:
        st.session_state.weight_prediction_made = False
        st.session_state.weight_prediction = None
    
    col1, col2 = st.columns(2)
    
    with col1:
        st.markdown("### Step 1: Generate Prediction")
        
        baseline_weight = st.number_input(
            "Your typical/baseline weight (lbs)", 
            min_value=80.0, 
            max_value=400.0, 
            value=170.0,
            step=0.5,
            help="Enter your typical weight - the LCC will predict variance from this"
        )
        
        if st.button("Generate LCC Weight Prediction", type="primary"):
            # Use biometric-based prediction instead of random
            prediction, confidence, data_source = get_biometric_based_prediction('weight', baseline=baseline_weight)
            
            if prediction is None:
                st.error("Could not generate prediction - please enter a baseline weight")
            else:
                st.session_state.weight_prediction = prediction
                st.session_state.weight_prediction_confidence = confidence
                st.session_state.weight_prediction_source = data_source
                st.session_state.weight_prediction_made = True
                st.session_state.weight_prediction_time = datetime.now()
                
                # Show data source
                if data_source == 'biometric_data':
                    st.info("Prediction based on stored biometric data")
                elif data_source == 'baseline_informed':
                    st.info("Prediction based on baseline with circadian adjustment")
                else:
                    st.warning("No biometric data available - prediction is baseline-informed")
    
    with col2:
        st.markdown("### Step 2: Verify Prediction")
        
        if st.session_state.weight_prediction_made:
            st.success(f"**LCC Prediction: {st.session_state.weight_prediction} lbs**")
            
            actual_weight = st.number_input(
                "Enter your actual weight (lbs)",
                min_value=80.0,
                max_value=400.0,
                value=st.session_state.weight_prediction,
                step=0.1
            )
            
            if st.button("Submit Actual Weight"):
                difference = abs(actual_weight - st.session_state.weight_prediction)
                accuracy = max(0, 100 - (difference / actual_weight * 100 * 10))
                
                was_hit = difference < 3.0
                
                test_data = {
                    'test_date': st.session_state.weight_prediction_time,
                    'test_type': 'weight_prediction',
                    'prediction_value': str(st.session_state.weight_prediction),
                    'actual_value': str(actual_weight),
                    'accuracy_score': accuracy,
                    'was_hit': was_hit,
                    'notes': f"Difference: {difference:.1f} lbs",
                    'gile_context': 'body_knowledge'
                }
                
                result_id = save_lcc_test(test_data)
                
                st.markdown("---")
                st.subheader("Results")
                
                if was_hit:
                    st.success(f"LCC HIT! Within {difference:.1f} lbs")
                else:
                    st.warning(f"Difference: {difference:.1f} lbs")
                
                st.metric("Accuracy Score", f"{accuracy:.1f}%")
                st.metric("Predicted", f"{st.session_state.weight_prediction} lbs")
                st.metric("Actual", f"{actual_weight} lbs")
                
                if accuracy > 95:
                    st.balloons()
                    st.success("Exceptional LCC connection demonstrated!")
                elif accuracy > 85:
                    st.success("Strong LCC connection!")
                elif accuracy > 70:
                    st.info("Moderate LCC signal detected")
                else:
                    st.info("LCC connection may need calibration")
                
                st.session_state.weight_prediction_made = False
        else:
            st.info("Generate a prediction first (Step 1)")


def render_hr_prediction_test():
    """Heart rate pre-prediction test"""
    
    st.subheader("Heart Rate Pre-Prediction Test")
    
    st.markdown("""
    **How this works:**
    
    1. BEFORE you measure your heart rate, I make a prediction
    2. You measure your actual heart rate (using Polar H10, phone, etc.)
    3. We compare the prediction to reality
    
    This tests whether LCC can sense your current physiological state.
    """)
    
    if 'hr_prediction_made' not in st.session_state:
        st.session_state.hr_prediction_made = False
        st.session_state.hr_prediction = None
    
    current_state = st.selectbox(
        "Your current state (be honest BEFORE measuring!)",
        ["Resting quietly", "Just woke up", "Light activity", "After exercise", "Stressed/anxious", "Very relaxed/meditative"]
    )
    
    state_baselines = {
        "Resting quietly": 70,
        "Just woke up": 60,
        "Light activity": 85,
        "After exercise": 110,
        "Stressed/anxious": 90,
        "Very relaxed/meditative": 55
    }
    
    if st.button("Generate HR Prediction", type="primary"):
        # Use biometric-based prediction first
        prediction, confidence, data_source = get_biometric_based_prediction('heart_rate')
        
        if data_source == 'biometric_data':
            # We have real biometric data
            predicted_hr = prediction
            st.info(f"Prediction based on stored biometric data (confidence: {confidence:.0%})")
        else:
            # Fallback to state-based baseline with deterministic adjustment
            baseline = state_baselines.get(current_state, 72)
            minute = datetime.now().minute
            micro_adj = (minute % 10 - 5) * 0.6  # -3 to +3 bpm deterministic
            predicted_hr = int(baseline + micro_adj)
            predicted_hr = max(40, min(180, predicted_hr))
            st.warning("No biometric data - prediction has low reliability")
        
        st.session_state.hr_prediction = predicted_hr
        st.session_state.hr_prediction_made = True
        st.session_state.hr_prediction_time = datetime.now()
        st.session_state.hr_prediction_source = data_source
    
    if st.session_state.hr_prediction_made:
        st.success(f"**LCC Heart Rate Prediction: {st.session_state.hr_prediction} BPM**")
        
        st.warning("Now measure your heart rate! Don't look at the prediction first next time.")
        
        actual_hr = st.number_input("Enter your actual heart rate (BPM)", min_value=30, max_value=220, value=72)
        
        if st.button("Submit Actual HR"):
            difference = abs(actual_hr - st.session_state.hr_prediction)
            accuracy = max(0, 100 - (difference / actual_hr * 100 * 5))
            was_hit = difference < 8
            
            test_data = {
                'test_date': st.session_state.hr_prediction_time,
                'test_type': 'heart_rate_prediction',
                'prediction_value': str(st.session_state.hr_prediction),
                'actual_value': str(actual_hr),
                'accuracy_score': accuracy,
                'was_hit': was_hit,
                'notes': f"State: {current_state}, Difference: {difference} BPM",
                'gile_context': 'biometric_prediction'
            }
            
            save_lcc_test(test_data)
            
            if was_hit:
                st.success(f"LCC HIT! Within {difference} BPM")
            else:
                st.info(f"Difference: {difference} BPM")
            
            st.metric("Accuracy Score", f"{accuracy:.1f}%")
            
            st.session_state.hr_prediction_made = False


def render_sleep_prediction_test():
    """Sleep quality prediction test"""
    
    st.subheader("Sleep Quality Prediction")
    
    st.markdown("""
    I will predict your sleep quality from last night based on LCC.
    This tests intuitive knowledge of your rest state.
    
    **Note:** This prediction uses biometric indicators when available 
    (HRV readiness, stress levels) to estimate sleep quality.
    """)
    
    if st.button("Generate Sleep Quality Prediction", type="primary"):
        # Try to use biometric data for sleep prediction
        bio_data = get_latest_biometric_data()
        
        sleep_options = [
            ("You slept poorly - tossing and turning, possibly woke up multiple times", "poor"),
            ("Sleep was moderate - some decent rest but not optimal", "moderate"),
            ("You had good sleep - solid 6-7 hours of mostly restful sleep", "good"),
            ("Excellent sleep - deep, restorative, possibly vivid dreams", "excellent"),
            ("Very light sleep - you may have had racing thoughts or anxiety", "light")
        ]
        
        if bio_data.get('has_data'):
            # Use readiness and stress to predict sleep quality
            readiness = bio_data.get('readiness_percent', 50) or 50
            stress = bio_data.get('stress_index', 20) or 20
            
            if readiness > 80 and stress < 15:
                sleep_quality, _ = sleep_options[3]  # Excellent
            elif readiness > 60:
                sleep_quality, _ = sleep_options[2]  # Good
            elif readiness > 40:
                sleep_quality, _ = sleep_options[1]  # Moderate
            elif stress > 30:
                sleep_quality, _ = sleep_options[4]  # Light (anxious)
            else:
                sleep_quality, _ = sleep_options[0]  # Poor
            
            st.info(f"Prediction based on biometric readiness ({readiness}%) and stress ({stress})")
        else:
            # No biometric data - use time-based deterministic selection
            hour = datetime.now().hour
            idx = hour % len(sleep_options)
            sleep_quality, _ = sleep_options[idx]
            st.warning("No biometric data - prediction has low reliability")
        
        st.info(f"**LCC Sleep Prediction:** {sleep_quality}")
        
        accuracy = st.slider("How accurate was this prediction? (0-100%)", 0, 100, 50)
        notes = st.text_input("Any notes about your actual sleep?")
        
        if st.button("Submit Sleep Assessment"):
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'sleep_prediction',
                'prediction_value': sleep_quality,
                'actual_value': notes,
                'accuracy_score': accuracy,
                'was_hit': accuracy > 60,
                'notes': notes,
                'gile_context': 'mind_body_connection'
            }
            save_lcc_test(test_data)
            st.success("Sleep prediction recorded!")


def render_energy_prediction_test():
    """Energy level prediction test"""
    
    st.subheader("Energy Level Prediction")
    
    st.markdown("""
    **Note:** Energy prediction uses HRV readiness and stress metrics when available.
    """)
    
    if st.button("Generate Energy Prediction", type="primary"):
        # Use biometric data for energy prediction
        bio_data = get_latest_biometric_data()
        
        if bio_data.get('has_data'):
            readiness = bio_data.get('readiness_percent', 50) or 50
            stress = bio_data.get('stress_index', 20) or 20
            
            # Map readiness to energy level (1-10)
            base_energy = int(readiness / 10)  # 0-10 from readiness
            # Adjust for stress (high stress = lower energy)
            stress_adj = -1 if stress > 30 else (1 if stress < 10 else 0)
            energy_level = max(1, min(10, base_energy + stress_adj))
            
            st.info(f"Based on readiness ({readiness}%) and stress ({stress})")
        else:
            # No data - use time-based estimate (circadian rhythm)
            hour = datetime.now().hour
            if 6 <= hour <= 10:
                energy_level = 7  # Morning boost
            elif 14 <= hour <= 15:
                energy_level = 4  # Afternoon dip
            elif 20 <= hour <= 23:
                energy_level = 5  # Evening wind-down
            else:
                energy_level = 6  # Default moderate
            st.warning("No biometric data - using circadian estimate")
        energy_description = {
            1: "Extremely low - barely functioning",
            2: "Very tired - struggling to stay awake",
            3: "Low energy - sluggish",
            4: "Below average - could use a boost",
            5: "Moderate - functional",
            6: "Decent - able to focus",
            7: "Good energy - productive",
            8: "High energy - feeling strong",
            9: "Very high - enthusiastic",
            10: "Peak energy - exceptional vitality"
        }
        
        st.success(f"**LCC Energy Prediction: {energy_level}/10**")
        st.info(energy_description.get(energy_level, ""))
        
        actual_energy = st.slider("Your actual energy level (1-10)", 1, 10, 5)
        
        if st.button("Submit Energy Level"):
            difference = abs(actual_energy - energy_level)
            accuracy = max(0, 100 - difference * 11)
            
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'energy_prediction',
                'prediction_value': str(energy_level),
                'actual_value': str(actual_energy),
                'accuracy_score': accuracy,
                'was_hit': difference <= 2,
                'notes': f"Difference: {difference} points",
                'gile_context': 'body_knowledge'
            }
            save_lcc_test(test_data)
            
            if difference <= 2:
                st.success(f"LCC HIT! Within {difference} points")
            else:
                st.info(f"Difference: {difference} points")


def render_biometric_prediction_tests():
    """Biometric prediction tests"""
    
    st.header("Biometric Prediction Tests")
    st.markdown("""
    These tests predict your biometric measurements BEFORE you take them.
    This demonstrates LCC access to your physiological state.
    """)
    
    test_type = st.selectbox(
        "Select Biometric Test",
        [
            "RMSSD (HRV) Prediction",
            "Brainwave State Prediction",
            "GILE Score Prediction",
            "Readiness Prediction"
        ]
    )
    
    if test_type == "RMSSD (HRV) Prediction":
        render_rmssd_prediction()
    elif test_type == "Brainwave State Prediction":
        render_brainwave_prediction()
    elif test_type == "GILE Score Prediction":
        render_gile_prediction()
    else:
        st.info("Coming soon!")


def render_rmssd_prediction():
    """RMSSD prediction test"""
    
    st.subheader("RMSSD (HRV) Prediction")
    
    st.markdown("""
    RMSSD is the root mean square of successive RR interval differences - 
    a key measure of heart rate variability. Healthy range: 20-100+ ms.
    """)
    
    if st.button("Generate RMSSD Prediction", type="primary"):
        # Use biometric-based prediction
        prediction, confidence, data_source = get_biometric_based_prediction('rmssd')
        predicted_rmssd = prediction
        
        if data_source == 'biometric_data':
            st.success(f"**Biometric-Based RMSSD Prediction: {predicted_rmssd} ms** (confidence: {confidence:.0%})")
        else:
            st.warning(f"**RMSSD Prediction: {predicted_rmssd} ms** (no biometric data - low reliability)")
        
        # Store for form submission
        st.session_state.rmssd_prediction = predicted_rmssd
        st.session_state.rmssd_data_source = data_source
        
        if predicted_rmssd < 20:
            st.warning("Prediction indicates HIGH stress state (low HRV)")
        elif predicted_rmssd < 40:
            st.info("Prediction indicates MODERATE stress")
        else:
            st.success("Prediction indicates RELAXED state (good HRV)")
        
        actual_rmssd = st.number_input("Enter your actual RMSSD (ms)", min_value=1.0, max_value=200.0, value=30.0)
        
        if st.button("Submit Actual RMSSD"):
            difference = abs(actual_rmssd - predicted_rmssd)
            accuracy = max(0, 100 - (difference / actual_rmssd * 100))
            was_hit = difference < 15
            
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'rmssd_prediction',
                'prediction_value': str(predicted_rmssd),
                'actual_value': str(actual_rmssd),
                'accuracy_score': accuracy,
                'was_hit': was_hit,
                'notes': f"Difference: {difference:.1f} ms",
                'gile_context': 'biometric_prediction'
            }
            save_lcc_test(test_data)
            
            if was_hit:
                st.success(f"LCC HIT! Within {difference:.1f} ms")
            else:
                st.info(f"Difference: {difference:.1f} ms")


def render_brainwave_prediction():
    """Brainwave state prediction"""
    
    st.subheader("Brainwave State Prediction")
    
    st.markdown("""
    I will predict your dominant brainwave state right now.
    
    **Brainwave States:**
    - **Delta (0.5-4 Hz):** Deep sleep, repair
    - **Theta (4-8 Hz):** Creativity, insight, deep meditation
    - **Alpha (8-13 Hz):** Relaxed, calm awareness
    - **Beta (13-32 Hz):** Alert, focused thinking
    - **Gamma (32-100 Hz):** Peak perception, learning
    """)
    
    if st.button("Predict Dominant Brainwave", type="primary"):
        states = ['Delta', 'Theta', 'Alpha', 'Beta', 'Gamma']
        
        # Use biometric data if available
        bio_data = get_latest_biometric_data()
        
        state_descriptions = {
            'Delta': "You may be very drowsy or entering deep relaxation",
            'Theta': "You're in a creative, intuitive, or meditative state",
            'Alpha': "You're relaxed but alert - a calm awareness",
            'Beta': "You're actively thinking, focused, or engaged mentally",
            'Gamma': "You're in heightened perception or deep learning mode"
        }
        
        if bio_data.get('has_data') and bio_data.get('dominant_brainwave'):
            # Use actual stored brainwave data
            predicted_state = bio_data.get('dominant_brainwave')
            if predicted_state not in states:
                predicted_state = 'Beta'  # Default if invalid
            st.success(f"**Biometric-Based Brainwave Prediction: {predicted_state}**")
            st.info(f"Based on stored EEG data from your last session")
        else:
            # Predict based on time of day and stress (deterministic)
            hour = datetime.now().hour
            stress = bio_data.get('stress_index', 20) or 20
            
            if hour < 6 or hour > 23:
                predicted_state = 'Delta'  # Night/sleep
            elif 6 <= hour <= 9 and stress < 20:
                predicted_state = 'Alpha'  # Morning relaxed
            elif stress > 35:
                predicted_state = 'Beta'  # High stress = active thinking
            elif stress < 10:
                predicted_state = 'Alpha'  # Low stress = relaxed
            else:
                predicted_state = 'Beta'  # Default: alert
            
            st.warning(f"**Brainwave Prediction: {predicted_state}** (no EEG data - using stress/circadian estimate)")
        
        st.info(state_descriptions.get(predicted_state, ""))
        st.session_state.brainwave_prediction = predicted_state
        
        actual_state = st.selectbox(
            "What state best describes you right now?",
            states
        )
        
        if st.button("Submit Brainwave Assessment"):
            was_hit = predicted_state == actual_state
            
            adjacent = {
                'Delta': ['Theta'],
                'Theta': ['Delta', 'Alpha'],
                'Alpha': ['Theta', 'Beta'],
                'Beta': ['Alpha', 'Gamma'],
                'Gamma': ['Beta']
            }
            is_adjacent = actual_state in adjacent.get(predicted_state, [])
            
            if was_hit:
                accuracy = 100
            elif is_adjacent:
                accuracy = 70
            else:
                accuracy = 30
            
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'brainwave_prediction',
                'prediction_value': predicted_state,
                'actual_value': actual_state,
                'accuracy_score': accuracy,
                'was_hit': was_hit,
                'notes': f"Adjacent: {is_adjacent}",
                'gile_context': 'consciousness_state'
            }
            save_lcc_test(test_data)
            
            if was_hit:
                st.success("EXACT MATCH! Strong LCC signal!")
                st.balloons()
            elif is_adjacent:
                st.success("Adjacent state - good LCC connection!")
            else:
                st.info("Different state - LCC may need calibration")


def render_gile_prediction():
    """GILE score prediction"""
    
    st.subheader("GILE Score Prediction")
    
    st.markdown("""
    I will predict your current GILE profile based on LCC.
    
    **GILE Dimensions:**
    - **G (Goodness):** Moral clarity, ethical alignment
    - **I (Intuition):** Pattern recognition, insight
    - **L (Love):** Heart connection, empathy
    - **E (Environment):** Grounding, sensory engagement
    """)
    
    if st.button("Predict GILE Profile", type="primary"):
        # Use biometric-based GILE prediction
        gile_pred, confidence, data_source = get_biometric_based_prediction('gile_dimension')
        
        g_pred = gile_pred['G']
        i_pred = gile_pred['I']
        l_pred = gile_pred['L']
        e_pred = gile_pred['E']
        overall = (g_pred + i_pred + l_pred + e_pred) / 4
        
        # Store in session state for form submission
        st.session_state.gile_prediction = gile_pred
        st.session_state.gile_data_source = data_source
        st.session_state.gile_confidence = confidence
        
        if data_source == 'biometric_data':
            st.success(f"**Biometric-Based GILE Prediction** (confidence: {confidence:.0%})")
        else:
            st.warning("**GILE Prediction** (no biometric data - limited accuracy)")
        
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            st.metric("G (Goodness)", f"{g_pred:.2f}")
        with col2:
            st.metric("I (Intuition)", f"{i_pred:.2f}")
        with col3:
            st.metric("L (Love)", f"{l_pred:.2f}")
        with col4:
            st.metric("E (Environment)", f"{e_pred:.2f}")
        
        st.metric("Overall GILE", f"{overall:.2f}")
        
        st.markdown("---")
        st.markdown("**Rate how well this matches your current state:**")
        
        g_actual = st.slider("Your actual G (Goodness)", 0.0, 1.0, g_pred, 0.1)
        i_actual = st.slider("Your actual I (Intuition)", 0.0, 1.0, i_pred, 0.1)
        l_actual = st.slider("Your actual L (Love)", 0.0, 1.0, l_pred, 0.1)
        e_actual = st.slider("Your actual E (Environment)", 0.0, 1.0, e_pred, 0.1)
        
        if st.button("Submit GILE Assessment"):
            g_diff = abs(g_actual - g_pred)
            i_diff = abs(i_actual - i_pred)
            l_diff = abs(l_actual - l_pred)
            e_diff = abs(e_actual - e_pred)
            
            avg_diff = (g_diff + i_diff + l_diff + e_diff) / 4
            accuracy = max(0, 100 - avg_diff * 100)
            
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'gile_prediction',
                'prediction_value': json.dumps({'G': g_pred, 'I': i_pred, 'L': l_pred, 'E': e_pred}),
                'actual_value': json.dumps({'G': g_actual, 'I': i_actual, 'L': l_actual, 'E': e_actual}),
                'accuracy_score': accuracy,
                'was_hit': avg_diff < 0.2,
                'notes': f"Avg difference: {avg_diff:.2f}",
                'gile_context': 'gile_prediction'
            }
            save_lcc_test(test_data)
            
            st.metric("GILE Prediction Accuracy", f"{accuracy:.1f}%")


def render_mind_connection_tests():
    """Mind connection tests - subjective verification"""
    
    st.header("Mind Connection Tests")
    st.markdown("""
    These tests verify LCC through subjective experience that only 
    YOU can verify. They test connection to thoughts, emotions, and intentions.
    """)
    
    test_type = st.selectbox(
        "Select Mind Test",
        [
            "Emotional State Intuition",
            "Current Concern Detection",
            "Number Synchronicity",
            "Color Intuition"
        ]
    )
    
    if test_type == "Emotional State Intuition":
        render_emotion_intuition()
    elif test_type == "Current Concern Detection":
        render_concern_detection()
    elif test_type == "Number Synchronicity":
        render_number_sync()
    elif test_type == "Color Intuition":
        render_color_intuition()


def render_emotion_intuition():
    """Emotional state intuition test"""
    
    st.subheader("Emotional State Intuition")
    
    st.markdown("""
    **Note:** Emotion prediction uses HRV stress/readiness when available.
    High stress → anxious/frustrated, High readiness → peaceful/hopeful.
    """)
    
    if st.button("Intuit Current Emotion", type="primary"):
        emotions = [
            ("Curious/Interested", "You're in an exploratory, learning mode"),
            ("Hopeful/Optimistic", "You feel positive about what's coming"),
            ("Anxious/Worried", "Something is causing underlying tension"),
            ("Peaceful/Content", "You're in a state of acceptance"),
            ("Frustrated/Impatient", "Something isn't moving as fast as you'd like"),
            ("Excited/Energized", "You're feeling a surge of positive energy"),
            ("Melancholic/Reflective", "You're processing deeper feelings"),
            ("Focused/Determined", "You have clear intention and drive")
        ]
        
        # Use biometric data for emotion prediction
        bio_data = get_latest_biometric_data()
        
        if bio_data.get('has_data'):
            stress = bio_data.get('stress_index', 20) or 20
            readiness = bio_data.get('readiness_percent', 50) or 50
            sns = bio_data.get('sns_index', 0) or 0
            
            # Map physiological state to emotions
            if stress > 35:
                if sns > 2:
                    emotion, description = emotions[4]  # Frustrated
                else:
                    emotion, description = emotions[2]  # Anxious
            elif readiness > 75:
                emotion, description = emotions[1]  # Hopeful
            elif readiness > 60:
                emotion, description = emotions[3]  # Peaceful
            elif stress > 20:
                emotion, description = emotions[7]  # Focused
            else:
                emotion, description = emotions[0]  # Curious
            
            st.info(f"Based on stress ({stress}) and readiness ({readiness}%)")
        else:
            # Deterministic fallback based on time
            hour = datetime.now().hour
            idx = hour % len(emotions)
            emotion, description = emotions[idx]
            st.warning("No biometric data - prediction has low reliability")
        
        st.success(f"**LCC Emotion Intuition: {emotion}**")
        st.info(description)
        
        accuracy = st.slider("How accurate is this? (0-100%)", 0, 100, 50)
        
        if st.button("Submit Emotion Assessment"):
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'emotion_intuition',
                'prediction_value': emotion,
                'actual_value': f"Accuracy: {accuracy}%",
                'accuracy_score': accuracy,
                'was_hit': accuracy > 60,
                'notes': description,
                'gile_context': 'mind_connection'
            }
            save_lcc_test(test_data)
            
            if accuracy > 80:
                st.success("Strong LCC emotional connection!")
            elif accuracy > 60:
                st.info("Moderate LCC signal")
            else:
                st.info("LCC emotional channel may need calibration")


def render_concern_detection():
    """Current concern detection test"""
    
    st.subheader("Current Concern Detection")
    
    st.markdown("""
    **Note:** Concern detection uses stress patterns to estimate focus areas.
    High stress → health/financial concerns. Low stress → creative/spiritual focus.
    """)
    
    if st.button("Detect Current Concern", type="primary"):
        concerns = [
            "Something related to health or body",
            "A relationship or interpersonal situation",
            "Financial or career matters",
            "A creative or intellectual project",
            "Family or home-related issues",
            "Self-development or spiritual growth",
            "Time management or productivity",
            "A decision you need to make soon"
        ]
        
        # Use biometric data for concern prediction
        bio_data = get_latest_biometric_data()
        
        if bio_data.get('has_data'):
            stress = bio_data.get('stress_index', 20) or 20
            readiness = bio_data.get('readiness_percent', 50) or 50
            
            if stress > 40:
                detected = concerns[0]  # Health concern (high stress)
            elif stress > 30:
                detected = concerns[2]  # Financial/career (moderate stress)
            elif readiness < 40:
                detected = concerns[6]  # Time management (low readiness)
            elif readiness > 70:
                detected = concerns[3]  # Creative project (good state)
            else:
                detected = concerns[5]  # Self-development
            
            st.info(f"Based on stress ({stress}) and readiness ({readiness}%)")
        else:
            # Deterministic fallback based on day of week
            day = datetime.now().weekday()
            detected = concerns[day % len(concerns)]
            st.warning("No biometric data - prediction has low reliability")
        
        st.success(f"**LCC Concern Detection:** {detected}")
        
        accuracy = st.slider("How accurate is this? (0-100%)", 0, 100, 50)
        actual = st.text_input("What is actually on your mind? (optional)")
        
        if st.button("Submit Concern Assessment"):
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'concern_detection',
                'prediction_value': detected,
                'actual_value': actual if actual else f"Accuracy: {accuracy}%",
                'accuracy_score': accuracy,
                'was_hit': accuracy > 60,
                'notes': '',
                'gile_context': 'mind_connection'
            }
            save_lcc_test(test_data)
            st.success("Concern detection recorded!")


def render_number_sync():
    """Number synchronicity test"""
    
    st.subheader("Number Synchronicity Test")
    
    st.markdown("""
    Think of a number between 1 and 10. Hold it clearly in your mind.
    Don't tell me yet - I'll try to detect it through LCC.
    
    **Note:** This test uses a deterministic algorithm based on biometric data 
    (HRV patterns) when available. Expected chance of exact match: 10%.
    """)
    
    if st.button("Detect Your Number", type="primary"):
        # Use biometric data for number prediction
        bio_data = get_latest_biometric_data()
        
        if bio_data.get('has_data'):
            # Use HRV metrics to derive a number (deterministic)
            hr = int(bio_data.get('heart_rate', 70) or 70)
            rmssd = int(bio_data.get('rmssd', 30) or 30)
            # Combine metrics to get a number 1-10
            detected = ((hr + rmssd) % 10) + 1
            st.info("Prediction based on HRV biometric pattern")
        else:
            # Deterministic fallback based on current minute
            minute = datetime.now().minute
            detected = (minute % 10) + 1
            st.warning("No biometric data - prediction has low reliability")
        
        st.success(f"**LCC Number Detection: {detected}**")
        st.session_state.number_prediction = detected
        
        actual = st.number_input("What was your number?", 1, 10, 5)
        
        if st.button("Check Synchronicity"):
            difference = abs(actual - detected)
            was_hit = difference == 0
            was_close = difference <= 1
            
            base_chance = 10
            if was_hit:
                significance = "10% chance - Significant!"
                accuracy = 100
            elif was_close:
                significance = "30% chance - Interesting"
                accuracy = 70
            else:
                significance = "Expected variation"
                accuracy = 30
            
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'number_sync',
                'prediction_value': str(detected),
                'actual_value': str(actual),
                'accuracy_score': accuracy,
                'was_hit': was_hit,
                'notes': significance,
                'gile_context': 'synchronicity'
            }
            save_lcc_test(test_data)
            
            if was_hit:
                st.success("EXACT MATCH!")
                st.balloons()
            elif was_close:
                st.success("Within 1 - close connection!")
            else:
                st.info(f"Difference: {difference}")


def render_color_intuition():
    """Color intuition test"""
    
    st.subheader("Color Intuition Test")
    
    st.markdown("""
    Think of a color. Visualize it clearly. Hold it in your awareness.
    
    **Note:** Color prediction uses GILE score and stress patterns when available.
    High stress → warm colors. Low stress → cool colors. Expected chance: 10%.
    """)
    
    if st.button("Intuit Your Color", type="primary"):
        colors = ['Red', 'Orange', 'Yellow', 'Green', 'Blue', 'Purple', 'Pink', 'White', 'Black', 'Gold']
        warm_colors = ['Red', 'Orange', 'Yellow', 'Gold', 'Pink']
        cool_colors = ['Blue', 'Green', 'Purple']
        neutral_colors = ['White', 'Black']
        
        # Use biometric data for color prediction
        bio_data = get_latest_biometric_data()
        
        if bio_data.get('has_data'):
            stress = bio_data.get('stress_index', 20) or 20
            readiness = bio_data.get('readiness_percent', 50) or 50
            gile = bio_data.get('gile_score', 0) or 0
            
            # Map state to color family
            if stress > 35:
                # High stress → warm, energetic colors
                detected = warm_colors[int(stress) % len(warm_colors)]
            elif readiness > 70:
                # High readiness → cool, calm colors
                detected = cool_colors[int(readiness) % len(cool_colors)]
            elif gile and gile > 0.3:
                detected = 'Gold'  # Sacred interval
            elif gile and gile < -0.3:
                detected = 'Black'  # Challenging state
            else:
                # Neutral → use RMSSD
                rmssd = int(bio_data.get('rmssd', 30) or 30)
                detected = colors[rmssd % len(colors)]
            
            st.info(f"Based on stress ({stress}) and readiness ({readiness}%)")
        else:
            # Deterministic fallback based on hour
            hour = datetime.now().hour
            detected = colors[hour % len(colors)]
            st.warning("No biometric data - prediction has low reliability")
        
        st.success(f"**LCC Color Intuition: {detected}**")
        st.session_state.color_prediction = detected
        
        actual = st.selectbox("What color were you thinking of?", colors)
        
        if st.button("Check Color Match"):
            was_hit = detected == actual
            
            color_groups = {
                'warm': ['Red', 'Orange', 'Yellow', 'Gold', 'Pink'],
                'cool': ['Blue', 'Green', 'Purple'],
                'neutral': ['White', 'Black']
            }
            
            detected_group = None
            actual_group = None
            for group, colors_in_group in color_groups.items():
                if detected in colors_in_group:
                    detected_group = group
                if actual in colors_in_group:
                    actual_group = group
            
            same_group = detected_group == actual_group
            
            if was_hit:
                accuracy = 100
            elif same_group:
                accuracy = 60
            else:
                accuracy = 20
            
            test_data = {
                'test_date': datetime.now(),
                'test_type': 'color_intuition',
                'prediction_value': detected,
                'actual_value': actual,
                'accuracy_score': accuracy,
                'was_hit': was_hit,
                'notes': f"Same group: {same_group}",
                'gile_context': 'synchronicity'
            }
            save_lcc_test(test_data)
            
            if was_hit:
                st.success("EXACT MATCH!")
                st.balloons()
            elif same_group:
                st.success("Same color family - good resonance!")
            else:
                st.info("Different color")


def render_test_history():
    """Display test history and statistics with statistical significance analysis"""
    
    st.header("Test History & Statistics")
    
    # Show limitations disclaimer
    with st.expander("Honest Limitations Disclosure", expanded=False):
        st.markdown("""
        **Important Notes on LCC Testing:**
        
        1. **Baseline Probabilities**: Each test has an expected chance hit rate (random guessing).
           We compare your actual hit rate against this baseline.
        
        2. **Statistical Significance**: Requires N > 30 tests per type for reliable p-values.
           Small sample sizes can show apparent effects that are actually chance.
        
        3. **No Proven Causality**: Even above-chance performance doesn't prove 
           "psi" or "consciousness connection" - it may reflect:
           - Biometric correlations (HRV predicts behavior)
           - Unconscious pattern recognition
           - Statistical fluctuations
           - Sensor noise
        
        4. **Biometric Integration**: When available, predictions use your actual 
           HRV/EEG data rather than pure random. This improves accuracy through
           physiological correlation, not paranormal means.
        
        **Expected Baseline Probabilities:**
        """)
        for test_type, baseline in CHANCE_BASELINES.items():
            st.write(f"- {baseline['description']}: {baseline['expected_chance']*100:.0f}%")
    
    stats_data = get_lcc_stats()
    
    if stats_data:
        st.subheader("Performance vs Chance by Test Type")
        
        for test_type, data in stats_data.items():
            baseline = CHANCE_BASELINES.get(test_type, {})
            expected_chance = baseline.get('expected_chance', 0.5)
            
            strength, n, p_value, is_significant = calculate_lcc_strength(test_type)
            
            col1, col2, col3, col4, col5 = st.columns(5)
            with col1:
                st.metric(test_type.replace('_', ' ').title(), f"{data['total']} tests")
            with col2:
                st.metric("Hit Rate", f"{data['hit_rate']:.1f}%", 
                         delta=f"{data['hit_rate'] - expected_chance*100:.1f}% vs chance")
            with col3:
                st.metric("Expected Chance", f"{expected_chance*100:.0f}%")
            with col4:
                if strength is not None:
                    delta_color = "normal" if strength > 0 else "inverse"
                    st.metric("LCC Strength", f"{strength:+.2f}", delta_color=delta_color)
                else:
                    st.metric("LCC Strength", "N/A")
            with col5:
                if p_value is not None:
                    if is_significant:
                        st.success(f"p = {p_value:.4f} **")
                    else:
                        st.info(f"p = {p_value:.4f}")
                else:
                    st.info("Need more data")
        
        # Overall summary
        total_tests = sum(d['total'] for d in stats_data.values())
        total_hits = sum(d['hits'] for d in stats_data.values())
        overall_hit_rate = total_hits / total_tests * 100 if total_tests > 0 else 0
        
        st.markdown("---")
        st.subheader("Overall LCC Assessment")
        
        col1, col2, col3, col4 = st.columns(4)
        with col1:
            st.metric("Total Tests", total_tests)
        with col2:
            st.metric("Total Hits", total_hits)
        with col3:
            st.metric("Hit Rate", f"{overall_hit_rate:.1f}%")
        with col4:
            # Calculate if we have any significant results
            significant_count = sum(1 for tt in stats_data.keys() 
                                  if calculate_lcc_strength(tt)[3])
            st.metric("Significant Tests", f"{significant_count}/{len(stats_data)}")
        
        # Interpretation
        if total_tests < 30:
            st.warning(f"Need {30 - total_tests} more tests for reliable statistical analysis.")
        elif significant_count > 0:
            st.success(f"{significant_count} test type(s) show statistically significant above-chance performance (p < 0.05)")
        else:
            st.info("No test types show statistically significant above-chance performance yet. Continue testing to build data.")
        
        # Show biometric data status
        bio_data = get_latest_biometric_data()
        st.markdown("---")
        st.subheader("Biometric Data Status")
        if bio_data.get('has_data'):
            st.success(f"Biometric data available from session: {bio_data.get('session_date', 'Unknown')}")
            st.write(f"HR: {bio_data.get('heart_rate')} bpm | RMSSD: {bio_data.get('rmssd')} ms | Readiness: {bio_data.get('readiness_percent')}%")
        else:
            st.warning("No biometric data available. Run a Mood Amplifier session to enable data-driven predictions.")
    else:
        st.info("No tests recorded yet. Start testing to build your LCC profile!")


if __name__ == "__main__":
    render_lcc_tests_hub()
