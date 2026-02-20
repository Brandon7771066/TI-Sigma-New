"""
Brain Coupling Test - Number Guessing
======================================
A statistically rigorous 1-10 number guessing game designed to measure
intuitive brain coupling accuracy with real-time statistical analysis.
"""

import streamlit as st
import numpy as np
import pandas as pd
from datetime import datetime
from scipy import stats
import math
import os


def initialize_session_state():
    """Set up all session state variables for the brain coupling test."""
    defaults = {
        'bcg_target': None,
        'bcg_guesses': [],
        'bcg_last_result': None,
        'bcg_current_streak': 0,
        'bcg_longest_streak': 0,
        'bcg_round_active': True,
        'bcg_session_start': datetime.now().isoformat(),
    }
    for key, value in defaults.items():
        if key not in st.session_state:
            st.session_state[key] = value


def generate_target():
    """Generate a new random target number 1-10 and store in session state."""
    st.session_state.bcg_target = int(np.random.randint(1, 11))
    st.session_state.bcg_round_active = True
    st.session_state.bcg_last_result = None


def classify_result(guess, target):
    """Classify a guess as HIT, NEAR, or MISS."""
    if guess == target:
        return "HIT"
    diff = abs(guess - target)
    if diff == 1 or (guess == 1 and target == 10) or (guess == 10 and target == 1):
        return "NEAR"
    return "MISS"


def process_guess(guess):
    """Process a user's guess against the current target."""
    target = st.session_state.bcg_target
    result = classify_result(guess, target)

    entry = {
        'timestamp': datetime.now().isoformat(),
        'guess': guess,
        'actual': target,
        'result': result,
        'round': len(st.session_state.bcg_guesses) + 1,
    }
    st.session_state.bcg_guesses.append(entry)

    if result == "HIT":
        st.session_state.bcg_current_streak += 1
        if st.session_state.bcg_current_streak > st.session_state.bcg_longest_streak:
            st.session_state.bcg_longest_streak = st.session_state.bcg_current_streak
    else:
        st.session_state.bcg_current_streak = 0

    st.session_state.bcg_last_result = {
        'guess': guess,
        'actual': target,
        'result': result,
    }
    st.session_state.bcg_round_active = False


def compute_statistics(guesses):
    """Compute all statistical metrics from the guess history."""
    if not guesses:
        return {
            'total': 0, 'hits': 0, 'near_misses': 0, 'misses': 0,
            'hit_rate': 0.0, 'near_rate': 0.0, 'miss_rate': 0.0,
            'p_value': 1.0, 'p_value_str': 'N/A',
            'significance': 'Not enough data',
            'bcs': 0.0, 'gile_score': 0.0,
            'ci_lower': 0.0, 'ci_upper': 0.0,
            'chi2_p': None, 'chi2_stat': None,
        }

    total = len(guesses)
    hits = sum(1 for g in guesses if g['result'] == 'HIT')
    near_misses = sum(1 for g in guesses if g['result'] == 'NEAR')
    misses = total - hits - near_misses

    hit_rate = hits / total
    near_rate = near_misses / total
    miss_rate = misses / total

    if total >= 10:
        p_value = stats.binom.sf(hits - 1, total, 0.10)
        p_value_str = f"{p_value:.6f}"
    else:
        p_value = 1.0
        p_value_str = "Need 10+ guesses"

    if total >= 10:
        if p_value < 0.001:
            significance = "🌟 EXTREMELY SIGNIFICANT (p < 0.001)"
        elif p_value < 0.01:
            significance = "⭐ HIGHLY SIGNIFICANT (p < 0.01)"
        elif p_value < 0.05:
            significance = "✅ SIGNIFICANT (p < 0.05)"
        elif p_value < 0.10:
            significance = "📊 Marginally significant (p < 0.10)"
        else:
            significance = "📈 Not significant (keep testing)"
    else:
        significance = f"Need {10 - total} more guesses for analysis"

    if total > 0:
        se = math.sqrt(hit_rate * (1 - hit_rate) / total) if hit_rate > 0 and hit_rate < 1 else 0
        ci_lower = max(0, hit_rate - 1.96 * se)
        ci_upper = min(1, hit_rate + 1.96 * se)
    else:
        ci_lower = 0.0
        ci_upper = 0.0

    chi2_p = None
    chi2_stat = None
    if total >= 30:
        actual_counts = np.zeros(10)
        for g in guesses:
            actual_counts[g['actual'] - 1] += 1
        expected_counts = np.full(10, total / 10.0)
        chi2_stat, chi2_p = stats.chisquare(actual_counts, expected_counts)

    expected_hit = 0.10
    expected_near = 0.20
    excess_hit = max(0, hit_rate - expected_hit)
    excess_near = max(0, near_rate - expected_near)

    longest_streak = st.session_state.bcg_longest_streak
    streak_bonus = min(20, longest_streak * 5)
    bcs = min(100, (excess_hit * 500 + excess_near * 200 + streak_bonus))

    if total > 0:
        accuracy_factor = hit_rate / expected_hit if expected_hit > 0 else 1.0
        near_factor = near_rate / expected_near if expected_near > 0 else 1.0
        consistency = 1.0 - (miss_rate / 0.70 if miss_rate < 0.70 else 1.0)
        raw_gile = (accuracy_factor * 0.5 + near_factor * 0.2 + consistency * 0.3) * 10
        gile_score = min(10.0, max(0.0, raw_gile))
    else:
        gile_score = 0.0

    return {
        'total': total, 'hits': hits, 'near_misses': near_misses, 'misses': misses,
        'hit_rate': hit_rate, 'near_rate': near_rate, 'miss_rate': miss_rate,
        'p_value': p_value, 'p_value_str': p_value_str,
        'significance': significance,
        'bcs': bcs, 'gile_score': gile_score,
        'ci_lower': ci_lower, 'ci_upper': ci_upper,
        'chi2_p': chi2_p, 'chi2_stat': chi2_stat,
    }


def render_result_display():
    """Render the big colored result display."""
    result = st.session_state.bcg_last_result
    if result is None:
        st.markdown(
            "<div style='text-align:center; padding:40px; background:linear-gradient(135deg,#1a1a2e,#16213e); "
            "border-radius:15px; margin:10px 0;'>"
            "<div style='font-size:48px;'>🧠</div>"
            "<div style='font-size:24px; color:#aaa; margin-top:10px;'>Focus your intuition...</div>"
            "<div style='font-size:16px; color:#666; margin-top:5px;'>Pick a number 1-10 below</div>"
            "</div>",
            unsafe_allow_html=True
        )
        return

    guess = result['guess']
    actual = result['actual']
    outcome = result['result']

    if outcome == "HIT":
        bg = "linear-gradient(135deg, #0a3d0a, #1a5a1a)"
        border_color = "#00ff88"
        emoji = "🎯"
        label = "EXACT HIT!"
        text_color = "#00ff88"
        sub = f"You guessed {guess} — Target was {actual}"
    elif outcome == "NEAR":
        bg = "linear-gradient(135deg, #3d3d0a, #5a5a1a)"
        border_color = "#ffcc00"
        emoji = "🔥"
        label = "NEAR MISS!"
        text_color = "#ffcc00"
        sub = f"You guessed {guess} — Target was {actual} (off by {abs(guess - actual)})"
    else:
        bg = "linear-gradient(135deg, #3d0a0a, #5a1a1a)"
        border_color = "#ff4444"
        emoji = "❌"
        label = "MISS"
        text_color = "#ff4444"
        sub = f"You guessed {guess} — Target was {actual}"

    st.markdown(
        f"<div style='text-align:center; padding:30px; background:{bg}; "
        f"border:2px solid {border_color}; border-radius:15px; margin:10px 0;'>"
        f"<div style='font-size:48px;'>{emoji}</div>"
        f"<div style='font-size:36px; color:{text_color}; font-weight:bold; margin-top:5px;'>{label}</div>"
        f"<div style='font-size:18px; color:#ccc; margin-top:8px;'>{sub}</div>"
        f"</div>",
        unsafe_allow_html=True
    )


def render_number_buttons():
    """Render the 1-10 number buttons for guessing."""
    if not st.session_state.bcg_round_active:
        return

    cols = st.columns(10)
    for i, col in enumerate(cols):
        num = i + 1
        with col:
            if st.button(str(num), key=f"bcg_btn_{num}", use_container_width=True):
                process_guess(num)
                st.rerun()


def render_statistics_panel(stats_data):
    """Render the statistics panel."""
    st.markdown("### 📊 Statistics")

    col_a, col_b = st.columns(2)
    with col_a:
        st.metric("Total Guesses", stats_data['total'])
        st.metric(
            "Hits",
            f"{stats_data['hits']} ({stats_data['hit_rate']*100:.1f}%)",
            f"{(stats_data['hit_rate'] - 0.10)*100:+.1f}% vs expected" if stats_data['total'] > 0 else None
        )
        st.metric(
            "Near Misses",
            f"{stats_data['near_misses']} ({stats_data['near_rate']*100:.1f}%)"
        )
    with col_b:
        st.metric("Expected Hit Rate", "10.0%")
        st.metric("P-Value", stats_data['p_value_str'])
        st.metric("Brain Coupling Score", f"{stats_data['bcs']:.1f}")

    st.markdown("---")
    st.markdown(f"**{stats_data['significance']}**")

    if stats_data['total'] >= 10:
        st.markdown(
            f"**95% CI for hit rate**: "
            f"[{stats_data['ci_lower']*100:.1f}%, {stats_data['ci_upper']*100:.1f}%]"
        )

    if stats_data['chi2_p'] is not None:
        st.markdown("---")
        st.markdown("### 📐 Distribution Test")
        st.markdown(f"**Chi-square statistic**: {stats_data['chi2_stat']:.3f}")
        chi_p = stats_data['chi2_p']
        if chi_p < 0.05:
            st.warning(f"⚠️ Target distribution may be non-uniform (p={chi_p:.4f})")
        else:
            st.success(f"✅ Target distribution appears uniform (p={chi_p:.4f})")


def render_streak_panel():
    """Render streak tracking information."""
    st.markdown("### 🔥 Streaks")
    col_a, col_b = st.columns(2)
    with col_a:
        st.metric("Current Streak", st.session_state.bcg_current_streak)
    with col_b:
        st.metric("Longest Streak", st.session_state.bcg_longest_streak)


def render_gile_panel(stats_data):
    """Render the GILE score panel."""
    st.markdown("### 🧬 GILE Score")
    gile = stats_data['gile_score']

    if gile >= 8.0:
        gile_color = "#00ff88"
        gile_label = "Exceptional"
    elif gile >= 6.0:
        gile_color = "#44aaff"
        gile_label = "Strong"
    elif gile >= 4.0:
        gile_color = "#ffcc00"
        gile_label = "Moderate"
    elif gile >= 2.0:
        gile_color = "#ff8800"
        gile_label = "Developing"
    else:
        gile_color = "#ff4444"
        gile_label = "Baseline"

    st.markdown(
        f"<div style='text-align:center; padding:15px; background:#ffffff10; border-radius:10px; "
        f"border:1px solid {gile_color};'>"
        f"<div style='font-size:36px; color:{gile_color}; font-weight:bold;'>{gile:.1f}</div>"
        f"<div style='font-size:14px; color:{gile_color};'>{gile_label}</div>"
        f"</div>",
        unsafe_allow_html=True
    )

    if stats_data['total'] > 0:
        st.markdown(
            f"<div style='font-size:12px; color:#888; margin-top:8px; text-align:center;'>"
            f"Based on {stats_data['total']} trials"
            f"</div>",
            unsafe_allow_html=True
        )


def render_history_table(guesses):
    """Render the history table of recent guesses."""
    if not guesses:
        st.info("No guesses yet. Start playing to see your history!")
        return

    recent = guesses[-20:][::-1]

    rows = []
    for g in recent:
        ts = g['timestamp']
        try:
            dt = datetime.fromisoformat(ts)
            time_str = dt.strftime("%H:%M:%S")
        except (ValueError, TypeError):
            time_str = ts

        result_emoji = {"HIT": "🎯 HIT", "NEAR": "🔥 NEAR", "MISS": "❌ MISS"}
        rows.append({
            'Round': g['round'],
            'Time': time_str,
            'Guess': g['guess'],
            'Actual': g['actual'],
            'Result': result_emoji.get(g['result'], g['result']),
        })

    df = pd.DataFrame(rows)
    st.dataframe(df, use_container_width=True, hide_index=True)


def render_distribution_charts(guesses):
    """Render bar charts showing distribution of guesses vs actual numbers."""
    if len(guesses) < 3:
        return

    guess_counts = np.zeros(10)
    actual_counts = np.zeros(10)
    for g in guesses:
        guess_counts[g['guess'] - 1] += 1
        actual_counts[g['actual'] - 1] += 1

    labels = [str(i) for i in range(1, 11)]

    chart_df = pd.DataFrame({
        'Number': labels,
        'Your Guesses': guess_counts,
        'Target Numbers': actual_counts,
    })
    chart_df = chart_df.set_index('Number')

    st.bar_chart(chart_df)


def render_bcs_breakdown(stats_data):
    """Render a breakdown of the Brain Coupling Score calculation."""
    if stats_data['total'] < 5:
        return

    hit_rate = stats_data['hit_rate']
    near_rate = stats_data['near_rate']
    expected_hit = 0.10
    expected_near = 0.20

    excess_hit = max(0, hit_rate - expected_hit)
    excess_near = max(0, near_rate - expected_near)
    streak_bonus = min(20, st.session_state.bcg_longest_streak * 5)

    hit_component = excess_hit * 500
    near_component = excess_near * 200

    st.markdown("### 🧮 BCS Breakdown")
    breakdown_data = {
        'Component': ['Hit Excess', 'Near Excess', 'Streak Bonus', 'Total BCS'],
        'Value': [
            f"{hit_component:.1f}",
            f"{near_component:.1f}",
            f"{streak_bonus:.1f}",
            f"{stats_data['bcs']:.1f}"
        ],
        'Detail': [
            f"({hit_rate*100:.1f}% - {expected_hit*100:.0f}%) × 500",
            f"({near_rate*100:.1f}% - {expected_near*100:.0f}%) × 200",
            f"Longest streak ({st.session_state.bcg_longest_streak}) × 5",
            "Capped at 100"
        ]
    }
    st.dataframe(pd.DataFrame(breakdown_data), use_container_width=True, hide_index=True)


def render_power_analysis(stats_data):
    """Show how many more trials are needed for significance."""
    total = stats_data['total']
    if total < 5 or total >= 100:
        return

    st.markdown("### 🔬 Power Analysis")

    current_hits = stats_data['hits']

    needed_for_05 = 0
    for n in range(total, total + 500):
        threshold = stats.binom.isf(0.05, n, 0.10)
        projected_hits = current_hits + int((n - total) * stats_data['hit_rate']) if stats_data['hit_rate'] > 0.10 else current_hits
        if projected_hits >= threshold:
            needed_for_05 = n - total
            break

    if needed_for_05 > 0:
        st.info(f"At your current hit rate ({stats_data['hit_rate']*100:.1f}%), "
                f"you may reach p < 0.05 in approximately **{needed_for_05}** more trials.")
    else:
        if stats_data['p_value'] < 0.05:
            st.success("You've already achieved statistical significance!")
        else:
            st.info("Keep testing — more trials increase statistical power. "
                    "Try at least 50-100 trials for reliable results.")

    st.markdown(f"""
    **Quick reference for {total} trials:**
    - Need **{int(stats.binom.isf(0.05, total, 0.10)) + 1}+ hits** for p < 0.05
    - Need **{int(stats.binom.isf(0.01, total, 0.10)) + 1}+ hits** for p < 0.01
    - You currently have **{current_hits} hits**
    """)


def save_to_database(stats_data):
    """Attempt to save session results to database if available."""
    try:
        db_url = os.environ.get('DATABASE_URL')
        if not db_url:
            return False

        import psycopg2

        conn = psycopg2.connect(db_url)
        cur = conn.cursor()

        cur.execute("""
            CREATE TABLE IF NOT EXISTS brain_coupling_sessions (
                id SERIAL PRIMARY KEY,
                session_start TIMESTAMP,
                session_end TIMESTAMP,
                total_guesses INTEGER,
                hits INTEGER,
                near_misses INTEGER,
                misses INTEGER,
                hit_rate FLOAT,
                p_value FLOAT,
                bcs FLOAT,
                gile_score FLOAT,
                longest_streak INTEGER,
                raw_data JSONB
            )
        """)

        import json
        cur.execute("""
            INSERT INTO brain_coupling_sessions 
            (session_start, session_end, total_guesses, hits, near_misses, misses,
             hit_rate, p_value, bcs, gile_score, longest_streak, raw_data)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            st.session_state.bcg_session_start,
            datetime.now().isoformat(),
            stats_data['total'],
            stats_data['hits'],
            stats_data['near_misses'],
            stats_data['misses'],
            stats_data['hit_rate'],
            stats_data['p_value'],
            stats_data['bcs'],
            stats_data['gile_score'],
            st.session_state.bcg_longest_streak,
            json.dumps(st.session_state.bcg_guesses),
        ))

        conn.commit()
        cur.close()
        conn.close()
        return True
    except Exception:
        return False


def load_historical_sessions():
    """Load historical session data from database if available."""
    try:
        db_url = os.environ.get('DATABASE_URL')
        if not db_url:
            return None

        import psycopg2

        conn = psycopg2.connect(db_url)
        cur = conn.cursor()

        cur.execute("""
            SELECT session_start, total_guesses, hits, hit_rate, p_value, bcs, gile_score, longest_streak
            FROM brain_coupling_sessions
            ORDER BY session_start DESC
            LIMIT 20
        """)

        rows = cur.fetchall()
        cur.close()
        conn.close()

        if not rows:
            return None

        df = pd.DataFrame(rows, columns=[
            'Session Start', 'Guesses', 'Hits', 'Hit Rate',
            'P-Value', 'BCS', 'GILE', 'Longest Streak'
        ])
        return df
    except Exception:
        return None


def render():
    """Main render function for the Brain Coupling Test page."""
    initialize_session_state()

    if st.session_state.bcg_target is None:
        generate_target()

    st.markdown(
        "<h1 style='text-align:center;'>🧠 Brain Coupling Test - Number Guessing</h1>",
        unsafe_allow_html=True
    )
    st.markdown(
        "<p style='text-align:center; color:#888; font-size:18px;'>"
        "Test your intuitive connection accuracy</p>",
        unsafe_allow_html=True
    )

    st.markdown("---")

    game_col, stats_col = st.columns([3, 2])

    with game_col:
        st.markdown("### 🎯 Game Area")

        render_result_display()

        if st.session_state.bcg_round_active:
            st.markdown(
                "<div style='text-align:center; padding:10px; color:#aaa; font-size:16px;'>"
                "Choose a number (trust your intuition):</div>",
                unsafe_allow_html=True
            )
            render_number_buttons()
        else:
            st.markdown("")
            if st.button("🔄 Next Round", type="primary", use_container_width=True):
                generate_target()
                st.rerun()

        st.markdown("")
        col_reset, col_save = st.columns(2)
        with col_reset:
            if st.button("🗑️ Reset Session", use_container_width=True):
                for key in list(st.session_state.keys()):
                    if isinstance(key, str) and key.startswith('bcg_'):
                        del st.session_state[key]
                st.rerun()
        with col_save:
            if st.button("💾 Save Session", use_container_width=True):
                current_stats = compute_statistics(st.session_state.bcg_guesses)
                if current_stats['total'] > 0:
                    saved = save_to_database(current_stats)
                    if saved:
                        st.success("Session saved to database!")
                    else:
                        st.warning("Database not available — results kept in session only.")
                else:
                    st.info("No data to save yet.")

    with stats_col:
        current_stats = compute_statistics(st.session_state.bcg_guesses)
        render_statistics_panel(current_stats)
        st.markdown("---")
        render_streak_panel()
        st.markdown("---")
        render_gile_panel(current_stats)

    st.markdown("---")

    tab_history, tab_charts, tab_breakdown, tab_historical = st.tabs([
        "📋 History", "📊 Distribution", "🧮 Score Breakdown", "📁 Past Sessions"
    ])

    with tab_history:
        render_history_table(st.session_state.bcg_guesses)

    with tab_charts:
        if st.session_state.bcg_guesses:
            st.markdown("### Distribution of Guesses vs Targets")
            render_distribution_charts(st.session_state.bcg_guesses)

            st.markdown("### Running Hit Rate")
            if len(st.session_state.bcg_guesses) >= 5:
                running_hits = []
                cumulative_hits = 0
                for i, g in enumerate(st.session_state.bcg_guesses):
                    if g['result'] == 'HIT':
                        cumulative_hits += 1
                    running_hits.append(cumulative_hits / (i + 1))

                rate_df = pd.DataFrame({
                    'Trial': range(1, len(running_hits) + 1),
                    'Your Hit Rate': running_hits,
                    'Expected (10%)': [0.10] * len(running_hits),
                })
                rate_df = rate_df.set_index('Trial')
                st.line_chart(rate_df)
        else:
            st.info("Play some rounds to see distribution charts!")

    with tab_breakdown:
        render_bcs_breakdown(current_stats)
        render_power_analysis(current_stats)

    with tab_historical:
        historical = load_historical_sessions()
        if historical is not None and not historical.empty:
            st.markdown("### Past Brain Coupling Sessions")
            st.dataframe(historical, use_container_width=True, hide_index=True)
        else:
            st.info("No historical sessions found. Save a session to start tracking progress!")

    with st.sidebar:
        st.markdown("---")
        st.markdown("### 🧠 Brain Coupling Tips")
        st.markdown("""
        - Relax and don't overthink
        - Trust your first instinct
        - Breathe deeply before each guess
        - Don't try to track patterns
        - Run 50+ trials for best results
        """)
        st.markdown("### 📊 Quick Stats")
        st.markdown(f"""
        **Expected by chance:**
        - Exact hit: 10% (1 in 10)
        - Near miss: 20% (2 in 10)
        - Miss: 70% (7 in 10)

        **Your session:**
        - Guesses: {current_stats['total']}
        - Hits: {current_stats['hits']}
        - BCS: {current_stats['bcs']:.1f}
        """)


if __name__ == "__main__" or "streamlit" in str(type(st)):
    render()
