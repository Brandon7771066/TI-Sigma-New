"""Weather Prediction Dashboard for Streamlit."""

import streamlit as st
from datetime import datetime


def render_weather_dashboard():
    """Render the weather prediction trading dashboard."""
    st.header("🌤️ TI Weather Prediction Trader")
    st.caption("AI-powered weather prediction for ForecastEx/Kalshi daily temperature contracts")

    from engines.weather_prediction_engine import (
        WeatherPredictionEngine, NWS_STATIONS, KALSHI_CITY_TICKERS,
        TAU, EPSILON, GAMMA, LAMBDA_LCC, ETA
    )

    if 'weather_engine' not in st.session_state:
        st.session_state.weather_engine = WeatherPredictionEngine(bankroll=500.0)
    engine = st.session_state.weather_engine

    weather_tabs = st.tabs(["📡 Live Scanner", "📊 Signals & Edge", "💰 Projections", "📈 History"])

    with weather_tabs[0]:
        _render_live_scanner(engine)

    with weather_tabs[1]:
        _render_signals(engine)

    with weather_tabs[2]:
        _render_projections(engine)

    with weather_tabs[3]:
        _render_history(engine)


def _render_live_scanner(engine):
    st.subheader("📡 Live NWS Forecast Scanner")

    col1, col2 = st.columns([3, 1])
    with col1:
        st.markdown("Fetches real-time forecasts from the National Weather Service for all 10 ForecastEx cities.")
    with col2:
        bankroll = st.number_input("Bankroll ($)", value=int(engine.bankroll), min_value=100, step=100)
        engine.bankroll = float(bankroll)

    if st.button("🔄 Scan All Markets", type="primary", use_container_width=True):
        with st.spinner("Fetching NWS forecasts for 10 cities..."):
            results = engine.scan_all_markets()
            engine.save_scan_to_db(results)
            st.session_state.weather_scan_results = results

    if 'weather_scan_results' in st.session_state:
        results = st.session_state.weather_scan_results
        summary = results['summary']

        c1, c2, c3, c4 = st.columns(4)
        c1.metric("Cities Scanned", summary['cities_scanned'])
        c2.metric("Opportunities", summary['total_opportunities'])
        c3.metric("Strong Signals", summary['strong_signals'])
        c4.metric("Edge Capital", f"${summary['total_edge_dollars']:.2f}")

        st.markdown("### City Forecasts")
        for city, market in results['markets'].items():
            fc = market['forecast']
            if fc.get('high'):
                with st.expander(f"**{city}**: {fc['high']:.0f}°F / {fc['low']:.0f}°F — {fc['conditions']} ({fc['date']})"):
                    cols = st.columns(3)
                    cols[0].metric("High", f"{fc['high']:.0f}°F")
                    cols[1].metric("Low", f"{fc['low']:.0f}°F")
                    cols[2].metric("Actionable Signals", market['actionable_signals'])

                    if market['best_opportunity']:
                        best = market['best_opportunity']
                        st.success(
                            f"**Best Trade:** {best['bracket']} | "
                            f"Edge: {best['edge']:.1%} | "
                            f"Size: ${best['position_size']:.2f} | "
                            f"{best['recommendation']}"
                        )

                    for sig in market['signals']:
                        if 'SKIP' not in sig['recommendation']:
                            zone_color = "🟢" if sig['tralse_zone'] == 'True' else "🟡"
                            st.markdown(
                                f"{zone_color} **{sig['bracket']}** — "
                                f"NWS: {sig['nws_probability']:.1%} vs Market: {sig['market_price']:.1%} | "
                                f"Edge: {sig['edge']:.1%} | Kelly: {sig['kelly_fraction']:.1%} | "
                                f"${sig['position_size']:.2f} — *{sig['recommendation']}*"
                            )

    kalshi_status = engine.get_kalshi_balance()
    if kalshi_status:
        st.markdown("---")
        st.markdown("### Kalshi Account")
        balance_cents = kalshi_status.get('balance', 0)
        st.metric("Kalshi Balance", f"${balance_cents / 100:.2f}")
    else:
        st.info("Kalshi API not connected. Using simulated market prices for edge calculation.")


def _render_signals(engine):
    st.subheader("📊 Trading Signals & Edge Analysis")

    if not engine.signals:
        st.info("Run the scanner first to generate signals.")
        return

    from engines.weather_prediction_engine import ETA, EPSILON

    actionable = [s for s in engine.signals if 'SKIP' not in s.recommendation]
    skipped = [s for s in engine.signals if 'SKIP' in s.recommendation]

    st.markdown(f"**{len(actionable)} actionable** signals out of {len(engine.signals)} total")

    if actionable:
        st.markdown("### Actionable Trades")
        for s in sorted(actionable, key=lambda x: abs(x.edge), reverse=True):
            edge_pct = s.edge * 100
            zone_icon = "🟢" if s.tralse_zone == 'True' else "🟡"
            conf_icon = "🔥" if s.confidence == 'high' else "📊"

            st.markdown(
                f"{zone_icon} {conf_icon} **{s.city}** ({s.date}) — {s.bracket_low}-{s.bracket_high}°F | "
                f"Edge: **{edge_pct:+.1f}%** | Kelly: {s.kelly_fraction:.1%} | "
                f"Position: **${s.position_size_dollars:.2f}** | {s.recommendation}"
            )

    st.markdown("### TI Tralse Zone Distribution")
    true_count = sum(1 for s in engine.signals if s.tralse_zone == 'True')
    tralse_count = sum(1 for s in engine.signals if s.tralse_zone == 'Tralse')
    c1, c2 = st.columns(2)
    c1.metric("True Zone (Tradeable)", true_count)
    c2.metric("Tralse Zone (Skip)", tralse_count)

    st.caption(f"TI Thresholds: eta={ETA:.4f} (manifestation), epsilon={EPSILON:.4f} (existence)")


def _render_projections(engine):
    st.subheader("💰 Monthly Earnings Projections")

    col1, col2 = st.columns(2)
    with col1:
        daily_trades = st.slider("Daily Trades", 1, 20, 5)
    with col2:
        avg_edge = st.slider("Average Edge (%)", 1, 20, 8) / 100.0

    projections = engine.estimate_monthly_earnings(daily_trades=daily_trades, avg_edge=avg_edge)

    st.markdown("### Assumptions")
    a = projections['assumptions']
    c1, c2, c3 = st.columns(3)
    c1.metric("Bankroll", f"${a['bankroll']:.0f}")
    c2.metric("Avg Edge", f"{a['avg_edge_pct']}%")
    c3.metric("Avg Position", f"${a['avg_position']:.0f}")

    st.markdown("### Linear Estimates")
    l = projections['linear_estimate']
    c1, c2, c3 = st.columns(3)
    c1.metric("Daily EV", f"${l['daily_ev']:.2f}")
    c2.metric("Monthly EV", f"${l['monthly_ev']:.2f}")
    c3.metric("Monthly Sharpe", f"{l['monthly_sharpe']:.2f}")

    st.markdown("### Compound Growth")
    c = projections['compound_estimate']
    c1, c2, c3 = st.columns(3)
    c1.metric("Month 1 Return", f"${c['monthly_return']:.2f}", f"{c['monthly_return_pct']}%")
    c2.metric("Month 3 Bankroll", f"${c['month_3_bankroll']:.2f}")
    c3.metric("Month 6 Bankroll", f"${c['month_6_bankroll']:.2f}")

    st.markdown("### Risk Metrics")
    r = projections['risk_metrics']
    c1, c2, c3 = st.columns(3)
    c1.metric("Max Daily Loss", f"${r['max_daily_loss']:.2f}")
    c2.metric("Kelly Max", f"{r['kelly_max_fraction']:.1%}")
    c3.metric("Ruin Probability", f"{r['ruin_probability_pct']:.1f}%")


def _render_history(engine):
    st.subheader("📈 Scan History & Performance")

    history = engine.get_scan_history(days=30)
    if history:
        st.markdown(f"**{len(history)} scans** recorded")
        for scan in history:
            st.markdown(
                f"**{scan['date']}** — {scan['cities_scanned']} cities, "
                f"{scan['opportunities']} opportunities ({scan['strong_signals']} strong), "
                f"Edge: ${scan['edge_dollars']:.2f}, Bankroll: ${scan['bankroll']:.2f}"
            )
    else:
        st.info("No scan history yet. Run a scan to start tracking.")

    st.markdown("### Historical Accuracy")
    accuracy = engine.get_historical_accuracy()
    if 'error' in accuracy:
        st.info("No historical accuracy data available yet. Accuracy tracking begins once actual temperatures are recorded.")
    else:
        if accuracy.get('city_accuracy'):
            for city, data in accuracy['city_accuracy'].items():
                st.markdown(
                    f"**{city}** — {data['total_forecasts']} forecasts, "
                    f"Avg High Error: {data['avg_high_error_f']}°F, "
                    f"Avg Low Error: {data['avg_low_error_f']}°F"
                )

        trading = accuracy.get('trading', {})
        if trading.get('total_signals', 0) > 0:
            st.markdown("### Trading Performance")
            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Total Trades", trading['total_signals'])
            c2.metric("Wins", trading.get('wins', 0))
            c3.metric("Losses", trading.get('losses', 0))
            c4.metric("Total P&L", f"${trading.get('total_pnl', 0):.2f}")
