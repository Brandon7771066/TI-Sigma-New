"""
GSA Infrastructure Status Dashboard

Audits the entire Grand Stock Algorithm infrastructure,
shows current status of all stock market components,
and provides a clear path forward.
"""

import streamlit as st
import os
import sys
import importlib
import numpy as np
from datetime import datetime
from typing import Dict, List, Tuple, Optional


GSA_COMPONENTS = [
    {
        "name": "GSA Core Engine",
        "file": "gsa_core.py",
        "module": "gsa_core",
        "description": "Core Ξ(E) = A(t) · κ(t,τ) · C(t) metrics, regime classification, PD scoring",
        "category": "Core",
    },
    {
        "name": "Grand Stock Algorithm",
        "file": "grand_stock_algorithm.py",
        "module": "grand_stock_algorithm",
        "description": "Higher-level GSA with backtest engine, options pricing, data pipeline",
        "category": "Core",
    },
    {
        "name": "Alpaca Paper Trader",
        "file": "alpaca_paper_trader.py",
        "module": "alpaca_paper_trader",
        "description": "Paper trading via Alpaca API with green-light stock universe",
        "category": "Trading",
    },
    {
        "name": "Daily Signal Scheduler",
        "file": "daily_signal_scheduler.py",
        "module": "daily_signal_scheduler",
        "description": "Scheduled signal generation at market open/close via APScheduler",
        "category": "Trading",
    },
    {
        "name": "Collective2 Integration",
        "file": "collective2/collective2_integration.py",
        "module": "collective2.collective2_integration",
        "description": "C2 API v3 signal submission and position management",
        "category": "Trading",
    },
    {
        "name": "ARTA Signal Runner",
        "file": "collective2/arta_signal_runner.py",
        "module": "collective2.arta_signal_runner",
        "description": "ARTA algorithm signal runner for Collective2",
        "category": "Trading",
    },
    {
        "name": "GSA-C2 Bridge",
        "file": "collective2/gsa_c2_bridge.py",
        "module": "collective2.gsa_c2_bridge",
        "description": "Bridge between GSA signals and Collective2 format",
        "category": "Trading",
    },
    {
        "name": "Stock Data Cache",
        "file": "stock_data_cache.py",
        "module": "stock_data_cache",
        "description": "Local caching layer for stock price data",
        "category": "Data",
    },
    {
        "name": "Alpha Vantage Integration",
        "file": "alpha_vantage_integration.py",
        "module": "alpha_vantage_integration",
        "description": "Alpha Vantage API for real-time quotes, RSI, SMA, fundamentals",
        "category": "Data",
    },
    {
        "name": "Prediction Replay Engine",
        "file": "prediction_replay_engine.py",
        "module": "prediction_replay_engine",
        "description": "Replay and backtest historical predictions",
        "category": "Validation",
    },
    {
        "name": "GSA Comprehensive Validator",
        "file": "gsa_comprehensive_validator.py",
        "module": "gsa_comprehensive_validator",
        "description": "Full validation suite: sector tests, crisis stress, slippage, regime accuracy",
        "category": "Validation",
    },
    {
        "name": "VectorBT Backtest",
        "file": "vectorbt_gsa_backtest.py",
        "module": "vectorbt_gsa_backtest",
        "description": "VectorBT-powered backtesting engine",
        "category": "Validation",
    },
    {
        "name": "QuantConnect Algorithm (v11 OPTICAL)",
        "file": "ti_quantconnect_v11_OPTICAL.py",
        "module": "ti_quantconnect_v11_OPTICAL",
        "description": "QuantConnect algorithm versions (v5, v7, v9, v11)",
        "category": "Platform",
    },
    {
        "name": "GSA-QC Bridge",
        "file": "gsa_qc_bridge.py",
        "module": "gsa_qc_bridge",
        "description": "Bridge between GSA core and QuantConnect platform",
        "category": "Platform",
    },
    {
        "name": "Strawberry Fields (Quantum Photonic)",
        "file": "ti_strawberry_fields.py",
        "module": "ti_strawberry_fields",
        "description": "Quantum photonic simulator for market regime signals",
        "category": "Advanced",
    },
    {
        "name": "Fractal Universe Engine",
        "file": "fractal_universe_engine.py",
        "module": "fractal_universe_engine",
        "description": "Hurst exponent, Kleiber scaling, 42 orders fractal analysis",
        "category": "Advanced",
    },
    {
        "name": "TI Evidence Registry",
        "file": "ti_evidence_registry.py",
        "module": "ti_evidence_registry",
        "description": "Evidence tracking and scoring for TI predictions",
        "category": "Advanced",
    },
]

API_KEYS = [
    {
        "name": "Alpha Vantage API Key",
        "env_var": "ALPHA_VANTAGE_API_KEY",
        "service": "Alpha Vantage",
        "purpose": "Real-time quotes, fundamentals, technical indicators",
        "free_tier": "Yes (25 req/day)",
    },
    {
        "name": "Alpaca API Key ID",
        "env_var": "APCA_API_KEY_ID",
        "service": "Alpaca Markets",
        "purpose": "Paper/live trading authentication",
        "free_tier": "Yes (paper trading free)",
    },
    {
        "name": "Alpaca API Secret Key",
        "env_var": "APCA_API_SECRET_KEY",
        "service": "Alpaca Markets",
        "purpose": "Paper/live trading authentication",
        "free_tier": "Yes (paper trading free)",
    },
    {
        "name": "Collective2 API Key",
        "env_var": "COLLECTIVE2_API_KEY",
        "service": "Collective2",
        "purpose": "Signal submission to C2 platform",
        "free_tier": "No ($99/mo for system)",
    },
    {
        "name": "Collective2 System ID",
        "env_var": "COLLECTIVE2_SYSTEM_ID",
        "service": "Collective2",
        "purpose": "Target trading system identifier",
        "free_tier": "No ($99/mo for system)",
    },
]


def check_file_status(filepath: str) -> Tuple[bool, Optional[datetime]]:
    """Check if file exists and get modification time."""
    if os.path.exists(filepath):
        mtime = os.path.getmtime(filepath)
        return True, datetime.fromtimestamp(mtime)
    return False, None


def check_import_status(module_name: str) -> Tuple[bool, str]:
    """Try to import a module and return success status and error message."""
    try:
        if module_name in sys.modules:
            importlib.reload(sys.modules[module_name])
        else:
            importlib.import_module(module_name)
        return True, ""
    except Exception as e:
        return False, str(e)[:120]


def get_status_indicator(exists: bool, imports: bool) -> Tuple[str, str]:
    """Return emoji and label for traffic light status."""
    if not exists:
        return "🔴", "Missing"
    if not imports:
        return "🟡", "Import Error"
    return "🟢", "Working"


def render_infrastructure_overview():
    """Render the infrastructure overview table with status checks."""
    st.header("📊 Infrastructure Overview")

    categories = {}
    for comp in GSA_COMPONENTS:
        cat = comp["category"]
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(comp)

    total_green = 0
    total_yellow = 0
    total_red = 0

    for category, components in categories.items():
        st.subheader(f"{'⚙️' if category == 'Core' else '📈' if category == 'Trading' else '💾' if category == 'Data' else '✅' if category == 'Validation' else '🌐' if category == 'Platform' else '🔬'} {category}")

        rows = []
        for comp in components:
            exists, mtime = check_file_status(comp["file"])
            imports_ok, error_msg = check_import_status(comp["module"]) if exists else (False, "File not found")
            indicator, status_label = get_status_indicator(exists, imports_ok)

            if indicator == "🟢":
                total_green += 1
            elif indicator == "🟡":
                total_yellow += 1
            else:
                total_red += 1

            rows.append({
                "Status": indicator,
                "Component": comp["name"],
                "File": comp["file"],
                "State": status_label,
                "Last Modified": mtime.strftime("%Y-%m-%d %H:%M") if mtime else "N/A",
                "Description": comp["description"],
            })

        st.dataframe(
            rows,
            use_container_width=True,
            hide_index=True,
            column_config={
                "Status": st.column_config.TextColumn(width="small"),
                "Component": st.column_config.TextColumn(width="medium"),
                "File": st.column_config.TextColumn(width="medium"),
                "State": st.column_config.TextColumn(width="small"),
                "Last Modified": st.column_config.TextColumn(width="medium"),
                "Description": st.column_config.TextColumn(width="large"),
            },
        )

    return total_green, total_yellow, total_red


def render_status_summary(green: int, yellow: int, red: int):
    """Render traffic light summary metrics."""
    st.header("🚦 Current Status Summary")

    total = green + yellow + red
    health_pct = (green / total * 100) if total > 0 else 0

    col1, col2, col3, col4 = st.columns(4)
    with col1:
        st.metric("🟢 Working", green)
    with col2:
        st.metric("🟡 Import Errors", yellow)
    with col3:
        st.metric("🔴 Missing", red)
    with col4:
        st.metric("Health Score", f"{health_pct:.0f}%")

    if health_pct >= 80:
        st.success(f"Infrastructure health: **{health_pct:.0f}%** — Most components operational")
    elif health_pct >= 50:
        st.warning(f"Infrastructure health: **{health_pct:.0f}%** — Some components need attention")
    else:
        st.error(f"Infrastructure health: **{health_pct:.0f}%** — Significant issues detected")


def render_api_keys_status():
    """Render API keys configuration status."""
    st.header("🔑 API Keys Status")

    rows = []
    configured_count = 0

    for key_info in API_KEYS:
        value = os.environ.get(key_info["env_var"])
        is_set = value is not None and len(value) > 0

        if is_set and value is not None:
            configured_count += 1
            masked = value[:4] + "..." + value[-4:] if len(value) > 8 else "****"
            status = "✅ Configured"
        else:
            masked = "—"
            status = "❌ Not Set"

        rows.append({
            "Status": status,
            "Key": key_info["env_var"],
            "Service": key_info["service"],
            "Value": masked,
            "Purpose": key_info["purpose"],
            "Free Tier": key_info["free_tier"],
        })

    st.dataframe(rows, use_container_width=True, hide_index=True)

    total_keys = len(API_KEYS)
    if configured_count == total_keys:
        st.success(f"All {total_keys} API keys configured")
    elif configured_count > 0:
        st.warning(f"{configured_count}/{total_keys} API keys configured. Missing keys will limit functionality.")
    else:
        st.info("No API keys configured yet. Paper trading with Alpaca is free — start there!")


def render_gsa_core_test():
    """Render interactive GSA core test with sample data."""
    st.header("🧪 GSA Core Quick Test")

    st.markdown(
        "Run a quick test of the GSA core engine with synthetic price data "
        "to verify Ξ metrics calculation, regime classification, and signal generation."
    )

    col1, col2 = st.columns(2)
    with col1:
        num_days = st.slider("Number of trading days", 60, 252, 120, key="gsa_test_days")
    with col2:
        volatility = st.slider("Annualized volatility (%)", 10, 80, 25, key="gsa_test_vol")

    if st.button("▶️ Run GSA Core Test", type="primary", key="run_gsa_test"):
        try:
            from gsa_core import GSACore, MarketRegime

            gsa = GSACore(lookback_short=7, lookback_long=60)

            np.random.seed(42)
            daily_vol = volatility / 100 / np.sqrt(252)
            drift = 0.0002
            returns_decimal = np.random.normal(drift, daily_vol, num_days)
            prices = 100 * np.cumprod(1 + returns_decimal)
            returns_pct = returns_decimal * 100

            xi = gsa.compute_xi_metrics(returns_pct, prices)
            gile = gsa.compute_gile(returns_pct, prices)

            vol_recent = float(np.std(returns_pct[-7:])) if len(returns_pct) >= 7 else 1.0
            vol_long = float(np.std(returns_pct[-60:])) if len(returns_pct) >= 60 else 1.0
            vol_ratio = vol_recent / max(vol_long, 0.01)

            regime, regime_conf, c_rate = gsa.classify_regime(xi.pd, xi.constraint, vol_ratio)
            signal = gsa.generate_signal(xi, gile, regime, regime_conf)

            st.success("GSA Core engine test completed successfully!")

            col_a, col_b, col_c = st.columns(3)

            with col_a:
                st.subheader("Ξ Metrics")
                st.markdown(f"""
| Metric | Value |
|--------|-------|
| Amplitude A(t) | `{xi.amplitude:.4f}` |
| Memory Kernel κ(t,τ) | `{xi.memory_kernel:.4f}` |
| Constraint C(t) | `{xi.constraint:.4f}` |
| Ξ Unsigned | `{xi.xi_unsigned:.4f}` |
| Ξ Signed | `{xi.xi_signed:.4f}` |
| PD Score | `{xi.pd:.4f}` |
""")

            with col_b:
                st.subheader("GILE Score")
                st.markdown(f"""
| Component | Value |
|-----------|-------|
| Goodness (G) | `{gile.goodness:.4f}` |
| Intuition (I) | `{gile.intuition:.4f}` |
| Love (L) | `{gile.love:.4f}` |
| Environment (E) | `{gile.environment:.4f}` |
| **Composite** | **`{gile.composite:.4f}`** |
""")

            with col_c:
                st.subheader("Signal Output")
                regime_colors = {
                    MarketRegime.EXPANSION: "🟢 Expansion",
                    MarketRegime.COMPRESSION: "🟡 Compression",
                    MarketRegime.FRACTURE: "🔴 Fracture",
                    MarketRegime.RESET: "🔵 Reset",
                }
                signal_colors = {
                    "strong_buy": "🟢",
                    "buy": "🟢",
                    "hold": "🟡",
                    "sell": "🔴",
                    "strong_sell": "🔴",
                }
                st.markdown(f"""
| Output | Value |
|--------|-------|
| Regime | {regime_colors.get(regime, regime.value)} |
| Regime Confidence | `{regime_conf:.2%}` |
| Signal | {signal_colors.get(signal.action, '⚪')} **{signal.action.upper()}** |
| Signal Confidence | `{signal.confidence:.2%}` |
| Constraint Rate | `{c_rate:.4f}` |
""")

            if signal.reasons:
                st.subheader("Signal Reasoning")
                for reason in signal.reasons:
                    st.markdown(f"- {reason}")

            st.subheader("Price Chart (Synthetic Data)")
            chart_data = {"Price": prices, "Day": list(range(len(prices)))}
            st.line_chart(data={"Price": prices})

        except ImportError as e:
            st.error(f"Cannot import GSA Core: {e}")
        except Exception as e:
            st.error(f"Test failed: {e}")


def render_backtest_summary():
    """Render backtest results summary from database or signal log."""
    st.header("📈 Backtest & Signal History")

    signal_file = "data/daily_signals.json"
    if os.path.exists(signal_file):
        try:
            import json
            with open(signal_file, "r") as f:
                history = json.load(f)

            signals_list = history.get("signals", [])
            if signals_list:
                st.success(f"Found {len(signals_list)} daily signal records")

                latest = signals_list[-1]
                col1, col2, col3 = st.columns(3)
                with col1:
                    st.metric("Latest Signal Date", latest.get("date", "N/A"))
                with col2:
                    st.metric("Buy Signals", latest.get("buy_count", 0))
                with col3:
                    st.metric("Sell Signals", latest.get("sell_count", 0))

                if latest.get("top_buys"):
                    st.subheader("Latest Top Buy Signals")
                    buy_rows = []
                    for sig in latest["top_buys"]:
                        buy_rows.append({
                            "Ticker": sig.get("ticker", ""),
                            "Action": sig.get("action", ""),
                            "GILE": f"{sig.get('gile', 0):.3f}",
                            "Confidence": f"{sig.get('confidence', 0):.3f}",
                            "Price": f"${sig.get('price', 0):.2f}",
                            "Regime": sig.get("regime", ""),
                        })
                    st.dataframe(buy_rows, use_container_width=True, hide_index=True)

                with st.expander("Signal History Timeline"):
                    history_rows = []
                    for entry in signals_list[-30:]:
                        history_rows.append({
                            "Date": entry.get("date", ""),
                            "Time": entry.get("time", ""),
                            "Total": entry.get("total_signals", 0),
                            "Buys": entry.get("buy_count", 0),
                            "Sells": entry.get("sell_count", 0),
                        })
                    st.dataframe(history_rows, use_container_width=True, hide_index=True)
            else:
                st.info("Signal history file exists but contains no records yet.")
        except Exception as e:
            st.warning(f"Could not parse signal history: {e}")
    else:
        st.info(
            "No signal history found. Run the daily signal scheduler to generate signals:\n\n"
            "`python daily_signal_scheduler.py --once`"
        )

    try:
        database_url = os.environ.get("DATABASE_URL")
        if database_url:
            import psycopg2
            conn = psycopg2.connect(database_url)
            cur = conn.cursor()
            cur.execute("""
                SELECT table_name FROM information_schema.tables 
                WHERE table_schema = 'public' 
                AND table_name LIKE '%backtest%'
            """)
            backtest_tables = cur.fetchall()
            if backtest_tables:
                st.subheader("Database Backtest Tables")
                for table in backtest_tables:
                    st.markdown(f"- `{table[0]}`")
            cur.close()
            conn.close()
    except Exception:
        pass


def render_path_forward():
    """Render the step-by-step path forward."""
    st.header("🗺️ Path Forward")

    st.markdown(
        "Follow these steps to go from validated algorithm to live paper trading. "
        "**All steps are achievable for free.**"
    )

    steps = [
        {
            "number": 1,
            "title": "Validate GSA Core with Historical Data",
            "description": (
                "Run the comprehensive validator across all sectors and crisis periods. "
                "Verify Sharpe ratio > 1.0 and fracture detection during known crashes."
            ),
            "command": "python gsa_comprehensive_validator.py",
            "status": "ready",
            "cost": "Free",
        },
        {
            "number": 2,
            "title": "Set Up Alpaca Paper Trading Account",
            "description": (
                "Create a free Alpaca paper trading account at alpaca.markets. "
                "Get API keys and set APCA_API_KEY_ID and APCA_API_SECRET_KEY."
            ),
            "command": None,
            "status": "ready",
            "cost": "Free",
        },
        {
            "number": 3,
            "title": "Connect Daily Signal Scheduler",
            "description": (
                "Start the daily signal scheduler to generate GSA signals at market open. "
                "Signals are logged to data/daily_signals.json for review."
            ),
            "command": "python daily_signal_scheduler.py",
            "status": "ready",
            "cost": "Free",
        },
        {
            "number": 4,
            "title": "Run 30-Day Paper Trading Trial",
            "description": (
                "Execute paper trades via Alpaca for 30 trading days. "
                "Track P&L, win rate, and regime detection accuracy. "
                "Target: Sharpe > 1.0, Max Drawdown < 15%."
            ),
            "command": "python alpaca_paper_trader.py",
            "status": "pending",
            "cost": "Free",
        },
        {
            "number": 5,
            "title": "Evaluate Performance and Iterate",
            "description": (
                "Review 30-day results. If Sharpe > 1.0 and drawdown < 15%, "
                "consider Collective2 signal publishing or live trading. "
                "Iterate on GILE weights and regime thresholds based on results."
            ),
            "command": None,
            "status": "pending",
            "cost": "Free (C2: $99/mo optional)",
        },
    ]

    for step in steps:
        status_icon = "✅" if step["status"] == "complete" else "🔲" if step["status"] == "ready" else "⬜"
        with st.expander(f"{status_icon} Step {step['number']}: {step['title']} — {step['cost']}"):
            st.markdown(step["description"])
            if step["command"]:
                st.code(step["command"], language="bash")

    st.info(
        "💡 **Budget Note:** Steps 1-4 are completely free. Alpaca paper trading costs nothing. "
        "Alpha Vantage offers 25 free API calls/day. Collective2 ($99/mo) is optional and only "
        "needed if you want to publish signals for subscribers."
    )


def render_quick_links():
    """Render quick reference links to external docs."""
    st.header("🔗 Quick Links & Resources")

    col1, col2, col3 = st.columns(3)

    with col1:
        st.subheader("Alpaca Markets")
        st.markdown("""
- [Dashboard](https://app.alpaca.markets/paper/dashboard/overview)
- [API Documentation](https://docs.alpaca.markets/)
- [Paper Trading Guide](https://docs.alpaca.markets/docs/paper-trading)
- [Python SDK](https://github.com/alpacahq/alpaca-trade-api-python)
""")

    with col2:
        st.subheader("QuantConnect")
        st.markdown("""
- [Algorithm Lab](https://www.quantconnect.com/terminal)
- [Documentation](https://www.quantconnect.com/docs)
- [Lean Engine (GitHub)](https://github.com/QuantConnect/Lean)
- [Community Forum](https://www.quantconnect.com/forum)
""")

    with col3:
        st.subheader("Collective2")
        st.markdown("""
- [Dashboard](https://collective2.com/)
- [API v3 Documentation](https://collective2.com/api-docs/latest)
- [Signal Entry Guide](https://collective2.com/help-signal-entry)
- [System Setup](https://collective2.com/create-system)
""")

    st.divider()

    col4, col5 = st.columns(2)
    with col4:
        st.subheader("Data Providers")
        st.markdown("""
- [Alpha Vantage (Free API)](https://www.alphavantage.co/support/#api-key)
- [Yahoo Finance (yfinance)](https://github.com/ranaroussi/yfinance)
- [VectorBT Docs](https://vectorbt.dev/)
""")

    with col5:
        st.subheader("GSA Framework Reference")
        st.markdown("""
- **Ξ(E) = A(t) · κ(t,τ) · C(t)** — Existence Intensity
- **GILE** — Goodness, Intuition, Love, Environment scoring
- **Regimes** — Expansion / Compression / Fracture / Reset
- **PD Score** — Probability Distribution [-3, +2]
""")


def render():
    """Main render function for the GSA Infrastructure Status dashboard."""
    st.title("📊 GSA Infrastructure Status Dashboard")
    st.caption("Grand Stock Algorithm — Infrastructure Audit & Path Forward")

    tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs([
        "🏗️ Infrastructure",
        "🔑 API Keys",
        "🧪 Core Test",
        "📈 Signals & Backtests",
        "🗺️ Path Forward",
        "🔗 Resources",
    ])

    with tab1:
        green, yellow, red = render_infrastructure_overview()
        st.divider()
        render_status_summary(green, yellow, red)

    with tab2:
        render_api_keys_status()

    with tab3:
        render_gsa_core_test()

    with tab4:
        render_backtest_summary()

    with tab5:
        render_path_forward()

    with tab6:
        render_quick_links()


render()
