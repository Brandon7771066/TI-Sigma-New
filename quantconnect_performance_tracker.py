"""
QuantConnect Performance Tracker
=================================
Track, compare, and analyze backtest results across algorithm versions
"""

import os
import json
import psycopg2
from datetime import datetime
from dataclasses import dataclass
from typing import Optional, Dict, List
import numpy as np

@dataclass
class BacktestResult:
    """Store backtest result data"""
    algorithm_version: str
    start_date: str
    end_date: str
    initial_capital: float
    final_value: float
    total_return_pct: float
    sharpe_ratio: float
    sortino_ratio: Optional[float] = None
    max_drawdown_pct: Optional[float] = None
    total_orders: Optional[int] = None
    winning_trades: Optional[int] = None
    losing_trades: Optional[int] = None
    win_rate_pct: Optional[float] = None
    avg_win_pct: Optional[float] = None
    avg_loss_pct: Optional[float] = None
    profit_factor: Optional[float] = None
    annual_return_pct: Optional[float] = None
    parameters: Optional[Dict] = None
    notes: Optional[str] = None
    jeff_time_weights: Optional[Dict] = None


class PerformanceTracker:
    """Track and analyze QuantConnect backtest performance"""
    
    def __init__(self):
        self.conn = psycopg2.connect(os.environ.get('DATABASE_URL'))
    
    def log_backtest(self, result: BacktestResult) -> int:
        """Log a new backtest result to the database"""
        
        cur = self.conn.cursor()
        
        cur.execute("""
            INSERT INTO quantconnect_backtest_results (
                algorithm_version, start_date, end_date,
                initial_capital, final_value, total_return_pct,
                sharpe_ratio, sortino_ratio, max_drawdown_pct,
                total_orders, winning_trades, losing_trades,
                win_rate_pct, avg_win_pct, avg_loss_pct,
                profit_factor, annual_return_pct,
                parameters, notes, jeff_time_weights
            ) VALUES (
                %s, %s, %s, %s, %s, %s, %s, %s, %s, %s,
                %s, %s, %s, %s, %s, %s, %s, %s, %s, %s
            )
            RETURNING id
        """, (
            result.algorithm_version,
            result.start_date,
            result.end_date,
            result.initial_capital,
            result.final_value,
            result.total_return_pct,
            result.sharpe_ratio,
            result.sortino_ratio,
            result.max_drawdown_pct,
            result.total_orders,
            result.winning_trades,
            result.losing_trades,
            result.win_rate_pct,
            result.avg_win_pct,
            result.avg_loss_pct,
            result.profit_factor,
            result.annual_return_pct,
            json.dumps(result.parameters) if result.parameters else None,
            result.notes,
            json.dumps(result.jeff_time_weights) if result.jeff_time_weights else None
        ))
        
        result_id = cur.fetchone()[0]
        self.conn.commit()
        
        print(f"Backtest logged with ID: {result_id}")
        return result_id
    
    def get_all_results(self) -> List[Dict]:
        """Get all backtest results"""
        cur = self.conn.cursor()
        cur.execute("""
            SELECT * FROM quantconnect_backtest_results
            ORDER BY run_date DESC
        """)
        
        columns = [desc[0] for desc in cur.description]
        results = []
        for row in cur.fetchall():
            results.append(dict(zip(columns, row)))
        
        return results
    
    def get_best_by_sharpe(self, limit: int = 5) -> List[Dict]:
        """Get top performing algorithms by Sharpe ratio"""
        cur = self.conn.cursor()
        cur.execute("""
            SELECT algorithm_version, total_return_pct, sharpe_ratio, 
                   total_orders, parameters, jeff_time_weights
            FROM quantconnect_backtest_results
            WHERE sharpe_ratio IS NOT NULL
            ORDER BY sharpe_ratio DESC
            LIMIT %s
        """, (limit,))
        
        columns = ['version', 'return_pct', 'sharpe', 'orders', 'params', 'jeff_time']
        return [dict(zip(columns, row)) for row in cur.fetchall()]
    
    def compare_versions(self) -> str:
        """Compare all algorithm versions"""
        results = self.get_all_results()
        
        if not results:
            return "No backtest results found."
        
        output = []
        output.append("="*80)
        output.append("QUANTCONNECT ALGORITHM PERFORMANCE COMPARISON")
        output.append("="*80)
        output.append("")
        
        for r in results:
            output.append(f"Version: {r['algorithm_version']}")
            output.append(f"  Period: {r['start_date']} to {r['end_date']}")
            output.append(f"  Return: {r['total_return_pct']:.2f}%")
            output.append(f"  Sharpe Ratio: {r['sharpe_ratio']:.4f}")
            output.append(f"  Total Orders: {r['total_orders']}")
            
            if r['jeff_time_weights']:
                weights = r['jeff_time_weights']
                output.append(f"  Jeff Time Weights: {weights}")
            
            if r['notes']:
                output.append(f"  Notes: {r['notes']}")
            
            output.append("")
        
        output.append("="*80)
        output.append("IMPROVEMENT ANALYSIS")
        output.append("="*80)
        
        if len(results) >= 2:
            latest = results[0]
            baseline = results[-1]
            
            sharpe_improvement = latest['sharpe_ratio'] - baseline['sharpe_ratio']
            return_improvement = latest['total_return_pct'] - baseline['total_return_pct']
            
            output.append(f"Baseline ({baseline['algorithm_version']}):")
            output.append(f"  Sharpe: {baseline['sharpe_ratio']:.4f}")
            output.append(f"  Return: {baseline['total_return_pct']:.2f}%")
            output.append("")
            output.append(f"Latest ({latest['algorithm_version']}):")
            output.append(f"  Sharpe: {latest['sharpe_ratio']:.4f}")
            output.append(f"  Return: {latest['total_return_pct']:.2f}%")
            output.append("")
            output.append(f"IMPROVEMENT:")
            output.append(f"  Sharpe: {sharpe_improvement:+.4f}")
            output.append(f"  Return: {return_improvement:+.2f}%")
        
        return "\n".join(output)
    
    def suggest_improvements(self) -> str:
        """Suggest algorithm improvements based on past results"""
        results = self.get_all_results()
        
        suggestions = []
        suggestions.append("="*80)
        suggestions.append("ALGORITHM IMPROVEMENT SUGGESTIONS")
        suggestions.append("="*80)
        suggestions.append("")
        
        if not results:
            suggestions.append("No backtest data yet. Run some backtests first!")
            return "\n".join(suggestions)
        
        latest = results[0]
        sharpe = latest['sharpe_ratio']
        
        suggestions.append(f"Current Best Sharpe: {sharpe:.4f}")
        suggestions.append("")
        
        if sharpe < 0.5:
            suggestions.append("Target: Basic profitability (Sharpe > 0.5)")
            suggestions.append("  - Reduce position sizes")
            suggestions.append("  - Add stricter entry criteria")
            suggestions.append("  - Increase t₃ (cosmological) weight for trend confirmation")
        
        elif sharpe < 1.0:
            suggestions.append("Target: Good strategy (Sharpe > 1.0)")
            suggestions.append("  - Fine-tune temporal dimension weights")
            suggestions.append("  - Consider adding stop-losses")
            suggestions.append("  - Optimize t₁ lookback period (try 2-5 days)")
            suggestions.append("  - Test different Love dimension calculations")
        
        elif sharpe < 1.5:
            suggestions.append("Target: Excellent strategy (Sharpe > 1.5)")
            suggestions.append("  - Add regime detection (bull/bear markets)")
            suggestions.append("  - Implement dynamic position sizing")
            suggestions.append("  - Consider volatility targeting")
            suggestions.append("  - Test sector rotation based on GILE")
        
        else:
            suggestions.append("EXCELLENT PERFORMANCE!")
            suggestions.append("  - Monitor for overfitting")
            suggestions.append("  - Test on out-of-sample data")
            suggestions.append("  - Consider paper trading before live")
        
        suggestions.append("")
        suggestions.append("="*80)
        suggestions.append("3D JEFF TIME OPTIMIZATION GRID")
        suggestions.append("="*80)
        suggestions.append("")
        suggestions.append("Weight combinations to test:")
        suggestions.append("")
        
        weight_grids = [
            {'t1': 0.20, 't2': 0.40, 't3': 0.25, 'L': 0.15, 'label': 'Jeff-Heavy'},
            {'t1': 0.30, 't2': 0.30, 't3': 0.25, 'L': 0.15, 'label': 'Balanced'},
            {'t1': 0.25, 't2': 0.25, 't3': 0.35, 'L': 0.15, 'label': 'Trend-Heavy'},
            {'t1': 0.25, 't2': 0.35, 't3': 0.20, 'L': 0.20, 'label': 'Love-Heavy'},
            {'t1': 0.15, 't2': 0.45, 't3': 0.25, 'L': 0.15, 'label': 'Pure-Jeff'},
        ]
        
        for w in weight_grids:
            suggestions.append(f"  {w['label']}: t₁={w['t1']:.2f} t₂={w['t2']:.2f} t₃={w['t3']:.2f} L={w['L']:.2f}")
        
        return "\n".join(suggestions)
    
    def close(self):
        self.conn.close()


def render_performance_dashboard():
    """Render Streamlit dashboard for performance tracking"""
    import streamlit as st
    
    st.markdown("## QuantConnect Performance Tracker")
    st.markdown("*Track, compare, and optimize your TI Framework algorithms*")
    
    tracker = PerformanceTracker()
    
    tab1, tab2, tab3 = st.tabs(["Results", "Log New", "Suggestions"])
    
    with tab1:
        st.markdown("### All Backtest Results")
        results = tracker.get_all_results()
        
        if results:
            for r in results:
                with st.expander(f"{r['algorithm_version']} - Sharpe: {r['sharpe_ratio']:.4f}"):
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Total Return", f"{r['total_return_pct']:.2f}%")
                    with col2:
                        st.metric("Sharpe Ratio", f"{r['sharpe_ratio']:.4f}")
                    with col3:
                        st.metric("Orders", r['total_orders'])
                    
                    if r['notes']:
                        st.info(r['notes'])
        else:
            st.info("No backtest results yet. Log your first backtest!")
    
    with tab2:
        st.markdown("### Log New Backtest")
        
        with st.form("log_backtest"):
            version = st.text_input("Algorithm Version", "V3_JeffTime")
            col1, col2 = st.columns(2)
            with col1:
                start = st.date_input("Start Date")
                initial = st.number_input("Initial Capital", value=100000)
                ret = st.number_input("Total Return %", value=0.0)
            with col2:
                end = st.date_input("End Date")
                final = st.number_input("Final Value", value=100000)
                sharpe = st.number_input("Sharpe Ratio", value=0.0, format="%.4f")
            
            orders = st.number_input("Total Orders", value=0)
            notes = st.text_area("Notes")
            
            submitted = st.form_submit_button("Log Backtest")
            
            if submitted:
                result = BacktestResult(
                    algorithm_version=version,
                    start_date=str(start),
                    end_date=str(end),
                    initial_capital=initial,
                    final_value=final,
                    total_return_pct=ret,
                    sharpe_ratio=sharpe,
                    total_orders=orders,
                    notes=notes
                )
                tracker.log_backtest(result)
                st.success("Backtest logged!")
                st.rerun()
    
    with tab3:
        st.markdown("### Improvement Suggestions")
        suggestions = tracker.suggest_improvements()
        st.code(suggestions, language="text")
    
    tracker.close()


if __name__ == "__main__":
    tracker = PerformanceTracker()
    
    print(tracker.compare_versions())
    print()
    print(tracker.suggest_improvements())
    
    tracker.close()
