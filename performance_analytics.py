"""
Performance Analytics Module
Calculates advanced metrics: Sharpe ratio, alpha, beta, information ratio
Compares TI Framework vs S&P 500 and broker recommendations
"""

import numpy as np
import psycopg2
from psycopg2.extras import RealDictCursor
import os
from datetime import datetime, timedelta
from typing import Dict, List, Tuple
import requests
import statistics

class PerformanceAnalytics:
    """
    Calculate portfolio performance metrics for TI Framework predictions
    """
    
    def __init__(self):
        self.alpha_vantage_key = os.getenv('ALPHA_VANTAGE_API_KEY')
        self.db_params = {
            'host': os.getenv('PGHOST'),
            'database': os.getenv('PGDATABASE'),
            'user': os.getenv('PGUSER'),
            'password': os.getenv('PGPASSWORD'),
            'port': os.getenv('PGPORT')
        }
        self.risk_free_rate = 0.045  # 4.5% annual risk-free rate (approx current 10Y Treasury)
    
    def get_db_connection(self):
        """Get database connection"""
        return psycopg2.connect(**self.db_params)
    
    def get_sp500_returns(self, start_date: datetime, end_date: datetime) -> List[float]:
        """
        Get S&P 500 daily returns for benchmark comparison
        
        Args:
            start_date: Start date
            end_date: End date
        
        Returns: List of daily returns (%)
        """
        try:
            url = "https://www.alphavantage.co/query"
            params = {
                'function': 'TIME_SERIES_DAILY',
                'symbol': 'SPY',  # S&P 500 ETF
                'apikey': self.alpha_vantage_key,
                'outputsize': 'full'
            }
            
            response = requests.get(url, params=params, timeout=20)
            data = response.json()
            
            if 'Time Series (Daily)' not in data:
                print(f"⚠️  No S&P 500 data available")
                return []
            
            time_series = data['Time Series (Daily)']
            
            # Filter dates within range
            prices = []
            dates = sorted(time_series.keys())
            
            for date_str in dates:
                date = datetime.strptime(date_str, '%Y-%m-%d')
                if start_date <= date <= end_date:
                    prices.append((date, float(time_series[date_str]['4. close'])))
            
            # Calculate daily returns
            returns = []
            for i in range(1, len(prices)):
                daily_return = ((prices[i][1] - prices[i-1][1]) / prices[i-1][1]) * 100
                returns.append(daily_return)
            
            return returns
        
        except Exception as e:
            print(f"❌ Error fetching S&P 500 data: {e}")
            return []
    
    def calculate_sharpe_ratio(self, returns: List[float], 
                               periods_per_year: int = 252) -> float:
        """
        Calculate Sharpe Ratio
        
        Args:
            returns: List of period returns (%)
            periods_per_year: Number of periods in a year (252 for daily, 12 for monthly)
        
        Returns: Sharpe ratio
        """
        if not returns or len(returns) == 0:
            return 0.0
        
        # Convert % returns to decimal
        returns_decimal = [r / 100 for r in returns]
        
        # Average return
        avg_return = statistics.mean(returns_decimal)
        
        # Standard deviation
        if len(returns_decimal) > 1:
            std_dev = statistics.stdev(returns_decimal)
        else:
            std_dev = 0.0
        
        if std_dev == 0:
            return 0.0
        
        # Annualize
        annual_return = avg_return * periods_per_year
        annual_std_dev = std_dev * np.sqrt(periods_per_year)
        
        # Risk-free rate (annualized)
        risk_free_annual = self.risk_free_rate
        
        # Sharpe ratio = (Return - RiskFree) / StdDev
        sharpe = (annual_return - risk_free_annual) / annual_std_dev
        
        return sharpe
    
    def calculate_alpha_beta(self, portfolio_returns: List[float], 
                            market_returns: List[float]) -> Tuple[float, float]:
        """
        Calculate Alpha and Beta vs market (S&P 500)
        
        Args:
            portfolio_returns: TI Framework returns (%)
            market_returns: S&P 500 returns (%)
        
        Returns: (alpha, beta)
        """
        if not portfolio_returns or not market_returns:
            return 0.0, 0.0
        
        # Ensure same length
        min_len = min(len(portfolio_returns), len(market_returns))
        portfolio_returns = portfolio_returns[:min_len]
        market_returns = market_returns[:min_len]
        
        # Convert to decimal
        port_decimal = [r / 100 for r in portfolio_returns]
        mkt_decimal = [r / 100 for r in market_returns]
        
        # Calculate covariance and variance
        if len(port_decimal) > 1:
            # Beta = Cov(portfolio, market) / Var(market)
            covariance = np.cov(port_decimal, mkt_decimal)[0][1]
            market_variance = np.var(mkt_decimal)
            
            if market_variance > 0:
                beta = covariance / market_variance
            else:
                beta = 0.0
            
            # Alpha = Avg_Portfolio_Return - (RiskFree + Beta * (Avg_Market_Return - RiskFree))
            avg_port = statistics.mean(port_decimal)
            avg_mkt = statistics.mean(mkt_decimal)
            
            # Annualize (assuming daily returns)
            annual_port = avg_port * 252
            annual_mkt = avg_mkt * 252
            
            alpha = annual_port - (self.risk_free_rate + beta * (annual_mkt - self.risk_free_rate))
        else:
            alpha = 0.0
            beta = 0.0
        
        return alpha, beta
    
    def calculate_information_ratio(self, portfolio_returns: List[float], 
                                    benchmark_returns: List[float]) -> float:
        """
        Calculate Information Ratio (active return / tracking error)
        
        Args:
            portfolio_returns: TI Framework returns
            benchmark_returns: Broker/S&P 500 returns
        
        Returns: Information ratio
        """
        if not portfolio_returns or not benchmark_returns:
            return 0.0
        
        # Ensure same length
        min_len = min(len(portfolio_returns), len(benchmark_returns))
        portfolio_returns = portfolio_returns[:min_len]
        benchmark_returns = benchmark_returns[:min_len]
        
        # Active returns (portfolio - benchmark)
        active_returns = [p - b for p, b in zip(portfolio_returns, benchmark_returns)]
        
        if len(active_returns) > 1:
            avg_active = statistics.mean(active_returns)
            tracking_error = statistics.stdev(active_returns)
            
            if tracking_error > 0:
                information_ratio = (avg_active / tracking_error) * np.sqrt(252)  # Annualized
            else:
                information_ratio = 0.0
        else:
            information_ratio = 0.0
        
        return information_ratio
    
    def calculate_max_drawdown(self, returns: List[float]) -> float:
        """
        Calculate maximum drawdown (%)
        
        Args:
            returns: List of returns (%)
        
        Returns: Max drawdown as positive %
        """
        if not returns:
            return 0.0
        
        # Calculate cumulative returns
        cumulative = [100.0]  # Start with $100
        for r in returns:
            cumulative.append(cumulative[-1] * (1 + r / 100))
        
        # Find max drawdown
        max_dd = 0.0
        peak = cumulative[0]
        
        for value in cumulative:
            if value > peak:
                peak = value
            
            drawdown = ((peak - value) / peak) * 100
            if drawdown > max_dd:
                max_dd = drawdown
        
        return max_dd
    
    def calculate_win_rate(self, predictions: List[Dict]) -> Dict:
        """
        Calculate win rate statistics
        
        Args:
            predictions: List of prediction dicts with outcomes
        
        Returns: {
            'win_rate': float,
            'wins': int,
            'losses': int,
            'total': int,
            'avg_win': float,
            'avg_loss': float,
            'win_loss_ratio': float
        }
        """
        wins = []
        losses = []
        
        for pred in predictions:
            if 'is_correct' in pred and pred['is_correct'] is not None:
                if 'return_pct' in pred and pred['return_pct'] is not None:
                    if pred['is_correct']:
                        wins.append(pred['return_pct'])
                    else:
                        losses.append(pred['return_pct'])
        
        total = len(wins) + len(losses)
        win_rate = (len(wins) / total * 100) if total > 0 else 0.0
        
        avg_win = statistics.mean(wins) if wins else 0.0
        avg_loss = statistics.mean(losses) if losses else 0.0
        win_loss_ratio = (avg_win / abs(avg_loss)) if avg_loss != 0 else 0.0
        
        return {
            'win_rate': win_rate,
            'wins': len(wins),
            'losses': len(losses),
            'total': total,
            'avg_win': avg_win,
            'avg_loss': avg_loss,
            'win_loss_ratio': win_loss_ratio
        }
    
    def generate_performance_report(self, predictions: List[Dict], 
                                    start_date: datetime, 
                                    end_date: datetime) -> Dict:
        """
        Generate comprehensive performance report
        
        Args:
            predictions: List of predictions with outcomes
            start_date: Analysis start date
            end_date: Analysis end date
        
        Returns: Complete performance metrics dict
        """
        print("\n📊 Generating Performance Analytics...")
        print("=" * 60)
        
        # Extract returns
        returns = [p['return_pct'] for p in predictions if 'return_pct' in p and p['return_pct'] is not None]
        
        # Get S&P 500 benchmark
        sp500_returns = self.get_sp500_returns(start_date, end_date)
        
        # Calculate metrics
        sharpe = self.calculate_sharpe_ratio(returns)
        alpha, beta = self.calculate_alpha_beta(returns, sp500_returns)
        max_dd = self.calculate_max_drawdown(returns)
        win_stats = self.calculate_win_rate(predictions)
        
        # Calculate total return
        total_return = sum(returns)
        avg_return = statistics.mean(returns) if returns else 0.0
        
        # S&P 500 benchmark performance
        sp500_total = sum(sp500_returns) if sp500_returns else 0.0
        sp500_avg = statistics.mean(sp500_returns) if sp500_returns else 0.0
        
        # Information ratio vs S&P 500
        info_ratio = self.calculate_information_ratio(returns, sp500_returns)
        
        report = {
            'period': {
                'start': start_date,
                'end': end_date,
                'days': (end_date - start_date).days
            },
            'returns': {
                'total': total_return,
                'average': avg_return,
                'count': len(returns)
            },
            'risk_adjusted': {
                'sharpe_ratio': sharpe,
                'alpha': alpha,
                'beta': beta,
                'information_ratio': info_ratio,
                'max_drawdown': max_dd
            },
            'win_loss': win_stats,
            'benchmark': {
                'sp500_total_return': sp500_total,
                'sp500_avg_return': sp500_avg,
                'outperformance': total_return - sp500_total
            },
            'timestamp': datetime.now()
        }
        
        # Print report
        print(f"\n📈 PERIOD: {start_date.strftime('%Y-%m-%d')} to {end_date.strftime('%Y-%m-%d')}")
        print(f"   Days: {report['period']['days']}")
        
        print(f"\n💰 RETURNS:")
        print(f"   Total: {total_return:+.2f}%")
        print(f"   Average: {avg_return:+.2f}%")
        print(f"   Count: {len(returns)} trades")
        
        print(f"\n⚖️  RISK-ADJUSTED METRICS:")
        print(f"   Sharpe Ratio: {sharpe:.2f}")
        print(f"   Alpha: {alpha*100:+.2f}%")
        print(f"   Beta: {beta:.2f}")
        print(f"   Information Ratio: {info_ratio:.2f}")
        print(f"   Max Drawdown: {max_dd:.2f}%")
        
        print(f"\n🎯 WIN/LOSS STATS:")
        print(f"   Win Rate: {win_stats['win_rate']:.1f}%")
        print(f"   Wins: {win_stats['wins']}")
        print(f"   Losses: {win_stats['losses']}")
        print(f"   Avg Win: {win_stats['avg_win']:+.2f}%")
        print(f"   Avg Loss: {win_stats['avg_loss']:+.2f}%")
        print(f"   Win/Loss Ratio: {win_stats['win_loss_ratio']:.2f}x")
        
        print(f"\n📊 vs S&P 500:")
        print(f"   S&P 500 Total: {sp500_total:+.2f}%")
        print(f"   Outperformance: {report['benchmark']['outperformance']:+.2f}%")
        
        return report

if __name__ == '__main__':
    # Example usage
    analytics = PerformanceAnalytics()
    
    # Would typically be called with actual predictions data
    print("Performance Analytics Module Ready")
