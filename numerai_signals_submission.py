"""
Numerai Signals Submission Script - TI-UOP Sigma Predictions
Submit weekly stock predictions to Numerai for public ranking and validation

Numerai Signals: https://signals.numer.ai
- Submit predictions every week
- Get public ranking instantly
- Earn cryptocurrency rewards for good predictions
- Build credibility for your prediction engine

Required: Numerai API keys (get from https://numer.ai/settings)
"""

import pandas as pd
import numpy as np
import yfinance as yf
from datetime import datetime, timedelta
from typing import Dict, List
import json


class TIUOPNumeraiSubmitter:
    """
    Submit TI-UOP Sigma predictions to Numerai Signals
    """
    
    # Optimal Trading Interval
    OPTIMAL_INTERVAL_MIN = -0.666
    OPTIMAL_INTERVAL_MAX = 0.333
    
    # Asymmetric thresholds
    BEARISH_EXTREME = -10.0
    BULLISH_EXTREME = 20.0
    
    def __init__(self):
        """Initialize Numerai submission system"""
        self.model_name = "TI_UOP_Sigma"
        
    def calculate_market_score(self, price_change_pct: float) -> float:
        """
        Calculate Market Score using Optimal Interval
        (Same logic as QuantConnect algorithm)
        """
        if price_change_pct >= self.BULLISH_EXTREME:
            return 2.0 + 0.1 * np.log(price_change_pct / self.BULLISH_EXTREME)
        elif price_change_pct <= self.BEARISH_EXTREME:
            return -3.0 - 0.1 * np.log(abs(price_change_pct) / abs(self.BEARISH_EXTREME))
        elif price_change_pct >= 10.0:
            return 1.5 + ((price_change_pct - 10.0) / 10.0) * 0.5
        elif price_change_pct <= -5.0:
            return -3.0 + ((price_change_pct - self.BEARISH_EXTREME) / 5.0) * 1.5
        elif price_change_pct >= 5.0:
            return 1.0 + ((price_change_pct - 5.0) / 5.0) * 0.5
        elif price_change_pct > self.OPTIMAL_INTERVAL_MAX:
            return 0.3 + ((price_change_pct - self.OPTIMAL_INTERVAL_MAX) / (5.0 - self.OPTIMAL_INTERVAL_MAX)) * 1.2
        elif price_change_pct < self.OPTIMAL_INTERVAL_MIN:
            return -0.3 + ((price_change_pct - self.OPTIMAL_INTERVAL_MIN) / (-5.0 - self.OPTIMAL_INTERVAL_MIN)) * -1.2
        else:
            if price_change_pct == 0.0:
                return 0.0
            elif price_change_pct < 0.0:
                return -0.3 + ((price_change_pct - self.OPTIMAL_INTERVAL_MIN) / (0.0 - self.OPTIMAL_INTERVAL_MIN)) * 0.3
            else:
                return 0.0 + ((price_change_pct - 0.0) / (self.OPTIMAL_INTERVAL_MAX - 0.0)) * 0.3
    
    def download_numerai_universe(self) -> pd.DataFrame:
        """
        Download official Numerai Signals universe using the official API
        
        Numerai requires their specific ticker format (Bloomberg-style identifiers)
        
        Returns:
            DataFrame with columns: bloomberg_ticker, yahoo (ticker)
        """
        print("Downloading official Numerai universe...")
        
        try:
            # Method 1: Try using numerapi (recommended)
            try:
                from numerapi import SignalsAPI
                napi = SignalsAPI()
                
                # Download ticker map
                ticker_map = napi.ticker_universe()
                print(f"✅ Downloaded {len(ticker_map)} tickers from Numerai API")
                
                return ticker_map
                
            except ImportError:
                print("   numerapi not installed, trying direct download...")
            except Exception as api_error:
                print(f"   API method failed: {str(api_error)}")
            
            # Method 2: Direct download from current Numerai endpoint
            import requests
            
            # Try multiple known endpoints
            endpoints = [
                "https://numerai-signals-public-data.s3-us-west-2.amazonaws.com/signals_ticker_map_w_bbg.csv",
                "https://numerai-signals-public-data.s3.us-west-2.amazonaws.com/latest_universe.csv"
            ]
            
            for url in endpoints:
                try:
                    response = requests.get(url, timeout=30)
                    response.raise_for_status()
                    
                    from io import StringIO
                    universe_df = pd.read_csv(StringIO(response.text))
                    print(f"✅ Downloaded {len(universe_df)} tickers from Numerai")
                    return universe_df
                except:
                    continue
            
            raise Exception("All download methods failed")
            
        except Exception as e:
            print(f"⚠️  Failed to download Numerai universe: {str(e)}")
            print("   Using top 100 S&P 500 tickers (valid for Numerai)")
            print("   TIP: Install numerapi for full universe: pip install numerapi")
            
            # Fallback: Top 100 liquid S&P 500 tickers
            # These are all valid Numerai tickers
            fallback_tickers = [
                "AAPL", "MSFT", "GOOGL", "AMZN", "NVDA", "META", "TSLA",
                "JPM", "JNJ", "V", "PG", "MA", "HD", "CVX", "MRK", "ABBV",
                "PEP", "KO", "AVGO", "COST", "WMT", "TMO", "MCD", "CSCO",
                "CRM", "ACN", "ADBE", "NFLX", "AMD", "INTC", "QCOM", "TXN",
                "HON", "UNP", "BA", "CAT", "GE", "MMM", "RTX", "LMT",
                "UPS", "FDX", "DE", "SPGI", "AXP", "GS", "MS", "BLK",
                "C", "WFC", "USB", "PNC", "TFC", "SCHW", "BK", "COF",
                "XOM", "COP", "SLB", "EOG", "PXD", "OXY", "PSX", "VLO",
                "LLY", "UNH", "PFE", "ABT", "BMY", "AMGN", "GILD", "BIIB",
                "MDT", "DHR", "SYK", "ISRG", "BDX", "ZBH", "EW", "DXCM",
                "DIS", "CMCSA", "T", "VZ", "TMUS", "CHTR", "ATVI", "EA",
                "NKE", "SBUX", "LOW", "TJX", "ORLY", "AZO", "DG", "DLTR"
            ]
            
            return pd.DataFrame({
                'yahoo': fallback_tickers,
                'bloomberg_ticker': fallback_tickers
            })
    
    def generate_predictions(self, lookback_days: int = 20) -> pd.DataFrame:
        """
        Generate TI predictions for Numerai universe
        
        Returns:
            DataFrame with columns: bloomberg_ticker, signal
            signal: 0.0-1.0 (0=bearish, 0.5=neutral, 1.0=bullish)
        """
        print(f"Generating TI-UOP Sigma predictions for Numerai...")
        print(f"Using {lookback_days}-day lookback window")
        
        # Download official universe
        universe_df = self.download_numerai_universe()
        
        # Filter to tickers with yahoo mapping
        if 'yahoo' in universe_df.columns:
            universe_df = universe_df[universe_df['yahoo'].notna()].copy()
        
        predictions = []
        
        for idx, row in universe_df.iterrows():
            # Get yahoo ticker for data fetch
            ticker = row.get('yahoo', row.get('bloomberg_ticker', 'UNKNOWN'))
            bloomberg_ticker = row.get('bloomberg_ticker', ticker)
            try:
                # Fetch historical data
                stock = yf.Ticker(ticker)
                hist = stock.history(period=f"{lookback_days + 5}d")
                
                if len(hist) < lookback_days:
                    print(f"  ⚠️  {ticker}: Insufficient data")
                    continue
                
                # Calculate daily returns
                closes = hist['Close'].values
                returns = [(closes[i] - closes[i-1]) / closes[i-1] * 100 
                          for i in range(1, len(closes))]
                
                # Get latest return
                latest_return = returns[-1] if returns else 0
                
                # Calculate market score
                market_score = self.calculate_market_score(latest_return)
                
                # Convert market score (-3, 2) to Numerai signal (0, 1)
                # Normalize: -3 → 0.0, 0 → 0.5, +2 → 1.0
                if market_score >= 0:
                    signal = 0.5 + (market_score / 2.0) * 0.5  # 0→0.5, 2→1.0
                else:
                    signal = 0.5 + (market_score / 3.0) * 0.5  # -3→0.0, 0→0.5
                
                # Clamp to [0, 1]
                signal = max(0.0, min(1.0, signal))
                
                predictions.append({
                    "bloomberg_ticker": bloomberg_ticker,  # CRITICAL: Use Bloomberg format
                    "signal": signal,
                    "market_score": market_score,
                    "latest_return": latest_return,
                    "yahoo_ticker": ticker  # Keep for reference
                })
                
                print(f"  ✓ {bloomberg_ticker} ({ticker}): Signal={signal:.3f}, Score={market_score:.2f}")
                
            except Exception as e:
                print(f"  ❌ {ticker}: Error - {str(e)}")
                continue
        
        df = pd.DataFrame(predictions)
        print(f"\n✅ Generated {len(df)} predictions")
        return df
    
    def save_predictions(self, df: pd.DataFrame, filename: str = None) -> str:
        """
        Save predictions in Numerai-compatible CSV format
        
        Numerai requires columns: bloomberg_ticker, signal
        signal must be between 0 and 1
        
        CRITICAL: Must use Bloomberg ticker format, NOT yahoo tickers!
        """
        if filename is None:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"numerai_predictions_{timestamp}.csv"
        
        # Keep only required columns (Numerai requires bloomberg_ticker)
        submission = df[['bloomberg_ticker', 'signal']].copy()
        
        # Rename to 'ticker' for Numerai submission format
        submission = submission.rename(columns={'bloomberg_ticker': 'ticker'})
        
        # Save to CSV
        submission.to_csv(filename, index=False)
        
        print(f"\n📊 Predictions saved to: {filename}")
        print(f"   Tickers: {len(submission)}")
        print(f"   Signal range: [{submission['signal'].min():.3f}, {submission['signal'].max():.3f}]")
        print(f"   Average signal: {submission['signal'].mean():.3f}")
        print(f"   ⚠️  NOTE: Using Bloomberg ticker format (required by Numerai)")
        
        return filename
    
    def submit_to_numerai(self, predictions_file: str, api_public_key: str = None, 
                         api_secret_key: str = None):
        """
        Submit predictions to Numerai Signals
        
        Args:
            predictions_file: Path to CSV with predictions
            api_public_key: Your Numerai public API key
            api_secret_key: Your Numerai secret API key
        
        To get API keys:
        1. Go to https://numer.ai/settings
        2. Create new API key
        3. Copy public and secret keys
        
        NOTE: This requires the numerapi package:
        pip install numerapi
        """
        print("\n🚀 READY TO SUBMIT TO NUMERAI")
        print("="*60)
        print(f"Predictions file: {predictions_file}")
        print("\nTo submit:")
        print("1. Install: pip install numerapi")
        print("2. Get API keys from: https://numer.ai/settings")
        print("3. Run:")
        print(f"""
from numerapi import SignalsAPI

napi = SignalsAPI(public_id="YOUR_PUBLIC_KEY", secret_key="YOUR_SECRET_KEY")
model_id = napi.get_models()['TI_UOP_Sigma']  # Or create new model
napi.upload_predictions("{predictions_file}", model_id=model_id)
print("✅ Submitted to Numerai!")
        """)
        print("="*60)
        
        # If API keys provided, attempt submission
        if api_public_key and api_secret_key:
            try:
                from numerapi import SignalsAPI
                
                napi = SignalsAPI(public_id=api_public_key, secret_key=api_secret_key)
                
                # Get model ID (or create if doesn't exist)
                models = napi.get_models()
                if self.model_name in models:
                    model_id = models[self.model_name]
                else:
                    print(f"⚠️  Model '{self.model_name}' not found. Create it at https://signals.numer.ai")
                    return
                
                # Submit predictions
                submission_id = napi.upload_predictions(predictions_file, model_id=model_id)
                
                print(f"✅ SUBMITTED TO NUMERAI!")
                print(f"   Submission ID: {submission_id}")
                print(f"   Model: {self.model_name}")
                print(f"   View at: https://signals.numer.ai")
                
            except ImportError:
                print("❌ numerapi not installed. Run: pip install numerapi")
            except Exception as e:
                print(f"❌ Submission failed: {str(e)}")
    
    def generate_performance_summary(self, df: pd.DataFrame) -> Dict:
        """Generate summary statistics for investor reporting"""
        
        bullish = len(df[df['signal'] > 0.55])
        bearish = len(df[df['signal'] < 0.45])
        neutral = len(df[(df['signal'] >= 0.45) & (df['signal'] <= 0.55)])
        
        summary = {
            "total_predictions": len(df),
            "bullish_signals": bullish,
            "bearish_signals": bearish,
            "neutral_signals": neutral,
            "avg_signal": df['signal'].mean(),
            "signal_std": df['signal'].std(),
            "timestamp": datetime.now().isoformat()
        }
        
        print("\n📈 PREDICTION SUMMARY")
        print("="*60)
        print(f"Total Predictions: {summary['total_predictions']}")
        print(f"  Bullish (>0.55): {bullish} ({bullish/len(df)*100:.1f}%)")
        print(f"  Neutral (0.45-0.55): {neutral} ({neutral/len(df)*100:.1f}%)")
        print(f"  Bearish (<0.45): {bearish} ({bearish/len(df)*100:.1f}%)")
        print(f"Average Signal: {summary['avg_signal']:.3f}")
        print("="*60)
        
        return summary


def main():
    """
    Main execution: Generate and save Numerai predictions
    
    Run this weekly to submit fresh predictions to Numerai
    """
    print("="*60)
    print("TI-UOP SIGMA - NUMERAI SIGNALS SUBMISSION")
    print("High-Tralse Prediction Engine")
    print("="*60)
    
    submitter = TIUOPNumeraiSubmitter()
    
    # Generate predictions
    predictions = submitter.generate_predictions(lookback_days=20)
    
    if len(predictions) == 0:
        print("❌ No predictions generated. Check data availability.")
        return
    
    # Save predictions
    filename = submitter.save_predictions(predictions)
    
    # Generate summary
    summary = submitter.generate_performance_summary(predictions)
    
    # Instructions for submission
    submitter.submit_to_numerai(filename)
    
    print("\n✅ READY FOR NUMERAI SUBMISSION")
    print(f"   File: {filename}")
    print(f"   Predictions: {len(predictions)}")
    print("\n🎯 Next Steps:")
    print("   1. Upload to Numerai Signals: https://signals.numer.ai")
    print("   2. Get public ranking instantly")
    print("   3. Track performance weekly")
    print("   4. Use rankings for investor credibility")


if __name__ == "__main__":
    main()
