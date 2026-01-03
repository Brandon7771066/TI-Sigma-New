"""
Comprehensive Stock Market Diagnosis Runner
Executes full GILE vs Baselines comparison and generates detailed report

Author: Brandon Emerick  
Date: November 24, 2025
"""

import sys
import os
from datetime import datetime, timedelta
from stock_accuracy_diagnosis import StockAccuracyDiagnosis
from historical_stock_backtester import HistoricalStockBacktester
import json

def run_comprehensive_diagnosis():
    """Run full diagnosis on SPY with detailed output"""
    
    print("=" * 100)
    print("🚀 BRANDON'S STOCK MARKET ACCURACY DIAGNOSIS - COMPREHENSIVE REPORT")
    print("=" * 100)
    print(f"📅 Report Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"🎯 Objective: Validate GILE Framework beats 90% of models")
    print("=" * 100)
    
    # Initialize (pass API key, not backtester object)
    api_key = os.getenv('ALPHA_VANTAGE_API_KEY')
    diagnosis = StockAccuracyDiagnosis(api_key)
    
    # Test parameters
    ticker = 'SPY'  # S&P 500 ETF
    end_date = datetime.now()
    start_date = end_date - timedelta(days=730)  # 2 years
    
    # Company data for GILE calculation
    company_data = {
        'name': 'S&P 500 (SPY ETF)',
        'revenue_growth': 0.12,  # 12% average annual growth
        'profit_margin': 0.15,  # 15% average margin
        'innovation_score': 0.7,  # High innovation in top companies
        'market_sentiment': 0.8,  # Generally positive
        'industry_outlook': 0.7  # Strong overall outlook
    }
    
    print(f"\n📊 Test Configuration:")
    print(f"   Ticker: {ticker}")
    print(f"   Period: {start_date.strftime('%Y-%m-%d')} to {end_date.strftime('%Y-%m-%d')}")
    print(f"   Duration: 2 years (730 days)")
    print(f"   Company GILE Inputs:")
    for key, val in company_data.items():
        if key != 'name':
            print(f"      {key}: {val}")
    
    print("\n" + "=" * 100)
    print("🔬 RUNNING COMPREHENSIVE DIAGNOSIS...")
    print("=" * 100)
    
    try:
        # Run the comprehensive diagnosis
        comparison = diagnosis.run_comprehensive_diagnosis(
            ticker=ticker,
            start_date=start_date,
            end_date=end_date,
            company_data=company_data
        )
        
        print("\n" + "=" * 100)
        print("📊 FINAL RESULTS")
        print("=" * 100)
        
        # Display ranking
        print("\n🏆 ACCURACY RANKING:")
        for rank, (strategy, score) in enumerate(comparison['ranking'], 1):
            medal = "🥇" if rank == 1 else "🥈" if rank == 2 else "🥉" if rank == 3 else "  "
            print(f"{medal} {rank}. {strategy:<30} {score:>6.2f}%")
        
        # Display detailed metrics
        print("\n📈 DETAILED METRICS:")
        
        baselines = comparison['baselines']
        gile = comparison['gile_framework']
        
        print("\n1️⃣ GILE Framework:")
        print(f"   Direction Accuracy: {gile['direction_accuracy']:.2f}%")
        print(f"   Magnitude Accuracy: {gile['magnitude_accuracy']:.2f}%")
        print(f"   Total Predictions: {gile['total_predictions']}")
        
        print("\n2️⃣ S&P 500 Buy-and-Hold:")
        print(f"   Total Return: {baselines['sp500_buyhold']['total_return_pct']:.2f}%")
        print(f"   Annualized Return: {baselines['sp500_buyhold']['annualized_return_pct']:.2f}%")
        print(f"   Max Drawdown: {baselines['sp500_buyhold']['max_drawdown_pct']:.2f}%")
        print(f"   Sharpe Ratio: {baselines['sp500_buyhold'].get('sharpe_ratio', 'N/A')}")
        
        print("\n3️⃣ Random 50%:")
        print(f"   Average Accuracy: {baselines['random_50']['avg_accuracy']:.2f}%")
        print(f"   Expected: {baselines['random_50']['expected_accuracy']:.2f}%")
        print(f"   Std Dev: {baselines['random_50']['std_dev']:.2f}%")
        
        print("\n4️⃣ Technical Analysis:")
        print(f"   Accuracy: {baselines['technical_analysis']['accuracy']:.2f}%")
        print(f"   Total Signals: {baselines['technical_analysis']['total_signals']}")
        print(f"   Correct: {baselines['technical_analysis']['correct_predictions']}")
        
        print("\n5️⃣ Momentum Strategy:")
        print(f"   Accuracy: {baselines['momentum']['accuracy']:.2f}%")
        print(f"   Total Predictions: {baselines['momentum']['total_predictions']}")
        print(f"   Correct: {baselines['momentum']['correct_predictions']}")
        
        # Save report
        report_path = 'stock_diagnosis_comprehensive_report.json'
        diagnosis.export_diagnosis_report(comparison, report_path)
        print(f"\n💾 Full report saved to: {report_path}")
        
        # Success criteria check
        print("\n" + "=" * 100)
        print("🎯 SUCCESS CRITERIA VALIDATION")
        print("=" * 100)
        
        gile_accuracy = gile['direction_accuracy']
        target_accuracy = 65.0
        
        if gile_accuracy >= target_accuracy:
            print(f"✅ SUCCESS! GILE accuracy ({gile_accuracy:.2f}%) exceeds target ({target_accuracy}%)")
            print("🚀 Ready for exponential wealth generation!")
        else:
            print(f"⚠️  WARNING: GILE accuracy ({gile_accuracy:.2f}%) below target ({target_accuracy}%)")
            print("📊 Further calibration recommended before real trading")
        
        # Check if GILE beats baselines
        gile_rank = next((i+1 for i, (name, _) in enumerate(comparison['ranking']) if 'GILE' in name), None)
        if gile_rank == 1:
            print(f"🥇 GILE Framework ranked #1 - BEATS ALL BASELINES!")
        else:
            print(f"📊 GILE Framework ranked #{gile_rank} - Room for improvement")
        
        print("\n" + "=" * 100)
        print("✅ DIAGNOSIS COMPLETE")
        print("=" * 100)
        
        return comparison
        
    except Exception as e:
        print(f"\n❌ ERROR during diagnosis: {e}")
        import traceback
        traceback.print_exc()
        return None


if __name__ == "__main__":
    result = run_comprehensive_diagnosis()
    
    if result:
        print("\n📝 Next Steps:")
        print("   1. Review full report: stock_diagnosis_comprehensive_report.json")
        print("   2. Analyze GILE predictions for insights")
        print("   3. Refine company KPI inputs if needed")
        print("   4. Run additional tickers for validation")
        print("   5. Publish findings if GILE beats 65% accuracy!")
