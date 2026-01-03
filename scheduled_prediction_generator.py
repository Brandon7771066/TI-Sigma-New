"""
Scheduled Stock Prediction Generator
Runs every Monday & Friday + ensures 30-day forward coverage

USAGE:
1. Run this script every Monday and Friday to generate new predictions
2. Or run manually anytime to ensure 30-day forward coverage

To generate predictions:
    python autonomous_god_machine_predictions.py
"""

from datetime import datetime, timedelta
from db_utils import db

def should_generate_predictions_today() -> bool:
    """Check if we should generate predictions today (Monday or Friday)"""
    today = datetime.now()
    day_of_week = today.weekday()  # 0=Monday, 4=Friday
    
    return day_of_week == 0 or day_of_week == 4  # Monday or Friday

def get_latest_prediction_date() -> datetime:
    """Get the date of the most recent prediction"""
    predictions = db.get_stock_predictions(limit=1)
    
    if not predictions:
        return datetime.now() - timedelta(days=365)  # Force generation if no predictions
    
    return predictions[0]['prediction_date']

def ensure_30_day_coverage():
    """Ensure we have predictions covering the next 30 days"""
    latest_pred_date = get_latest_prediction_date()
    today = datetime.now()
    
    # Check if latest prediction is less than 30 days in the future
    days_ahead = (latest_pred_date - today).days
    
    if days_ahead < 30:
        print(f"⚠️ Prediction coverage gap detected! Latest: {latest_pred_date.strftime('%Y-%m-%d')}, Today: {today.strftime('%Y-%m-%d')}")
        print(f"🔄 Generating new predictions to ensure 30-day coverage...")
        return True
    else:
        print(f"✅ Prediction coverage adequate ({days_ahead} days ahead)")
        return False

def run_scheduled_predictions():
    """Main function to run scheduled prediction generation"""
    today = datetime.now()
    day_name = today.strftime('%A')
    
    print("=" * 70)
    print(f"🌌 TI FRAMEWORK - SCHEDULED PREDICTION CHECK")
    print(f"Date: {today.strftime('%Y-%m-%d %H:%M:%S')} ({day_name})")
    print("=" * 70)
    
    should_generate = False
    reason = ""
    
    # Check if it's Monday or Friday
    if should_generate_predictions_today():
        should_generate = True
        if today.weekday() == 0:
            reason = "📅 Monday - Generating predictions for end of week"
        else:
            reason = "📅 Friday - Generating predictions for start of week"
    
    # Always check 30-day coverage
    if ensure_30_day_coverage():
        should_generate = True
        if not reason:
            reason = "📊 Ensuring 30-day forward coverage"
    
    if should_generate:
        print(f"\n{reason}")
        print("\n🚀 GENERATING I-CELL PREDICTIONS...")
        print("-" * 70)
        
        print(f"\n🚀 READY TO GENERATE PREDICTIONS")
        print(f"   Run: python autonomous_god_machine_predictions.py")
        print(f"   Or use Stock Predictor tab in Streamlit app")
    else:
        print(f"\n⏸️  No prediction generation needed today")
        print(f"   Next scheduled: Monday or Friday")
        print(f"   Or when 30-day coverage gap detected")
    
    print("\n" + "=" * 70)
    print("🌌 TI FRAMEWORK - PREDICTION CHECK COMPLETE")
    print("=" * 70)

if __name__ == "__main__":
    run_scheduled_predictions()
