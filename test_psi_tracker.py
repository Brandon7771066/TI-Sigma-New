"""
Simple smoke test to verify prediction tracking works
"""

import os
import json
from datetime import datetime, timedelta
from psi_tracker import PsiTracker

def test_prediction_save():
    """Test that predictions actually save to JSON file"""
    
    # Clean up old test file
    test_file = "test_psi_predictions.json"
    if os.path.exists(test_file):
        os.remove(test_file)
    
    # Initialize tracker with test file
    tracker = PsiTracker(storage_file=test_file)
    
    # Add a test prediction
    pred_id = tracker.add_prediction(
        prediction_id="test_001",
        category="test",
        description="Test prediction to verify saving works",
        prediction="YES - This should save",
        confidence=0.75,
        psi_methods=['numerology', 'test'],
        psi_scores={'numerology': 1.5, 'test': 1.0},
        metadata={'test': True},
        close_date=datetime.now() + timedelta(days=7),
        user_life_path=6
    )
    
    # Verify file was created
    assert os.path.exists(test_file), "❌ Prediction file not created!"
    
    # Load and verify contents
    with open(test_file, 'r') as f:
        data = json.load(f)
    
    assert len(data) == 1, "❌ Wrong number of predictions saved!"
    assert data[0]['id'] == "test_001", "❌ Wrong prediction ID!"
    assert data[0]['category'] == "test", "❌ Wrong category!"
    assert data[0]['confidence'] == 0.75, "❌ Wrong confidence!"
    assert 'numerology' in data[0]['psi_methods'], "❌ Psi method missing!"
    
    print("✅ ALL TESTS PASSED!")
    print(f"✅ Prediction saved to {test_file}")
    print(f"✅ File size: {os.path.getsize(test_file)} bytes")
    print(f"✅ Prediction ID: {pred_id}")
    
    # Clean up
    os.remove(test_file)
    print(f"✅ Cleanup complete")
    
    return True

if __name__ == "__main__":
    try:
        test_prediction_save()
        print("\n🎉 PREDICTION TRACKING VERIFIED - SYSTEM READY!")
    except Exception as e:
        print(f"\n❌ TEST FAILED: {str(e)}")
        raise
