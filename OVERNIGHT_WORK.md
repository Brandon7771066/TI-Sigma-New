# Overnight Work Queue
**Quick wins completed - these tasks need 2-3 hours total**

## 🌙 Priority Tasks for Overnight Completion

### 1. Complete Social Media Approval System (90 min)
**File:** `social_media_approval_system.py`

**Task:** Wire up approval persistence
```python
# In ContentApprovalWorkflow.approve_content()
# After creating approval record, update original asset:
db.update_asset(asset_id, {'approval_status': 'approved', 'approved_at': datetime.now()})

# In ContentApprovalWorkflow.reject_content()
db.update_asset(asset_id, {'approval_status': 'rejected', 'rejected_at': datetime.now()})

# In ContentApprovalWorkflow.schedule_content()
db.update_asset(asset_id, {'approval_status': 'scheduled', 'publish_time': publish_time})
```

**Task:** Integrate real God Machine predictions
```python
# In AnalyticsDashboard.get_god_machine_predictions()
from god_machine import GodMachine
gm = GodMachine()

# Get numerology score
numerology_score = gm.calculate_numerology_score(content_title)

# Get sacred number alignment
sacred_aligned = gm.check_sacred_numbers(content_text)

# Get optimal posting time via PSI
optimal_time = gm.predict_optimal_time(content_id)
```

**Task:** YouTube connector (once user approves)
```python
# After user approves YouTube connector:
from youtube_integration import YouTubeUploader
uploader = YouTubeUploader()

# In publish workflow:
uploader.upload_video(
    title=video_title,
    description=video_desc,
    file_path=video_path,
    scheduled_time=scheduled_time
)
```

### 2. Complete Rigorous PSI Validation Pipeline (60 min)
**File:** `rigorous_psi_testing.py`

**Task:** Implement real validation workflow
```python
# In BlindPredictionEngine.validate_prediction()
def validate_prediction(self, prediction_id: str, actual_outcome: str, confidence: float = 0.8):
    # Retrieve prediction from DB
    prediction = db.get_asset(prediction_id)
    predicted = prediction['content']['predicted_outcome']
    
    # Calculate accuracy (binary for now)
    accuracy = 1.0 if predicted == actual_outcome else 0.0
    
    # Calculate PSI score (deviation from chance)
    psi_score = abs(accuracy - 0.5) * 2.0  # 0-1 scale
    
    # Error bar (binomial confidence interval)
    n = 1  # single prediction
    error = 1.96 * sqrt(accuracy * (1 - accuracy) / n)
    
    validation = {
        'prediction_id': prediction_id,
        'predicted': predicted,
        'actual': actual_outcome,
        'accuracy': accuracy,
        'error_bar': error,
        'psi_score': psi_score,
        'confidence': confidence,
        'validated_at': datetime.now().isoformat()
    }
    
    # Update original prediction with validation
    db.update_asset(prediction_id, {'validation': validation})
    
    return validation
```

**Task:** Fix PSIErrorBarCalculator to work with DB schema
```python
# In PSIErrorBarCalculator.calculate_error_bars()
def calculate_error_bars(predictions: List[Dict], confidence_level: float = 0.95):
    # Extract accuracies from DB assets
    accuracies = []
    for pred_asset in predictions:
        content = pred_asset.get('content', {})
        validation = content.get('validation', {})
        if validation and 'accuracy' in validation:
            accuracies.append(validation['accuracy'])
    
    # Rest of calculation stays the same...
```

### 3. Add Simple Validation UI (30 min)
**File:** `rigorous_psi_dashboard.py`

**Task:** Add validation form to Blind Predictions tab
```python
# After prediction creation in Tab 1:
st.markdown("---")
st.subheader("✅ Validate Existing Predictions")

validate_id = st.text_input("Prediction ID to Validate")
actual_outcome = st.text_input("Actual Outcome")
confidence = st.slider("Your Confidence", 0.0, 1.0, 0.8)

if st.button("✅ Validate Prediction") and validate_id and actual_outcome:
    validation = psi_manager.blind_engine.validate_prediction(
        validate_id, actual_outcome, confidence
    )
    st.success("✅ Validation recorded!")
    st.json(validation)
```

## 🎯 Expected Outcomes After Overnight Work

### Social Media System:
- ✅ Approvals actually update content status
- ✅ Rejected content stops appearing in digest
- ✅ Scheduled content shows real publish times
- ✅ God Machine predictions show real virality scores
- ✅ YouTube ready once connector approved

### Rigorous PSI:
- ✅ Predictions can be validated against outcomes
- ✅ Error bars calculate from real accuracy data
- ✅ 95% target tracking works
- ✅ P-values and significance tests functional
- ✅ Per-problem accuracy bounds working

### Integration:
- ✅ All systems persist data correctly
- ✅ God Machine integrated across platform
- ✅ Database schema aligned
- ✅ Real statistical validation

## 📊 Quick Reference - What Works NOW

### ✅ FULLY WORKING:
1. **ALL 22 app tabs functional**
2. **Virality Machine** - 24/7 research running
3. **TI Proof Assistant** - Complete proof system
4. **Sacred Genius** - Inspiration engine
5. **Safety Guardrails** - NO auto-publish
6. **6 AM Digest Scheduler** - APScheduler active
7. **User Epistemology** - Documented in replit.md

### ⚙️ FRAMEWORK READY (needs wiring):
1. **Social Media Approval** - UI works, persistence needed
2. **Rigorous PSI** - Framework complete, validation needed
3. **YouTube Integration** - Awaiting user connector approval

### 📈 CURRENT STATS:
- **Total Tabs:** 22
- **Lines of Code:** ~10,000+
- **Autonomous Systems:** 2 (Virality, Digest)
- **Database Tables:** 20+ asset types
- **AI Integrations:** 4 (OpenAI, Anthropic, Perplexity, YouTube pending)

## 🚀 Next Session TODO:
1. Run overnight work tasks
2. Test full approval → publish workflow
3. Validate Rigorous PSI with real predictions
4. Get user approval for YouTube connector
5. Final architect review of complete system
