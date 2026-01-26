# TI Multi-Competition Strategy
## Active Competitions (3)

### 1. 🎓 Playground S6E1 - Student Test Scores
**Status:** ✅ READY TO SUBMIT  
**Deadline:** January 31, 2026 (5 days)  
**Prize:** Points/Medals  
**Metric:** RMSE  

**Best CV:** 8.7862 (stacked meta-model)  
**Leader:** 8.5347  
**Gap:** +0.26  

**Submission Ready:** `kaggle_student_scores/submission_stacked.csv`

**TI Frameworks Applied:**
- LCC threshold (0.42) for feature selection
- Target encoding with smoothing
- Polynomial features on study_hours (r=0.76)
- Multi-layer stacking ensemble

---

### 2. 🌟 MALLORN Astronomical Classification
**Status:** 🔧 SOLVER READY, NEEDS DATA  
**Deadline:** January 30, 2026 (4 days)  
**Prize:** €1,000 (1st place)  
**Metric:** F1 Score  

**Task:** Identify Tidal Disruption Events (TDEs) - stars torn apart by black holes

**Solver:** `kaggle_mallorn/ti_mallorn_solver.py`

**To Run:**
1. Download data from: https://www.kaggle.com/competitions/mallorn-astronomical-classification-challenge/data
2. Extract to `kaggle_mallorn/`:
   - training_log.csv
   - training_lc/ (folder)
   - test_log.csv
   - test_lc/ (folder)
3. Run: `cd kaggle_mallorn && python ti_mallorn_solver.py`

**TI Enhancements:**
- LCC threshold for flux anomaly detection
- Light curve feature extraction (rise/decline asymmetry)
- Optimal F1 threshold tuning

---

### 3. 🧬 CAFA 6 Protein Function Prediction
**Status:** ⚠️ ENTRY DEADLINE TODAY (Jan 26)!  
**Deadline:** Entry closes TODAY  
**Prize:** $50,000  
**Metric:** F-max (multi-label)  

**Task:** Predict Gene Ontology terms from protein sequences

**Solver:** `kaggle_cafa6/ti_cafa6_solver.py`

**To Run:**
1. Download data from: https://www.kaggle.com/competitions/cafa-6-protein-function-prediction/data
2. Extract to `kaggle_cafa6/`:
   - train_sequences.fasta
   - train_terms.tsv
   - test_sequences.fasta
   - sample_submission.csv
3. Run: `cd kaggle_cafa6 && python ti_cafa6_solver.py`

**TI Enhancements:**
- Entropy as GILE I-dimension proxy
- Physicochemical property analysis
- Multi-label classification per GO term

---

## Quick Actions

> **Note:** Kaggle CLI is not installed in this environment. Use manual download from Kaggle website.

### Submit Student Scores:
1. Go to: https://www.kaggle.com/competitions/playground-series-s6e1/submit
2. Upload: `kaggle_student_scores/submission_stacked.csv`
3. Description: "TI Stacking Solver - CV 8.79"

### Download MALLORN Data (Manual):
1. Go to: https://www.kaggle.com/competitions/mallorn-astronomical-classification-challenge/data
2. Download all files
3. Extract `training_lc.zip` and `test_lc.zip` to `kaggle_mallorn/`
4. Run: `cd kaggle_mallorn && python ti_mallorn_solver.py`

### Download CAFA 6 Data (Manual):
1. Go to: https://www.kaggle.com/competitions/cafa-6-protein-function-prediction/data
2. Download all files to `kaggle_cafa6/`
3. Run: `cd kaggle_cafa6 && python ti_cafa6_solver.py`

---

## Strategy Notes

1. **Student Scores** - Without XGBoost/LightGBM, we're at ~8.79 vs leader 8.53. Still competitive for top 30-40%.

2. **MALLORN** - Binary classification with severe class imbalance. TDEs are rare (<1%). F1 optimization critical.

3. **CAFA 6** - Multi-label protein function. Complex ontology hierarchy. Large prize pool makes this high priority!

---

*Last Updated: January 26, 2026*
