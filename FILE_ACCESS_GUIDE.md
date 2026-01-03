# Mood Amplifier Platform - Complete File Access Guide

## All Available Files & Where to Find Them

### 📍 **Location:** This Replit project root directory

---

## Core Application Files

### **Main Application**
- **`app.py`** - Main Streamlit application with 3 tabs:
  - Safety Analysis (multi-AI)
  - Model Validation
  - Animal Testing
  - **How to access:** Click "Files" icon in left sidebar → app.py

### **Configuration**
- **`replit.md`** - Project documentation and preferences
- **`.streamlit/config.toml`** - Streamlit server configuration

---

## Safety Analysis Module

### **AI Integrations**
- **`ai_integrations.py`** - OpenAI, Anthropic, Perplexity clients
- **`magai_integration.py`** - MagAI platform integration
- **`safety_analyzer.py`** - Comprehensive safety analysis logic
- **`submission_logger.py`** - **NEW** Automatic submission logging

### **Submission Storage** (NEW)
- **`submissions/`** directory - All user submissions saved here
  - `submission_index.json` - Master index of all submissions
  - `submission_YYYYMMDD_HHMMSS.txt` - Raw submission content
  - `submission_YYYYMMDD_HHMMSS_meta.json` - Metadata
  - `submission_YYYYMMDD_HHMMSS_results.json` - Analysis results

---

## Model Validation Module

### **Core Validation**
- **`validation_app.py`** - Interactive validation dashboard
- **`model_comparison.py`** - Tests TI-UOP vs established models
- **`emotion_models.py`** - Russell's Circumplex, PANAS, Frontal Alpha
- **`tiuop_adapter.py`** - TI-UOP framework adapter
- **`deap_loader.py`** - DEAP dataset loader
- **`test_deap_loader.py`** - Test script for dataset

### **Documentation**
- **`VALIDATION_METHODOLOGY.md`** - Scientific methodology
- **`results_export.py`** - Export validation results

---

## Animal Testing Module

### **Simulation Engine**
- **`animal_testing_simulation.py`** - EEG generation, mood shift analysis, safety monitoring
- **`fmri_simulation.py`** - fMRI parallel data generation
- **`animal_testing_dashboard.py`** - Interactive Streamlit interface

### **Comprehensive Studies**
- **`comprehensive_animal_study.py`** - Multi-species analysis framework
- **`run_quick_comprehensive_study.py`** - Quick study runner
- **`COMPREHENSIVE_ANIMAL_STUDY_REPORT.md`** - Full research report

---

## How to Access Everything

### **Method 1: Through Replit UI** (Easiest)
1. Click the **Files** icon (📁) in left sidebar
2. Browse and click any file to view/edit
3. Use search bar to find specific files

### **Method 2: Download All Files**
```bash
# Run in Shell
zip -r mood_amplifier_archive.zip . -x ".*" -x "__pycache__/*" -x ".pythonlibs/*"
```
Then download `mood_amplifier_archive.zip` from Files panel

### **Method 3: Git Export** (if enabled)
```bash
git clone <your-replit-git-url>
```

### **Method 4: View Individual Files** (Current Session)
- All files are in this chat - ask me to show you any specific file!
- Example: "Show me the contents of animal_testing_simulation.py"

---

## Quick File Reference

### Need to see experimental data?
→ `COMPREHENSIVE_ANIMAL_STUDY_REPORT.md`

### Need methodology?
→ `VALIDATION_METHODOLOGY.md` (validation)
→ `animal_testing_simulation.py` (docstrings explain all algorithms)

### Need to access past submissions?
→ `submissions/` directory (all saved automatically now!)

### Need to run experiments?
→ `python run_quick_comprehensive_study.py` (animal studies)
→ Open Streamlit app → Model Validation tab (validation experiments)

### Need to export data?
→ All dashboards have JSON download buttons
→ `results_export.py` has export functions

---

## File Tree Structure

```
mood-amplifier-platform/
├── app.py                              # Main application
├── replit.md                           # Documentation
│
├── Safety Analysis/
│   ├── ai_integrations.py
│   ├── magai_integration.py
│   ├── safety_analyzer.py
│   └── submission_logger.py            # NEW - Logs everything
│
├── Model Validation/
│   ├── validation_app.py
│   ├── model_comparison.py
│   ├── emotion_models.py
│   ├── tiuop_adapter.py
│   ├── deap_loader.py
│   ├── results_export.py
│   └── VALIDATION_METHODOLOGY.md
│
├── Animal Testing/
│   ├── animal_testing_simulation.py
│   ├── fmri_simulation.py
│   ├── animal_testing_dashboard.py
│   ├── comprehensive_animal_study.py
│   ├── run_quick_comprehensive_study.py
│   └── COMPREHENSIVE_ANIMAL_STUDY_REPORT.md
│
└── submissions/                        # NEW - All user data
    ├── submission_index.json
    └── submission_*.txt/json           # Auto-saved
```

---

## Next Steps

1. **All future submissions are now auto-saved** to `submissions/` directory
2. **To recover last night's submission:** Check if browser tab is still open, or re-submit
3. **To access any file:** Use Replit Files panel or ask me to show it
4. **To run experiments:** Use the Streamlit app or Python scripts

Everything is preserved and accessible! 🎉
