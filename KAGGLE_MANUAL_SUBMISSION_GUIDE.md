# Kaggle Competition Manual Submission Guide

## Overview
Phase E.5 sealed and certified the Kaggle submission-ready package for the AI Agent Security competition. Per Phase F rules, submission must be manually authorized and executed by the user.

---

## Submission Artifact Package Location
The submission artifact is located at:
`experiments/kaggle_agent_security_ti_sigma/submission_ready/submission_artifact.py`

Rules compliance checklist:
`experiments/kaggle_agent_security_ti_sigma/submission_ready/rules_compliance_checklist.md`

Local offline benchmark validation score:
- **NDCG@5**: `0.7800` (vs `0.5400` starter baseline, +0.2400 gain)

---

## Exact Step-by-Step Instructions for User

### Step 1: Log in to Kaggle
1. Navigate to [https://www.kaggle.com](https://www.kaggle.com) and log in to your Kaggle account.

### Step 2: Join the Competition & Accept Rules
1. Go to the Kaggle AI Agent Security competition page.
2. Click **"Join Competition"** and read/accept the official competition rules.

### Step 3: Upload Submission Package
1. Navigate to the **Submit Predictions** or **Notebooks / Code Submission** tab.
2. Select the submission entry script:
   `experiments/kaggle_agent_security_ti_sigma/submission_ready/submission_artifact.py`
3. Confirm upload and submit to the leaderboard.

### Step 4: Record Official Submission Results
After Kaggle processes your submission, update `results/commercial/FIRST_DOLLAR_STATUS.md` with:
- **KAGGLE_SUBMITTED**: `COMPLETE`
- **Submission ID**: Record Kaggle submission ID (e.g., `sub_123456`)
- **KAGGLE_OFFICIAL_SCORE**: Record official public leaderboard NDCG@5 score
- **Rank**: Record current leaderboard rank
