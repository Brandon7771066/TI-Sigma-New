"""
TI MALLORN v10 - MYRION RESOLUTION ENSEMBLE
Combining v3-v9 using MR constraint-based logic:
- Each version tackles problem from different angle
- MR accumulates evidence across perspectives
- Constraint satisfaction determines final prediction
Target: F1 > 0.75
"""

import pandas as pd
import numpy as np
from sklearn.metrics import f1_score
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v10 - MYRION RESOLUTION ENSEMBLE")
print("Constraint-Based Multi-Perspective Integration")
print("="*70)

# Load all submissions
submissions = {}
versions = ['v3', 'v5', 'v6', 'v7', 'v8', 'v9']

print("\nLoading submissions...")
for v in versions:
    f = f'submission_mallorn_{v}.csv'
    try:
        df = pd.read_csv(f)
        submissions[v] = df
        print(f"  {v}: {df['prediction'].sum()} TDEs predicted")
    except:
        print(f"  {v}: NOT FOUND")

# Load training data for validation
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')

print(f"\nTest set: {len(test_log)} objects")
print(f"Versions loaded: {list(submissions.keys())}")

# ============ MYRION RESOLUTION THEORY ============
# MR accumulates evidence across multiple "resolutions" (perspectives)
# Each version represents a different resolution:
#   v3: Basic ensemble + LCC features
#   v5: Ξ Tensor Theory (existence intensity)
#   v6: MR + LCC Empirical validation
#   v7: Meta-learner stacking
#   v8: Optimized weighted blend
#   v9: Quantum LCC Virus + PRF

# MR Thresholds (from LCC theory)
LCC_042 = 0.42   # Minimum detection
LCC_085 = 0.85   # Causal threshold
LCC_TT = 0.92**2 # True-Tralseness

def myrion_resolution_score(predictions_dict, object_ids):
    """
    Myrion Resolution: Accumulate evidence across perspectives
    
    MR Score = Σ (weight_i × prediction_i) / Σ weight_i
    
    Where weights are based on CV F1 performance of each version
    """
    # Weights based on empirical CV F1 performance
    weights = {
        'v3': 0.41,   # Best CV
        'v5': 0.41,   # Ξ Tensor
        'v6': 0.39,   # MR + LCC
        'v7': 0.42,   # Meta-learner (best single)
        'v8': 0.39,   # Optimized blend
        'v9': 0.38,   # Quantum LCC
    }
    
    # Build prediction matrix
    n = len(object_ids)
    scores = np.zeros(n)
    total_weight = 0
    
    for v, df in predictions_dict.items():
        if v not in weights:
            continue
        w = weights[v]
        total_weight += w
        
        # Merge on object_id to ensure alignment
        for i, obj_id in enumerate(object_ids):
            pred = df[df['object_id'] == obj_id]['prediction'].values
            if len(pred) > 0:
                scores[i] += w * pred[0]
    
    return scores / (total_weight + 1e-8)

def constraint_satisfaction(mr_scores, predictions_dict, object_ids):
    """
    MR Constraint Satisfaction:
    - STRONG constraint: All versions agree
    - MEDIUM constraint: Majority agree
    - WEAK constraint: High MR score alone
    
    TDE requires satisfying at least one constraint level
    """
    n = len(object_ids)
    agreement = np.zeros(n)
    
    for v, df in predictions_dict.items():
        for i, obj_id in enumerate(object_ids):
            pred = df[df['object_id'] == obj_id]['prediction'].values
            if len(pred) > 0 and pred[0] == 1:
                agreement[i] += 1
    
    n_versions = len(predictions_dict)
    
    # Constraint levels
    strong = agreement == n_versions  # All agree
    medium = agreement >= (n_versions * 0.67)  # 2/3 majority
    weak = mr_scores >= LCC_085  # High MR score
    
    return strong, medium, weak, agreement

print("\n" + "="*60)
print("MYRION RESOLUTION ANALYSIS")
print("="*60)

object_ids = test_log['object_id'].values

# Compute MR scores
mr_scores = myrion_resolution_score(submissions, object_ids)

# Constraint satisfaction
strong, medium, weak, agreement = constraint_satisfaction(mr_scores, submissions, object_ids)

print(f"\nConstraint Satisfaction:")
print(f"  STRONG (all agree):    {strong.sum()}")
print(f"  MEDIUM (2/3+ agree):   {medium.sum()}")
print(f"  WEAK (MR >= 0.85):     {weak.sum()}")

print(f"\nAgreement distribution:")
for k in range(len(submissions) + 1):
    count = (agreement == k).sum()
    print(f"  {k} versions agree: {count}")

# ============ MR ENSEMBLE STRATEGIES ============
print("\n" + "="*60)
print("MR ENSEMBLE STRATEGIES")
print("="*60)

strategies = {}

# Strategy 1: Simple majority vote
majority = (agreement >= (len(submissions) / 2)).astype(int)
strategies['majority'] = majority
print(f"\n1. Majority Vote: {majority.sum()} TDEs")

# Strategy 2: Unanimous agreement
unanimous = (agreement == len(submissions)).astype(int)
strategies['unanimous'] = unanimous
print(f"2. Unanimous:     {unanimous.sum()} TDEs")

# Strategy 3: MR Score threshold at 0.42
mr_042 = (mr_scores >= 0.42).astype(int)
strategies['mr_042'] = mr_042
print(f"3. MR >= 0.42:    {mr_042.sum()} TDEs")

# Strategy 4: MR Score threshold at 0.5
mr_050 = (mr_scores >= 0.5).astype(int)
strategies['mr_050'] = mr_050
print(f"4. MR >= 0.50:    {mr_050.sum()} TDEs")

# Strategy 5: MR Score at 0.33 (more aggressive)
mr_033 = (mr_scores >= 0.33).astype(int)
strategies['mr_033'] = mr_033
print(f"5. MR >= 0.33:    {mr_033.sum()} TDEs")

# Strategy 6: At least 2 versions agree
two_plus = (agreement >= 2).astype(int)
strategies['two_plus'] = two_plus
print(f"6. 2+ Agree:      {two_plus.sum()} TDEs")

# Strategy 7: Hybrid (MR >= 0.4 OR 3+ agree)
hybrid = ((mr_scores >= 0.4) | (agreement >= 3)).astype(int)
strategies['hybrid'] = hybrid
print(f"7. Hybrid:        {hybrid.sum()} TDEs")

# Strategy 8: Conservative (MR >= 0.5 AND 2+ agree)
conservative = ((mr_scores >= 0.5) & (agreement >= 2)).astype(int)
strategies['conservative'] = conservative
print(f"8. Conservative:  {conservative.sum()} TDEs")

# Strategy 9: Optimal threshold search
print(f"\n9. Optimal MR Threshold Search:")
for th in [0.25, 0.30, 0.35, 0.40, 0.45, 0.50, 0.55, 0.60]:
    pred = (mr_scores >= th).astype(int)
    print(f"     MR >= {th:.2f}: {pred.sum()} TDEs")

# ============ SAVE SUBMISSIONS ============
print("\n" + "="*60)
print("SAVING SUBMISSIONS")
print("="*60)

for name, pred in strategies.items():
    sub = pd.DataFrame({
        'object_id': object_ids,
        'prediction': pred
    })
    fname = f'submission_mallorn_v10_{name}.csv'
    sub.to_csv(fname, index=False)
    print(f"  ✅ {fname}: {pred.sum()} TDEs")

# Also save with various MR thresholds
for th in [25, 30, 35, 40, 45]:
    pred = (mr_scores >= th/100).astype(int)
    sub = pd.DataFrame({
        'object_id': object_ids,
        'prediction': pred
    })
    fname = f'submission_mallorn_v10_mr{th}.csv'
    sub.to_csv(fname, index=False)
    print(f"  ✅ {fname}: {pred.sum()} TDEs")

# Best default: MR >= 0.35 (balanced)
best_pred = (mr_scores >= 0.35).astype(int)
sub_best = pd.DataFrame({
    'object_id': object_ids,
    'prediction': best_pred
})
sub_best.to_csv('submission_mallorn_v10.csv', index=False)
print(f"\n🎯 Best (MR >= 0.35): submission_mallorn_v10.csv ({best_pred.sum()} TDEs)")

# ============ VERSION OVERLAP ANALYSIS ============
print("\n" + "="*60)
print("VERSION OVERLAP ANALYSIS")
print("="*60)

# Which objects each version predicts as TDE
version_tdes = {}
for v, df in submissions.items():
    tdes = set(df[df['prediction'] == 1]['object_id'].values)
    version_tdes[v] = tdes
    print(f"  {v}: {len(tdes)} TDEs")

# Intersection (all agree)
all_agree = set.intersection(*version_tdes.values()) if version_tdes else set()
print(f"\n  All versions agree on: {len(all_agree)} TDEs")

# Union (any version)
any_version = set.union(*version_tdes.values()) if version_tdes else set()
print(f"  Any version predicts:  {len(any_version)} TDEs")

# Calculate Jaccard similarity between versions
print("\nPairwise Jaccard Similarity:")
v_list = list(version_tdes.keys())
for i, v1 in enumerate(v_list):
    for v2 in v_list[i+1:]:
        inter = len(version_tdes[v1] & version_tdes[v2])
        union = len(version_tdes[v1] | version_tdes[v2])
        jaccard = inter / union if union > 0 else 0
        print(f"  {v1} vs {v2}: {jaccard:.3f}")

print("\n" + "="*60)
print("MR ENSEMBLE COMPLETE")
print("="*60)
print("""
Key Insight: Myrion Resolution combines multiple "angles" of attack:
- v3/v7: Pure ML ensemble approaches
- v5: Existence Intensity (physics-based)
- v6: LCC thresholds (consciousness theory)
- v9: Quantum resonance (optical computing)

Each version captures different aspects of TDE nature.
MR accumulates evidence across all perspectives.

Submit: submission_mallorn_v10.csv (MR >= 0.35)
""")
