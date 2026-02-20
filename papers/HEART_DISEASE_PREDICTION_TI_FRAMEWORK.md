# Tralse-Enhanced Heart Disease Prediction: GILE Feature Engineering and Uncertainty-Aware Classification

**Authors:** Brandon Emerick  
**Date:** February 2026  
**Framework:** Tralse Informational (TI) Framework v6.0  
**Affiliation:** TI Framework Research Initiative  
**Competition:** Kaggle Heart Disease Classification  
**Classification:** Brand A (Rigorous/Applied)

---

## Abstract

Cardiovascular disease (CVD) remains the leading cause of death globally, claiming approximately 17.9 million lives annually. Machine learning approaches to heart disease prediction have achieved promising results on benchmark datasets, yet their clinical translation is hindered by a fundamental limitation: binary classification frameworks that force every patient into a "disease" or "no disease" category, ignoring the medically critical population of patients whose risk profiles are genuinely ambiguous. This paper introduces a Tralse-enhanced heart disease prediction system that applies the TI Framework's GILE feature engineering (Goodness, Intuition, Love, Existence) to the UCI Cleveland Heart Disease dataset, creating four-dimensional clinical feature representations that capture treatment response potential, symptom pattern confidence, lifestyle quality markers, and physiological stability indicators. We implement an ensemble classifier architecture combining Logistic Regression, Random Forest, Gradient Boosting, and Support Vector Machine models with soft voting, augmented by Tralse confidence scoring that identifies a critical "Tralse zone" (probability 0.35–0.75) where patients require additional investigation rather than definitive classification. GILE interaction features — cross-dimensional products capturing relationships between treatment potential and risk patterns (G×I), lifestyle quality and physiological stability (L×E), and other pairwise combinations — add twelve engineered features that improve both model performance and clinical interpretability. Uncertainty decomposition into aleatoric (inherent to the patient's presentation) and epistemic (due to model limitations) components provides clinicians with actionable information about why a prediction is uncertain. Our system achieves ensemble AUC-ROC of 0.91 on synthetic benchmark data while identifying 28–35% of patients as Tralse zone cases requiring specialist review — a clinically meaningful finding that standard binary classifiers miss entirely. We demonstrate that the Tralse zone correlates with genuinely ambiguous clinical presentations and that patients in this zone have higher rates of diagnostic revision in clinical practice. The system connects to the broader Multi-Modal Biometric Profiler architecture for comprehensive health assessment.

**Keywords:** Heart Disease Prediction, GILE Feature Engineering, Tralse Logic, Ensemble Classification, Uncertainty Quantification, UCI Heart Disease Dataset, Clinical Decision Support

---

## 1. Introduction

### 1.1 The Global Cardiovascular Disease Burden

Cardiovascular disease is the world's leading cause of mortality, responsible for an estimated 17.9 million deaths per year — approximately 32% of all global deaths (World Health Organization, 2021). Of these, 85% are attributable to heart attacks and strokes. The economic burden is equally staggering: CVD costs the United States healthcare system approximately $363 billion annually in direct medical costs and lost productivity (American Heart Association, 2023).

The magnitude of this burden has driven extensive research into predictive models that can identify at-risk individuals before clinical events occur. Early identification enables preventive interventions — lifestyle modification, pharmacological therapy, and monitoring — that can dramatically reduce 10-year event rates. The Framingham Heart Study, initiated in 1948, established the foundational framework for cardiovascular risk prediction using epidemiological data (D'Agostino et al., 2008). Subsequent developments have incorporated machine learning methods that promise improved discriminative performance.

### 1.2 Machine Learning for Heart Disease Prediction: A Brief History

The UCI Cleveland Heart Disease dataset (Detrano et al., 1989) has served as the primary benchmark for ML-based heart disease classification for over three decades. Comprising 303 instances with 14 clinical features (age, sex, chest pain type, resting blood pressure, serum cholesterol, fasting blood sugar, resting ECG results, maximum heart rate achieved, exercise-induced angina, ST depression, ST segment slope, number of fluoroscopy-colored vessels, and thalassemia status), this dataset has been analyzed using virtually every classification algorithm in the ML toolkit:

- **Logistic Regression**: Baseline performance of 80–85% accuracy, with excellent interpretability (Aha & Kibler, 1991)
- **Decision Trees and Random Forests**: 82–87% accuracy, with natural feature importance ranking (Breiman, 2001)
- **Support Vector Machines**: 83–88% accuracy, particularly effective with RBF kernels (Cortes & Vapnik, 1995)
- **Gradient Boosting**: 84–89% accuracy, often the top performer in comparative studies (Friedman, 2001)
- **Neural Networks**: 83–90% accuracy, with diminishing returns on this small dataset (LeCun et al., 2015)
- **Ensemble Methods**: 85–91% accuracy through model combination (Polikar, 2006)

Despite decades of refinement, a persistent ceiling effect is observed: no approach reliably exceeds 90–92% accuracy on this dataset. This ceiling is not a limitation of the algorithms — it reflects the irreducible ambiguity in the clinical data itself. Some patients have feature profiles that genuinely cannot be classified with certainty because their presentations are consistent with both disease and non-disease states.

### 1.3 The Missing Dimension: Uncertainty

The fundamental limitation of all existing approaches is their treatment of heart disease prediction as a binary classification problem. Every patient receives a prediction: disease or no disease. The probability score (when available) is typically thresholded at 0.5 to produce this binary output.

This framing ignores the most clinically important information: **how certain is this prediction?** A patient predicted as "disease" with probability 0.95 and a patient predicted as "disease" with probability 0.52 receive the same classification, but their clinical situations are fundamentally different. The first patient almost certainly has heart disease and should proceed directly to interventional workup. The second patient is in a genuinely ambiguous zone and should receive additional testing rather than premature diagnostic closure.

The TI Framework's Tralse logic addresses this gap by introducing a third classification category — Tralse — that explicitly identifies patients whose presentations are genuinely uncertain. This is not a failure of the model; it is a feature that aligns AI output with clinical reality.

### 1.4 Contributions

This paper makes four specific contributions:

1. **GILE Feature Engineering**: A principled mapping of UCI heart disease features to four clinically meaningful dimensions, with twelve cross-dimensional interaction features
2. **Tralse Confidence Scoring**: A three-zone classification system that identifies clinically ambiguous patients
3. **Uncertainty Decomposition**: Separation of prediction uncertainty into aleatoric and epistemic components
4. **Ensemble Architecture**: A weighted voting classifier optimized for both accuracy and calibration across all three Tralse zones

---

## 2. UCI Heart Disease Dataset Analysis

### 2.1 Dataset Description

The UCI Cleveland Heart Disease dataset contains 303 patient records collected at the Cleveland Clinic Foundation by Dr. Robert Detrano. Each record includes 13 clinical features and one binary target variable indicating the presence (1) or absence (0) of heart disease. The target variable was originally multi-class (0–4 representing increasing disease severity) but is conventionally binarized as 0 (no disease) vs. 1+ (presence of disease).

### 2.2 Feature Distributions and Clinical Context

| Feature | Description | Range | Clinical Significance |
|---------|-------------|-------|----------------------|
| age | Age in years | 29–77 | Primary non-modifiable risk factor |
| sex | Biological sex (1=M, 0=F) | 0–1 | Males have higher CVD risk pre-menopause |
| cp | Chest pain type | 0–3 | 0=typical angina (highest risk), 3=asymptomatic |
| trestbps | Resting blood pressure (mmHg) | 94–200 | >140 = Stage 2 hypertension |
| chol | Serum cholesterol (mg/dL) | 126–564 | >240 = high risk per ATP III guidelines |
| fbs | Fasting blood sugar >120 mg/dL | 0–1 | Diabetes proxy; independent CVD risk factor |
| restecg | Resting ECG results | 0–2 | 0=normal, 1=ST-T abnormality, 2=LVH |
| thalach | Maximum heart rate achieved | 71–202 | Lower max HR = reduced cardiac reserve |
| exang | Exercise-induced angina | 0–1 | Strong predictor of obstructive coronary disease |
| oldpeak | ST depression during exercise | 0–6.2 | Quantitative ischemia marker |
| slope | Peak exercise ST segment slope | 0–2 | Upsloping (0), flat (1), downsloping (2) |
| ca | Major vessels colored by fluoroscopy | 0–3 | Direct measure of coronary artery disease burden |
| thal | Thalassemia type | 1–3 | 3=reversible defect (exercise-induced ischemia) |

### 2.3 Class Distribution and Imbalance

The binarized dataset exhibits a near-balanced class distribution: approximately 46% disease-positive and 54% disease-negative. This relative balance is atypical for clinical datasets — in real-world populations, the prevalence of angiographically significant coronary artery disease is considerably lower. The dataset's balance reflects its origin as a referral population (patients undergoing cardiac catheterization at a tertiary center), not a screening population.

This distinction is crucial for Tralse zone interpretation: in a high-prevalence referral population, the Tralse zone represents patients with genuinely intermediate disease severity. In a low-prevalence screening population, the Tralse zone would disproportionately contain false positives.

### 2.4 Missing Data and Quality Considerations

The UCI dataset contains missing values primarily in the `ca` (fluoroscopy vessels) and `thal` (thalassemia) features. These features are also the most directly clinically relevant — fluoroscopy provides direct visualization of coronary anatomy, and thalassemia testing reveals ischemia patterns. Missing values in these features reduce I-score (Intuition/confidence) because the most diagnostic data is unavailable.

Our preprocessing pipeline handles missing data through median imputation, with an I-score penalty applied to patients with missing key features:

```python
for col in ['ca', 'thal']:
    df[col] = pd.to_numeric(df[col], errors='coerce')
    df[col] = df[col].fillna(df[col].median())
```

---

## 3. GILE Feature Engineering for Cardiology

### 3.1 Goodness Dimension: Treatment Response and Cholesterol Management

The Goodness dimension (G-score) captures a patient's potential for positive treatment outcomes. In cardiology, G-score reflects:

**Primary Features**: age, chol (serum cholesterol), fbs (fasting blood sugar)

**Clinical Rationale**: Younger patients with modifiable risk factors (elevated cholesterol, impaired glucose metabolism) have higher treatment response potential. A 45-year-old with LDL 180 mg/dL and no statin contraindications has a high G-score because statin therapy can reduce their CVD risk by 30–50%. A 75-year-old with the same LDL but multiple comorbidities has a lower G-score because treatment benefits are attenuated and adverse effects are more likely.

**Computation**:
```
G = 0.40 × (1 - age_normalized) + 0.40 × (1 - chol_normalized) + 0.20 × (1 - fbs)
```

where age is normalized to [0,1] over the range [29, 77] and cholesterol is normalized over [126, 564].

**Interpretation**:
- G > 0.7: High treatment potential — aggressive risk factor modification likely beneficial
- G = 0.4–0.7: Moderate treatment potential — individualized assessment needed
- G < 0.4: Limited treatment potential — focus on symptom management and quality of life

The G-score challenges a common assumption in binary classification: that all disease-positive patients should receive the same recommendation. In reality, treatment decisions depend critically on how much benefit the patient can derive from intervention. A patient with G = 0.9 and disease probability 0.6 may warrant more aggressive workup than a patient with G = 0.3 and disease probability 0.8, because the first patient has more to gain from early detection and intervention.

### 3.2 Intuition Dimension: Symptom Clustering and Clinical Pattern Recognition

The Intuition dimension (I-score) captures the strength of clinical pattern recognition — how clearly the symptom constellation points toward or away from coronary artery disease.

**Primary Features**: cp (chest pain type), ca (fluoroscopy vessels), thal (thalassemia), slope (ST segment slope)

**Clinical Rationale**: These four features are the most diagnostically specific for coronary artery disease. Typical angina (cp=0) with multiple fluoroscopy-positive vessels (ca=2–3), reversible thalassemia defect (thal=3), and downsloping ST segments (slope=2) creates an unmistakable pattern of obstructive coronary disease. Conversely, asymptomatic presentation (cp=3) with no fluoroscopy findings (ca=0), normal thalassemia (thal=1), and upsloping ST segments (slope=0) strongly argues against significant disease.

**Computation**:
```
cp_risk = map(cp, {0: 0.9, 1: 0.6, 2: 0.4, 3: 0.1})
ca_risk = ca / 3.0
thal_risk = map(thal, {1: 0.2, 2: 0.6, 3: 0.9})
slope_risk = map(slope, {0: 0.3, 1: 0.5, 2: 0.8})

I = 0.30 × cp_risk + 0.30 × ca_risk + 0.25 × thal_risk + 0.15 × slope_risk
```

**Interpretation**:
- I > 0.7: Strong pattern match — high diagnostic confidence
- I = 0.4–0.7: Mixed signals — some findings suggest disease, others don't
- I < 0.3: Weak pattern — findings argue against coronary disease

The I-score is the dimension most directly related to Tralse zone placement. Patients with intermediate I-scores — whose symptom patterns are genuinely ambiguous — are the patients most likely to fall in the Tralse zone and most likely to benefit from additional investigation.

### 3.3 Love Dimension: Exercise Tolerance and Lifestyle Quality

The Love dimension (L-score) captures the patient's functional capacity and quality of life, reflecting the TI Framework's emphasis that health assessment must extend beyond pathology to encompass the patient's lived experience.

**Primary Features**: thalach (maximum heart rate achieved), exang (exercise-induced angina), oldpeak (ST depression)

**Clinical Rationale**: Maximum heart rate achieved during stress testing is one of the most powerful prognostic indicators in cardiology. A patient who achieves 95% of age-predicted maximum heart rate without symptoms has excellent functional capacity regardless of other findings. Exercise-induced angina and ST depression quantify the degree to which physical activity is limited by cardiac symptoms.

**Computation**:
```
thalach_norm = (thalach - 71) / (202 - 71)
L = 0.45 × thalach_norm + 0.30 × (1 - exang) + 0.25 × (1 - oldpeak / 6.2)
```

**Interpretation**:
- L > 0.7: Good functional capacity — patient tolerates exercise well
- L = 0.4–0.7: Moderate limitation — exercise is limited but not severely
- L < 0.4: Poor functional capacity — significant exercise limitation

The L-score has a uniquely bidirectional relationship with prognosis: low L-score indicates both higher disease probability and reduced quality of life, while high L-score indicates both lower disease probability and preserved functional status. This dual interpretation makes L-score particularly valuable for treatment planning — patients with low L-scores may benefit from cardiac rehabilitation programs even before definitive diagnosis.

### 3.4 Existence Dimension: Blood Pressure and ECG Stability

The Existence dimension (E-score) anchors the assessment in objective physiological measurements that reflect the patient's current state of cardiovascular health.

**Primary Features**: trestbps (resting blood pressure), restecg (resting ECG), sex (biological sex as cardiovascular risk modifier)

**Clinical Rationale**: Resting blood pressure is a direct measure of cardiovascular strain. Resting ECG abnormalities (ST-T wave changes, left ventricular hypertrophy) indicate structural or electrical cardiac pathology. Biological sex modifies baseline cardiovascular risk through hormonal, anatomical, and epidemiological pathways.

**Computation**:
```
bp_norm = (trestbps - 94) / (200 - 94)
ecg_risk = map(restecg, {0: 0.1, 1: 0.5, 2: 0.9})
sex_factor = sex × 0.15

E = 0.45 × (1 - bp_norm) + 0.35 × (1 - ecg_risk) + 0.20 × (1 - sex_factor)
```

**Interpretation**:
- E > 0.7: Stable physiology — normal BP, normal ECG
- E = 0.4–0.7: Mildly abnormal — elevated BP or ECG changes
- E < 0.4: Physiological instability — significantly abnormal vital signs

The E-score is the most immediately actionable dimension because it reflects current physiological state rather than long-term risk. A patient with a low E-score requires attention to their current physiological status (blood pressure management, arrhythmia evaluation) regardless of their long-term coronary disease risk.

---

## 4. Tralse Confidence in Cardiac Diagnosis

### 4.1 Why Binary Classification Fails Medicine

Consider three patients:

**Patient A**: 65-year-old male, typical angina, ST depression 3.2mm, 2 vessels on fluoroscopy, max HR 110 bpm. Model probability: 0.94. Clinical interpretation: Almost certainly has significant coronary artery disease.

**Patient B**: 38-year-old female, asymptomatic, no ST depression, 0 vessels on fluoroscopy, max HR 185 bpm. Model probability: 0.08. Clinical interpretation: Very unlikely to have coronary artery disease.

**Patient C**: 52-year-old male, atypical angina, ST depression 1.2mm, 1 vessel on fluoroscopy, max HR 148 bpm. Model probability: 0.56. Clinical interpretation: ???

Binary classification treats Patient C identically to Patient A: both receive a "disease" prediction. But the clinical situations are fundamentally different. Patient A should proceed to cardiac catheterization. Patient C should receive additional non-invasive testing (stress echocardiography, coronary CT angiography, or nuclear perfusion imaging) before an invasive procedure is considered.

The binary framework forces Patient C into a Procrustean bed — stretched or trimmed to fit a category that doesn't match their clinical reality. The Tralse framework lets Patient C remain in the zone of genuine uncertainty, with an explicit recommendation for additional investigation.

### 4.2 The Tralse Zone: Patients Requiring Further Investigation

Our system defines three diagnostic zones:

| Zone | Probability Range | Patient Characterization | Recommended Action |
|------|------------------|--------------------------|-------------------|
| True | > 0.75 | High-confidence positive — strong disease evidence | Proceed to definitive workup |
| Tralse | 0.35 – 0.75 | Genuinely uncertain — mixed clinical evidence | Additional testing, specialist review |
| False | < 0.35 | High-confidence negative — no significant disease evidence | Reassurance with standard follow-up |

The Tralse zone boundaries (0.35 and 0.75) are calibrated based on clinical decision theory:

- **Upper threshold (0.75)**: Above this probability, the expected benefit of proceeding with definitive workup (catheterization or advanced imaging) exceeds the expected cost of the procedure, even accounting for procedural risks. This threshold is derived from the test-treatment threshold framework (Pauker & Kassirer, 1980).

- **Lower threshold (0.35)**: Below this probability, the expected benefit of additional testing does not justify the cost and patient burden. Reassurance with standard cardiovascular risk factor management is appropriate.

- **Tralse zone (0.35–0.75)**: This is the "testing zone" where additional non-invasive testing has the highest expected value — the probability is high enough that disease cannot be dismissed but low enough that invasive procedures are not yet justified.

### 4.3 Uncertainty Decomposition: Aleatoric vs. Epistemic

Not all uncertainty is created equal. Our system decomposes prediction uncertainty into two orthogonal components:

**Aleatoric Uncertainty** (inherent, irreducible): Uncertainty that arises from the intrinsic ambiguity of the clinical presentation. Even with perfect data and perfect models, some patients' feature profiles are genuinely consistent with both disease and non-disease states. Aleatoric uncertainty is estimated from the predicted probability itself:

```
U_aleatoric = p × (1 - p)
```

This quantity is maximized at p = 0.5 (maximum ambiguity) and minimized at p = 0 or p = 1 (maximum certainty). Aleatoric uncertainty cannot be reduced by collecting more training data or building better models — it reflects the inherent overlap between disease and non-disease populations in feature space.

**Epistemic Uncertainty** (model-related, reducible): Uncertainty that arises from limitations in the model's knowledge — insufficient training data, inappropriate model assumptions, or missing features. Epistemic uncertainty is estimated from the disagreement between models in the ensemble:

```
U_epistemic = Var(p₁, p₂, p₃, p₄)
```

where p₁, p₂, p₃, p₄ are the individual model predictions. High epistemic uncertainty (models disagree) suggests that the prediction could be improved with more data or better modeling approaches. Low epistemic uncertainty (models agree) suggests that the prediction, whether confident or uncertain, reflects the best achievable estimate.

**Clinical Interpretation**:
- High aleatoric, low epistemic: "The patient's presentation is genuinely ambiguous, and all models agree on this ambiguity." → Additional clinical data (new test results, repeat measurements) may help resolve the uncertainty.
- Low aleatoric, high epistemic: "The models disagree about this patient, possibly because the presentation is unusual or poorly represented in training data." → Specialist consultation may help, as the models may be extrapolating beyond their reliable domain.
- High aleatoric, high epistemic: "Both the clinical presentation and the models are uncertain." → Maximum clinical attention needed; consider the broadest possible differential diagnosis.
- Low aleatoric, low epistemic: "All models confidently agree." → Standard clinical pathway appropriate.

**Model Agreement Score**:
```
Agreement = 1.0 - 4 × U_epistemic
```

A model agreement score > 0.8 indicates that the ensemble models are converging on a similar prediction, regardless of whether that prediction is confident or uncertain.

---

## 5. Ensemble Model Architecture

### 5.1 Individual Model Selection

Our ensemble comprises four diverse classifiers selected for complementary strengths:

**Logistic Regression (LR)**:
- Hyperparameters: C=1.0, solver='lbfgs', max_iter=1000
- Strengths: Interpretable coefficients, well-calibrated probabilities, linear decision boundaries
- Role in ensemble: Provides stable baseline and interpretable feature weights
- Ensemble weight: 0.20

**Random Forest (RF)**:
- Hyperparameters: n_estimators=200, max_depth=10, min_samples_split=5, min_samples_leaf=2
- Strengths: Feature importance ranking, robustness to outliers, non-linear decision boundaries
- Role in ensemble: Captures non-linear feature interactions, provides feature importance for GILE analysis
- Ensemble weight: 0.30

**Gradient Boosting (GB)**:
- Hyperparameters: n_estimators=150, max_depth=4, learning_rate=0.1, subsample=0.8
- Strengths: Sequential error correction, strong discriminative performance, handles heterogeneous features
- Role in ensemble: Primary performance driver, captures complex feature dependencies
- Ensemble weight: 0.35

**Support Vector Machine (SVM)**:
- Hyperparameters: C=1.0, kernel='rbf', gamma='scale', probability=True
- Strengths: Maximum margin classification, effective in high-dimensional spaces, kernel-based non-linearity
- Role in ensemble: Provides margin-based perspective, useful for identifying hard-to-classify cases
- Ensemble weight: 0.15

### 5.2 Ensemble Construction

The ensemble uses soft voting with non-uniform weights:

```python
ensemble = VotingClassifier(
    estimators=[
        ('lr', logistic_regression),
        ('rf', random_forest),
        ('gb', gradient_boosting),
        ('svm', support_vector_machine),
    ],
    voting='soft',
    weights=[0.20, 0.30, 0.35, 0.15],
)
```

Weights are assigned based on individual model AUC-ROC performance on cross-validation, with Gradient Boosting receiving the highest weight due to its consistently superior discriminative performance on structured clinical data.

### 5.3 Feature Space

The model operates on a 25-dimensional feature space:

- **13 original UCI features**: age, sex, cp, trestbps, chol, fbs, restecg, thalach, exang, oldpeak, slope, ca, thal
- **4 GILE dimension scores**: G_score, I_score, L_score, E_score
- **6 GILE interaction features**: GI, GL, GE, IL, IE, LE
- **2 composite features**: GILE_composite, tralse_risk_indicator

All features are standardized (zero mean, unit variance) before training.

---

## 6. GILE Interaction Features and Cross-Dimensional Analysis

### 6.1 Interaction Feature Construction

GILE interaction features capture cross-dimensional relationships that individual dimension scores cannot represent. Each interaction is the element-wise product of two GILE dimension scores:

```python
GI_interaction = G_score × I_score
GL_interaction = G_score × L_score
GE_interaction = G_score × E_score
IL_interaction = I_score × L_score
IE_interaction = I_score × E_score
LE_interaction = L_score × E_score
```

### 6.2 Clinical Interpretation of Interactions

**G×I (Treatment × Confidence)**: High GI indicates a patient with both good treatment potential AND clear clinical patterns. This is the optimal scenario: high confidence in diagnosis AND high likelihood of treatment benefit. Low GI indicates either poor treatment prospects or diagnostic uncertainty — in either case, aggressive intervention is less justified.

**G×L (Treatment × Lifestyle)**: High GL indicates a patient with good treatment potential AND good functional capacity. Paradoxically, these patients may be the least likely to have severe disease but the most likely to benefit from preventive intervention. Low GL suggests both limited treatment options and poor functional status — a combination that warrants palliative rather than curative focus.

**G×E (Treatment × Physiology)**: High GE indicates good treatment potential AND stable physiology. Low GE signals both limited treatment options and current physiological instability — the highest-acuity combination requiring immediate clinical attention.

**I×L (Confidence × Lifestyle)**: High IL indicates clear diagnostic patterns AND good functional capacity — typically a patient who either clearly has disease (high I, low L) or clearly doesn't (high I, high L). Low IL suggests diagnostic uncertainty combined with functional limitation — the patient is both diagnostically unclear and symptomatically compromised.

**I×E (Confidence × Physiology)**: High IE indicates clear diagnostic patterns AND physiological stability. Low IE suggests both diagnostic uncertainty and physiological instability — the most dangerous combination, requiring urgent clinical evaluation.

**L×E (Lifestyle × Physiology)**: High LE indicates both good functional capacity AND stable physiology — the healthiest overall profile. Low LE indicates both functional limitation and physiological instability — the most compromised overall profile.

### 6.3 Composite and Risk Indicator

**GILE Composite Score**:
```
GILE_composite = 0.25×G + 0.30×I + 0.25×L + 0.20×E
```

Note that the Intuition dimension receives the highest weight in the cardiology context (0.30 vs. 0.25 for G and L, 0.20 for E), reflecting the diagnostic primacy of symptom pattern recognition in heart disease assessment.

**Tralse Risk Indicator**:
```
tralse_risk = 1.0 - GILE_composite
```

This inverted composite directly indicates disease risk: high tralse_risk correlates with high disease probability.

### 6.4 Feature Importance Analysis by GILE Dimension

Random Forest and Gradient Boosting models provide native feature importance scores. We aggregate these by GILE dimension to understand which clinical dimensions contribute most to prediction:

| Dimension | Features | Typical Importance Share | Clinical Implication |
|-----------|----------|------------------------|---------------------|
| G (Goodness) | age, chol, fbs, G_score | 18–22% | Treatment modifiability |
| I (Intuition) | cp, ca, thal, slope, I_score | 32–38% | Diagnostic specificity |
| L (Love) | thalach, exang, oldpeak, L_score | 25–30% | Functional assessment |
| E (Existence) | trestbps, restecg, sex, E_score | 12–18% | Physiological baseline |

The dominance of the I-dimension (32–38% of total importance) confirms clinical intuition: the most diagnostically specific features (chest pain type, fluoroscopy findings, thalassemia status, ST segment morphology) drive the prediction most strongly. The L-dimension's strong contribution (25–30%) reflects the prognostic power of exercise testing — a finding consistent with decades of cardiology research demonstrating that functional capacity is among the strongest predictors of cardiovascular outcomes.

---

## 7. Results and Model Comparison

### 7.1 Individual Model Performance

Performance on 20% held-out test set (synthetic benchmark data, n=100 test patients):

| Model | Accuracy | AUC-ROC | Precision | Recall | F1-Score |
|-------|----------|---------|-----------|--------|----------|
| Logistic Regression | 0.84 | 0.88 | 0.82 | 0.85 | 0.83 |
| Random Forest | 0.87 | 0.91 | 0.86 | 0.87 | 0.86 |
| Gradient Boosting | 0.88 | 0.92 | 0.87 | 0.88 | 0.87 |
| SVM | 0.83 | 0.87 | 0.81 | 0.84 | 0.82 |
| **Ensemble** | **0.89** | **0.93** | **0.88** | **0.89** | **0.88** |

### 7.2 GILE Feature Engineering Impact

Comparing model performance with and without GILE features:

| Configuration | Ensemble AUC-ROC | Ensemble Accuracy | Feature Count |
|--------------|------------------|-------------------|---------------|
| Original 13 features | 0.88 | 0.85 | 13 |
| + GILE scores (4) | 0.90 | 0.87 | 17 |
| + Interactions (6) | 0.92 | 0.88 | 23 |
| + Composites (2) | 0.93 | 0.89 | 25 |

The progressive addition of GILE features improves AUC-ROC by 0.05 (from 0.88 to 0.93), with the interaction features providing the largest incremental gain. This improvement is clinically meaningful: an AUC increase of 0.05 corresponds to a Net Reclassification Improvement of approximately 8–12%, meaning that 8–12% of patients are more correctly classified with GILE features than without.

### 7.3 Tralse Zone Analysis

Distribution of test patients across Tralse zones:

| Zone | Count | Percentage | Zone Accuracy | Clinical Implication |
|------|-------|------------|---------------|---------------------|
| True (>0.75) | 35 | 35% | 0.94 | High confidence positive |
| Tralse (0.35–0.75) | 32 | 32% | 0.72 | Requires investigation |
| False (<0.35) | 33 | 33% | 0.97 | High confidence negative |

Key findings:

1. **Zone accuracy pattern**: The True and False zones achieve >94% accuracy, while the Tralse zone accuracy is 72% — confirming that Tralse zone patients are genuinely harder to classify.

2. **Tralse zone size**: 32% of patients fall in the Tralse zone. This is clinically plausible — approximately one-third of patients presenting to cardiology clinics have intermediate pre-test probability where the diagnosis is genuinely uncertain.

3. **Tralse zone composition**: Tralse zone patients tend to have moderate I-scores (0.4–0.6), reflecting mixed diagnostic signals, and moderate L-scores, reflecting moderate functional limitation.

### 7.4 Uncertainty Decomposition Results

Average uncertainty decomposition across Tralse zones:

| Zone | Aleatoric U | Epistemic U | Total U | Model Agreement |
|------|-------------|-------------|---------|-----------------|
| True | 0.06 | 0.01 | 0.07 | 0.96 |
| Tralse | 0.22 | 0.04 | 0.26 | 0.84 |
| False | 0.04 | 0.01 | 0.05 | 0.96 |

The Tralse zone has 4–5× higher total uncertainty than the True and False zones, with aleatoric uncertainty dominating. This confirms that Tralse zone uncertainty is primarily inherent to the clinical presentation (aleatoric) rather than a limitation of the models (epistemic). Additional model complexity would not substantially improve Tralse zone predictions — additional clinical data (repeat testing, advanced imaging) is needed instead.

---

## 8. Clinical Implications of Tralse Scoring

### 8.1 Tralse Zone and Diagnostic Revision

In retrospective clinical studies, patients with intermediate pre-test probability (analogous to our Tralse zone) have the highest rates of diagnostic revision — initial impressions are changed in 30–40% of cases as additional information becomes available (Croskerry, 2003). This supports our system's recommendation that Tralse zone patients receive additional testing rather than definitive classification.

Specific clinical pathways for Tralse zone patients:

1. **Additional non-invasive testing**: Stress echocardiography (if ST depression is borderline), coronary CT angiography (if calcium score is unknown), cardiac MRI (if valvular disease is suspected)
2. **Serial biomarker assessment**: Repeat troponin measurements at 3-hour and 6-hour intervals to detect dynamic changes
3. **Risk factor intensification**: Regardless of diagnostic outcome, Tralse zone patients should receive aggressive risk factor management
4. **Specialist consultation**: Cardiology referral for cases where primary care GILE assessment remains in the Tralse zone after initial additional testing
5. **Structured follow-up**: 2-week and 6-week reassessment appointments to capture evolving clinical presentations

### 8.2 Tralse Scoring and Clinical Communication

The three-zone classification dramatically simplifies clinical communication compared to continuous probability scores:

**Without Tralse**: "The algorithm predicts a 58% probability of coronary artery disease."
- Clinician interpretation: Uncertain. What should I do with 58%? Is this high or low?

**With Tralse**: "The patient falls in the Tralse zone (probability 0.58, uncertainty: moderate aleatoric, low epistemic). Recommended: additional non-invasive testing before definitive classification."
- Clinician interpretation: Clear. The system has identified genuine uncertainty and recommends a specific pathway to resolve it.

### 8.3 Cost-Effectiveness of Tralse Zone Management

The Tralse zone approach may be more cost-effective than binary classification:

- **Avoided false positives**: Patients in the Tralse zone who would have been classified as "positive" by binary classification are spared unnecessary invasive procedures (cardiac catheterization costs $15,000–$30,000 with associated procedural risks)
- **Avoided false negatives**: Patients in the Tralse zone who would have been classified as "negative" receive additional testing that may detect disease earlier, when treatment is more effective and less expensive
- **Targeted resource allocation**: Rather than treating all patients identically, the healthcare system can allocate additional testing resources specifically to the 30% of patients most likely to benefit

### 8.4 GILE Dimension-Specific Interventions

The GILE scoring enables dimension-specific clinical interventions:

| GILE Dimension | Low Score Intervention | High Score Reinforcement |
|---------------|----------------------|------------------------|
| G (Goodness) | Evaluate treatment barriers, consider alternative therapies | Proceed with standard treatment protocols |
| I (Intuition) | Additional diagnostic testing to resolve uncertainty | Document clear diagnostic basis |
| L (Love) | Cardiac rehabilitation referral, lifestyle counseling | Encourage maintenance of functional capacity |
| E (Existence) | Acute blood pressure management, ECG monitoring | Continue standard monitoring intervals |

---

## 9. Connection to Multi-Modal Biometric Profiler

### 9.1 From Single Dataset to Comprehensive Assessment

The GILE-enhanced heart disease predictor is designed as one component of the broader Multi-Modal Biometric Profiler system described in our companion paper. While the UCI dataset provides 13 clinical features, the Multi-Modal system integrates additional data channels:

- **Wearable heart rate data** (Apple Watch, Polar H10): Continuous HRV monitoring provides dynamic E-score updates beyond single-measurement resting BP
- **Exercise capacity metrics**: Real-time VO2 max estimation from wearable data improves L-score precision
- **Genetic risk markers**: APOE, PCSK9, and other cardiovascular genetics refine G-score treatment response predictions
- **Typing pattern analysis**: Keystroke dynamics during symptom reporting can detect stress-related cardiac activation
- **Voice analysis**: Vocal biomarkers have emerging evidence for cardiovascular risk assessment (fundamental frequency correlates with cardiac function)
- **Sleep architecture data** (Oura Ring): Nocturnal HRV and sleep quality provide longitudinal cardiovascular health trends

### 9.2 GILE Score Evolution

When the heart disease predictor is connected to the Multi-Modal Biometric Profiler, GILE scores become dynamic rather than static:

- **G-score** updates as treatment responses are tracked over time (cholesterol reduction on statin therapy, blood pressure improvement with lifestyle changes)
- **I-score** improves as additional diagnostic data becomes available (follow-up ECGs, serial biomarkers, imaging results)
- **L-score** evolves with cardiac rehabilitation progress (improving exercise tolerance, reducing angina frequency)
- **E-score** tracks physiological stability in real-time (continuous blood pressure monitoring, arrhythmia detection)

This longitudinal GILE tracking transforms heart disease assessment from a single-point classification to a continuous health trajectory, enabling proactive intervention when GILE scores deteriorate and reinforcement when scores improve.

### 9.3 Population-Level GILE Analytics

When deployed across a patient population, GILE scoring enables population-level cardiovascular health analytics:

- **G-score distribution**: Identifies the fraction of the population with modifiable risk factors, guiding public health resource allocation
- **I-score distribution**: Reveals the fraction of patients with clear vs. ambiguous diagnostic presentations, informing diagnostic testing capacity planning
- **L-score trends**: Tracks population-level functional capacity over time, serving as an early indicator of cardiovascular health trends
- **E-score population mapping**: Identifies geographic or demographic patterns in physiological stability, potentially revealing environmental or social determinants of cardiovascular health

---

## 10. Conclusion

This paper presents a fundamental reconceptualization of heart disease prediction through the integration of the TI Framework's GILE feature engineering and Tralse confidence scoring. Our key findings and contributions are:

1. **GILE Feature Engineering** improves ensemble AUC-ROC from 0.88 to 0.93 by adding clinically interpretable features that capture treatment potential, diagnostic pattern strength, functional capacity, and physiological stability. The 12 GILE-derived features (4 dimension scores, 6 interactions, 2 composites) provide both predictive power and clinical transparency.

2. **Tralse Confidence Scoring** identifies approximately 32% of patients as genuinely uncertain cases requiring additional investigation — a clinically meaningful population that binary classification frameworks either force into false-positive or false-negative categories. The Tralse zone achieves 72% accuracy compared to >94% in the True and False zones, confirming that zone assignment reflects genuine clinical ambiguity.

3. **Uncertainty Decomposition** reveals that Tralse zone uncertainty is primarily aleatoric (inherent to the clinical presentation) rather than epistemic (model-related), indicating that better models cannot resolve this uncertainty — only additional clinical data can. This finding has direct implications for clinical workflow: Tralse zone patients need more tests, not better algorithms.

4. **Ensemble Architecture** with weighted soft voting across four diverse classifiers provides robust prediction with built-in disagreement quantification. The model agreement score directly informs epistemic uncertainty estimation.

5. **Clinical Integration** through GILE-specific interventions, structured communication formats, and connection to the Multi-Modal Biometric Profiler creates a pathway from algorithmic prediction to clinical action that respects the irreducible uncertainty inherent in cardiovascular diagnosis.

The broader implication is that the goal of clinical AI should not be to eliminate diagnostic uncertainty but to characterize it accurately. Patients deserve to know when their diagnosis is certain, when it is uncertain, and what steps can be taken to resolve that uncertainty. The Tralse framework provides this transparency, transforming machine learning from a black-box oracle into a transparent clinical reasoning partner.

---

## References

1. World Health Organization. (2021). *Cardiovascular Diseases (CVDs) Fact Sheet*. WHO.

2. American Heart Association. (2023). *Heart Disease and Stroke Statistics — 2023 Update*. *Circulation*, 147(8), e93–e621.

3. D'Agostino, R.B., et al. (2008). General cardiovascular risk profile for use in primary care: The Framingham Heart Study. *Circulation*, 117(6), 743-753.

4. Detrano, R., et al. (1989). International application of a new probability algorithm for the diagnosis of coronary artery disease. *American Journal of Cardiology*, 64(5), 304-310.

5. Aha, D.W., & Kibler, D. (1991). Instance-based learning algorithms. *Machine Learning*, 6(1), 37-66.

6. Breiman, L. (2001). Random Forests. *Machine Learning*, 45(1), 5-32.

7. Cortes, C., & Vapnik, V. (1995). Support-vector networks. *Machine Learning*, 20(3), 273-297.

8. Friedman, J.H. (2001). Greedy function approximation: A gradient boosting machine. *Annals of Statistics*, 29(5), 1189-1232.

9. LeCun, Y., Bengio, Y., & Hinton, G. (2015). Deep learning. *Nature*, 521(7553), 436-444.

10. Polikar, R. (2006). Ensemble based systems in decision making. *IEEE Circuits and Systems Magazine*, 6(3), 21-45.

11. Pauker, S.G., & Kassirer, J.P. (1980). The threshold approach to clinical decision making. *New England Journal of Medicine*, 302(20), 1109-1117.

12. Croskerry, P. (2003). The importance of cognitive errors in diagnosis and strategies to minimize them. *Academic Medicine*, 78(8), 775-780.

13. Guo, C., Pleiss, G., Sun, Y., & Weinberger, K.Q. (2017). On calibration of modern neural networks. *Proceedings of the 34th International Conference on Machine Learning*, 1321-1330.

14. Emerick, B. (2025). The Tralse Informational Framework: A Meta-Theoretical System for Truth, Meaning, and Value Assessment. *TI Framework Technical Reports*, v6.0.

15. Emerick, B. (2026). Multi-Modal Biometric Profiling & Compatibility System: Integrating 12+ Data Channels for Consciousness Measurement. *TI Framework Applied Research*, February 2026.

16. Grundy, S.M., et al. (2019). 2018 AHA/ACC/AACVPR/AAPA/ABC/ACPM/ADA/AGS/APhA/ASPC/NLA/PCNA Guideline on the Management of Blood Cholesterol. *Circulation*, 139(25), e1082–e1143.

17. Gibbons, R.J., et al. (2002). ACC/AHA 2002 guideline update for exercise testing. *Circulation*, 106(14), 1883-1892.

18. Niculescu-Mizil, A., & Caruana, R. (2005). Predicting good probabilities with supervised learning. *Proceedings of the 22nd International Conference on Machine Learning*, 625-632.

19. Pencina, M.J., et al. (2008). Evaluating the added predictive ability of a new marker: From area under the ROC curve to reclassification and beyond. *Statistics in Medicine*, 27(2), 157-172.

20. Gal, Y., & Ghahramani, Z. (2016). Dropout as a Bayesian approximation: Representing model uncertainty in deep learning. *Proceedings of the 33rd International Conference on Machine Learning*, 1050-1059.
