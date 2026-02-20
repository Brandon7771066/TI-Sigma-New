"""
TI-FRAMEWORK-ENHANCED HEART DISEASE CLASSIFIER
=================================================
Kaggle heart disease prediction competition engine using the UCI/Cleveland
dataset with 14 standard features enhanced by GILE-dimension feature
engineering and Tralse medical confidence scoring.

FEATURES:
- Load/generate UCI Cleveland heart disease data (14 features + target)
- GILE feature engineering mapping clinical features to TI dimensions
- Ensemble classifier (LogisticRegression, RandomForest, GradientBoosting, SVM)
- Tralse confidence scoring for medical prediction uncertainty
- Cross-validation, EDA, ROC data, Kaggle submission generation

GILE DIMENSIONS:
  G (Goodness/Treatment): Treatment response likelihood from age, cholesterol
  I (Intuition/Risk): Intuitive risk pattern from symptom clustering
  L (Love/Lifestyle): Exercise tolerance, resting HR, quality-of-life
  E (Existence/Stability): Blood pressure, ECG physiological stability

Tralse Medical Confidence:
  True zone (>0.75): High confidence prediction
  Tralse zone (0.35-0.75): Uncertain — flag for specialist review
  False zone (<0.35): High confidence negative prediction
"""

import numpy as np
import pandas as pd
from typing import Dict, List, Optional, Tuple, Any
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import RandomForestClassifier, GradientBoostingClassifier, VotingClassifier
from sklearn.svm import SVC
from sklearn.preprocessing import StandardScaler
from sklearn.model_selection import train_test_split, cross_val_score, StratifiedKFold
from sklearn.metrics import (
    accuracy_score, precision_score, recall_score, f1_score,
    roc_auc_score, confusion_matrix, classification_report, roc_curve
)
from sklearn.calibration import CalibratedClassifierCV
import warnings

warnings.filterwarnings('ignore')

FEATURE_COLUMNS = [
    'age', 'sex', 'cp', 'trestbps', 'chol', 'fbs',
    'restecg', 'thalach', 'exang', 'oldpeak', 'slope', 'ca', 'thal'
]

FEATURE_DESCRIPTIONS = {
    'age': 'Age in years',
    'sex': 'Sex (1=male, 0=female)',
    'cp': 'Chest pain type (0-3)',
    'trestbps': 'Resting blood pressure (mm Hg)',
    'chol': 'Serum cholesterol (mg/dl)',
    'fbs': 'Fasting blood sugar > 120 mg/dl (1=true)',
    'restecg': 'Resting ECG results (0-2)',
    'thalach': 'Maximum heart rate achieved',
    'exang': 'Exercise-induced angina (1=yes)',
    'oldpeak': 'ST depression induced by exercise',
    'slope': 'Slope of peak exercise ST segment (0-2)',
    'ca': 'Number of major vessels colored by fluoroscopy (0-3)',
    'thal': 'Thalassemia (1=normal, 2=fixed defect, 3=reversible defect)',
}

GILE_FEATURE_MAP = {
    'G': {
        'primary': ['age', 'chol', 'fbs'],
        'description': 'Treatment response likelihood (age, cholesterol management)',
        'weight': 0.25,
    },
    'I': {
        'primary': ['cp', 'ca', 'thal', 'slope'],
        'description': 'Intuitive risk pattern from symptom clustering',
        'weight': 0.30,
    },
    'L': {
        'primary': ['thalach', 'exang', 'oldpeak'],
        'description': 'Lifestyle/exercise tolerance and quality-of-life',
        'weight': 0.25,
    },
    'E': {
        'primary': ['trestbps', 'restecg', 'sex'],
        'description': 'Physiological stability (blood pressure, ECG)',
        'weight': 0.20,
    },
}

TRALSE_THRESHOLDS = {
    'true_threshold': 0.75,
    'false_threshold': 0.35,
    'specialist_review_band': (0.35, 0.75),
}


class HeartDiseasePredictor:
    """
    TI-Framework-Enhanced Heart Disease Classifier for Kaggle competition.
    Uses GILE feature engineering and Tralse confidence scoring.
    """

    def __init__(self):
        self.models = {}
        self.ensemble = None
        self.scaler = StandardScaler()
        self.feature_columns = []
        self.is_trained = False
        self.training_metrics = {}
        self.model_comparison = {}
        self.gile_feature_names = []
        self.best_model_name = None

    def load_data(self, filepath: str = None) -> pd.DataFrame:
        """Load heart disease dataset from CSV (Cleveland/UCI format)."""
        try:
            if filepath is None:
                return self.generate_sample_data()

            df = pd.read_csv(filepath)
            expected = FEATURE_COLUMNS + ['target']
            if not all(c in df.columns for c in expected):
                alt_names = {
                    'num': 'target', 'goal': 'target',
                    'condition': 'target', 'disease': 'target',
                }
                for old, new in alt_names.items():
                    if old in df.columns:
                        df = df.rename(columns={old: new})

            if 'target' in df.columns:
                df['target'] = (df['target'] > 0).astype(int)

            for col in ['ca', 'thal']:
                if col in df.columns:
                    df[col] = pd.to_numeric(df[col], errors='coerce')
                    df[col] = df[col].fillna(df[col].median())

            df = df.dropna(subset=['target']) if 'target' in df.columns else df
            return df

        except Exception as e:
            raise ValueError(f"Error loading data from {filepath}: {e}")

    def generate_sample_data(self, n_samples: int = 500) -> pd.DataFrame:
        """Generate realistic synthetic heart disease data for demo/testing."""
        np.random.seed(42)

        ages = np.random.normal(54, 9, n_samples).clip(29, 77).astype(int)
        sex = np.random.binomial(1, 0.68, n_samples)
        cp = np.random.choice([0, 1, 2, 3], n_samples, p=[0.47, 0.17, 0.28, 0.08])
        trestbps = np.random.normal(131, 17, n_samples).clip(94, 200).astype(int)
        chol = np.random.normal(246, 52, n_samples).clip(126, 564).astype(int)
        fbs = np.random.binomial(1, 0.15, n_samples)
        restecg = np.random.choice([0, 1, 2], n_samples, p=[0.48, 0.48, 0.04])
        thalach = np.random.normal(149, 23, n_samples).clip(71, 202).astype(int)
        exang = np.random.binomial(1, 0.33, n_samples)
        oldpeak = np.abs(np.random.normal(1.04, 1.16, n_samples)).clip(0, 6.2).round(1)
        slope = np.random.choice([0, 1, 2], n_samples, p=[0.07, 0.46, 0.47])
        ca = np.random.choice([0, 1, 2, 3], n_samples, p=[0.58, 0.22, 0.13, 0.07])
        thal = np.random.choice([1, 2, 3], n_samples, p=[0.55, 0.13, 0.32])

        risk = np.zeros(n_samples, dtype=float)
        risk += (ages - 40) / 40 * 0.15
        risk += sex * 0.10
        risk += (cp == 0).astype(float) * 0.15
        risk += (trestbps > 140).astype(float) * 0.08
        risk += (chol > 240).astype(float) * 0.07
        risk += fbs * 0.05
        risk += (restecg > 0).astype(float) * 0.05
        risk -= (thalach - 100) / 100 * 0.12
        risk += exang * 0.12
        risk += oldpeak / 6 * 0.10
        risk += (slope == 2).astype(float) * 0.05
        risk += ca / 3 * 0.15
        risk += (thal == 3).astype(float) * 0.10

        noise = np.random.normal(0, 0.08, n_samples)
        prob = 1 / (1 + np.exp(-(risk + noise - 0.35) * 5))
        target = (prob > np.random.uniform(0, 1, n_samples)).astype(int)

        df = pd.DataFrame({
            'age': ages, 'sex': sex, 'cp': cp, 'trestbps': trestbps,
            'chol': chol, 'fbs': fbs, 'restecg': restecg, 'thalach': thalach,
            'exang': exang, 'oldpeak': oldpeak, 'slope': slope, 'ca': ca,
            'thal': thal, 'target': target,
        })
        return df

    def engineer_gile_features(self, df: pd.DataFrame) -> pd.DataFrame:
        """Add GILE-dimension engineered features to the dataframe."""
        result = df.copy()

        age_norm = (result['age'] - 29) / (77 - 29)
        chol_norm = (result['chol'] - 126) / (564 - 126)
        fbs_val = result['fbs']
        g_score = (
            (1.0 - age_norm) * 0.40 +
            (1.0 - chol_norm) * 0.40 +
            (1.0 - fbs_val) * 0.20
        ).clip(0, 1)
        result['G_score'] = g_score.round(4)

        cp_risk = result['cp'].map({0: 0.9, 1: 0.6, 2: 0.4, 3: 0.1}).fillna(0.5)
        ca_risk = result['ca'] / 3.0
        thal_risk = result['thal'].map({1: 0.2, 2: 0.6, 3: 0.9}).fillna(0.5)
        slope_risk = result['slope'].map({0: 0.3, 1: 0.5, 2: 0.8}).fillna(0.5)
        i_score = (
            cp_risk * 0.30 +
            ca_risk * 0.30 +
            thal_risk * 0.25 +
            slope_risk * 0.15
        ).clip(0, 1)
        result['I_score'] = i_score.round(4)

        thalach_norm = (result['thalach'] - 71) / (202 - 71)
        exang_val = result['exang']
        oldpeak_norm = result['oldpeak'] / 6.2
        l_score = (
            thalach_norm * 0.45 +
            (1.0 - exang_val) * 0.30 +
            (1.0 - oldpeak_norm) * 0.25
        ).clip(0, 1)
        result['L_score'] = l_score.round(4)

        bp_norm = (result['trestbps'] - 94) / (200 - 94)
        ecg_risk = result['restecg'].map({0: 0.1, 1: 0.5, 2: 0.9}).fillna(0.3)
        sex_factor = result['sex'] * 0.15
        e_score = (
            (1.0 - bp_norm) * 0.45 +
            (1.0 - ecg_risk) * 0.35 +
            (1.0 - sex_factor) * 0.20
        ).clip(0, 1)
        result['E_score'] = e_score.round(4)

        result['GI_interaction'] = (g_score * i_score).round(4)
        result['GL_interaction'] = (g_score * l_score).round(4)
        result['GE_interaction'] = (g_score * e_score).round(4)
        result['IL_interaction'] = (i_score * l_score).round(4)
        result['IE_interaction'] = (i_score * e_score).round(4)
        result['LE_interaction'] = (l_score * e_score).round(4)

        result['GILE_composite'] = (
            g_score * GILE_FEATURE_MAP['G']['weight'] +
            i_score * GILE_FEATURE_MAP['I']['weight'] +
            l_score * GILE_FEATURE_MAP['L']['weight'] +
            e_score * GILE_FEATURE_MAP['E']['weight']
        ).round(4)

        result['tralse_risk_indicator'] = (
            1.0 - result['GILE_composite']
        ).round(4)

        self.gile_feature_names = [
            'G_score', 'I_score', 'L_score', 'E_score',
            'GI_interaction', 'GL_interaction', 'GE_interaction',
            'IL_interaction', 'IE_interaction', 'LE_interaction',
            'GILE_composite', 'tralse_risk_indicator',
        ]
        return result

    def preprocess(self, df: pd.DataFrame) -> tuple:
        """Feature engineering, scaling, and train/test split."""
        df_enhanced = self.engineer_gile_features(df)

        self.feature_columns = FEATURE_COLUMNS + self.gile_feature_names

        missing_cols = [c for c in self.feature_columns if c not in df_enhanced.columns]
        if missing_cols:
            raise ValueError(f"Missing columns after engineering: {missing_cols}")

        X = df_enhanced[self.feature_columns].values
        y = df_enhanced['target'].values

        X_train, X_test, y_train, y_test = train_test_split(
            X, y, test_size=0.2, random_state=42, stratify=y
        )

        self.scaler.fit(X_train)
        X_train_scaled = self.scaler.transform(X_train)
        X_test_scaled = self.scaler.transform(X_test)

        return X_train_scaled, X_test_scaled, y_train, y_test

    def train_ensemble(self, X_train: np.ndarray, y_train: np.ndarray) -> dict:
        """Train multiple models and build a voting ensemble."""
        lr = LogisticRegression(
            C=1.0, max_iter=1000, random_state=42, solver='lbfgs'
        )
        rf = RandomForestClassifier(
            n_estimators=200, max_depth=10, min_samples_split=5,
            min_samples_leaf=2, random_state=42, n_jobs=-1
        )
        gb = GradientBoostingClassifier(
            n_estimators=150, max_depth=4, learning_rate=0.1,
            subsample=0.8, random_state=42
        )
        svm_base = SVC(
            C=1.0, kernel='rbf', gamma='scale', random_state=42, probability=True
        )

        model_specs = {
            'logistic_regression': lr,
            'random_forest': rf,
            'gradient_boosting': gb,
            'svm': svm_base,
        }

        results = {}
        for name, model in model_specs.items():
            try:
                model.fit(X_train, y_train)
                self.models[name] = model

                train_pred = model.predict(X_train)
                train_proba = model.predict_proba(X_train)[:, 1]
                acc = accuracy_score(y_train, train_pred)
                auc = roc_auc_score(y_train, train_proba)

                results[name] = {
                    'train_accuracy': round(float(acc), 4),
                    'train_auc': round(float(auc), 4),
                    'status': 'trained',
                }
            except Exception as e:
                results[name] = {'status': 'failed', 'error': str(e)}

        try:
            self.ensemble = VotingClassifier(
                estimators=[
                    ('lr', self.models.get('logistic_regression', lr)),
                    ('rf', self.models.get('random_forest', rf)),
                    ('gb', self.models.get('gradient_boosting', gb)),
                    ('svm', self.models.get('svm', svm_base)),
                ],
                voting='soft',
                weights=[0.20, 0.30, 0.35, 0.15],
            )
            self.ensemble.fit(X_train, y_train)
            self.models['ensemble'] = self.ensemble

            ens_pred = self.ensemble.predict(X_train)
            ens_proba = self.ensemble.predict_proba(X_train)[:, 1]
            results['ensemble'] = {
                'train_accuracy': round(float(accuracy_score(y_train, ens_pred)), 4),
                'train_auc': round(float(roc_auc_score(y_train, ens_proba)), 4),
                'status': 'trained',
                'weights': [0.20, 0.30, 0.35, 0.15],
            }
        except Exception as e:
            results['ensemble'] = {'status': 'failed', 'error': str(e)}

        best_name = max(
            [k for k, v in results.items() if v.get('status') == 'trained'],
            key=lambda k: results[k].get('train_auc', 0),
            default='ensemble'
        )
        self.best_model_name = best_name
        self.model_comparison = results
        self.is_trained = True
        self.training_metrics = results

        return results

    def predict_with_tralse(self, X: np.ndarray) -> List[Dict]:
        """
        Predict with Tralse confidence scoring.
        Returns per-patient predictions with True/Tralse/False classification.
        """
        if not self.is_trained:
            raise RuntimeError("Models not trained. Call train_ensemble first.")

        model = self.models.get(self.best_model_name, self.ensemble)
        if model is None:
            raise RuntimeError("No trained model available.")

        probas = model.predict_proba(X)[:, 1]
        predictions = []

        true_thresh = TRALSE_THRESHOLDS['true_threshold']
        false_thresh = TRALSE_THRESHOLDS['false_threshold']

        for i, prob in enumerate(probas):
            if prob >= true_thresh:
                zone = 'True'
                confidence = 'high'
                action = 'Positive prediction — high confidence heart disease risk'
                specialist_review = False
            elif prob <= false_thresh:
                zone = 'False'
                confidence = 'high'
                action = 'Negative prediction — low heart disease risk'
                specialist_review = False
            else:
                zone = 'Tralse'
                confidence = 'uncertain'
                action = 'Uncertain — recommend specialist review and additional testing'
                specialist_review = True

            uncertainty = self._decompose_uncertainty(X[i:i+1])

            predictions.append({
                'patient_index': i,
                'probability': round(float(prob), 4),
                'prediction': int(prob >= 0.5),
                'tralse_zone': zone,
                'confidence_level': confidence,
                'recommended_action': action,
                'specialist_review_needed': specialist_review,
                'uncertainty_decomposition': uncertainty,
                'distance_to_threshold': round(float(min(abs(prob - true_thresh), abs(prob - false_thresh))), 4),
            })

        return predictions

    def _decompose_uncertainty(self, x_single: np.ndarray) -> Dict:
        """Calculate per-patient uncertainty decomposition across models."""
        if len(self.models) < 2:
            return {'aleatoric': 0.5, 'epistemic': 0.5, 'total': 1.0}

        model_probs = []
        for name, model in self.models.items():
            if name == 'ensemble':
                continue
            try:
                p = model.predict_proba(x_single)[:, 1][0]
                model_probs.append(float(p))
            except Exception:
                continue

        if not model_probs:
            return {'aleatoric': 0.5, 'epistemic': 0.5, 'total': 1.0}

        mean_prob = np.mean(model_probs)
        aleatoric = float(mean_prob * (1.0 - mean_prob))
        epistemic = float(np.var(model_probs))
        total = aleatoric + epistemic

        return {
            'aleatoric': round(aleatoric, 4),
            'epistemic': round(epistemic, 4),
            'total': round(total, 4),
            'model_agreement': round(1.0 - epistemic * 4, 4),
            'individual_probs': {
                name: round(p, 4)
                for name, p in zip(
                    [n for n in self.models if n != 'ensemble'],
                    model_probs
                )
            },
        }

    def evaluate(self, X_test: np.ndarray, y_test: np.ndarray) -> Dict:
        """Comprehensive evaluation metrics."""
        if not self.is_trained:
            raise RuntimeError("Models not trained.")

        results = {}
        for name, model in self.models.items():
            try:
                y_pred = model.predict(X_test)
                y_proba = model.predict_proba(X_test)[:, 1]

                cm = confusion_matrix(y_test, y_pred)
                tn, fp, fn, tp = cm.ravel()

                results[name] = {
                    'accuracy': round(float(accuracy_score(y_test, y_pred)), 4),
                    'precision': round(float(precision_score(y_test, y_pred, zero_division=0)), 4),
                    'recall': round(float(recall_score(y_test, y_pred, zero_division=0)), 4),
                    'f1': round(float(f1_score(y_test, y_pred, zero_division=0)), 4),
                    'auc_roc': round(float(roc_auc_score(y_test, y_proba)), 4),
                    'confusion_matrix': {
                        'true_negative': int(tn),
                        'false_positive': int(fp),
                        'false_negative': int(fn),
                        'true_positive': int(tp),
                    },
                    'specificity': round(float(tn / (tn + fp)) if (tn + fp) > 0 else 0, 4),
                    'sensitivity': round(float(tp / (tp + fn)) if (tp + fn) > 0 else 0, 4),
                    'npv': round(float(tn / (tn + fn)) if (tn + fn) > 0 else 0, 4),
                    'ppv': round(float(tp / (tp + fp)) if (tp + fp) > 0 else 0, 4),
                }
            except Exception as e:
                results[name] = {'error': str(e)}

        tralse_predictions = self.predict_with_tralse(X_test)
        tralse_summary = self._tralse_summary(tralse_predictions, y_test)
        results['tralse_analysis'] = tralse_summary

        self.model_comparison.update(results)
        return results

    def _tralse_summary(self, predictions: List[Dict], y_true: np.ndarray) -> Dict:
        """Summarize Tralse zone distribution and accuracy by zone."""
        zones = {'True': [], 'Tralse': [], 'False': []}
        for pred in predictions:
            zones[pred['tralse_zone']].append(pred['patient_index'])

        zone_stats = {}
        for zone, indices in zones.items():
            if not indices:
                zone_stats[zone] = {
                    'count': 0, 'percentage': 0, 'accuracy': None,
                }
                continue

            zone_preds = [predictions[i]['prediction'] for i in indices]
            zone_true = y_true[indices]
            acc = accuracy_score(zone_true, zone_preds) if len(indices) > 0 else 0

            zone_stats[zone] = {
                'count': len(indices),
                'percentage': round(len(indices) / len(predictions) * 100, 1),
                'accuracy': round(float(acc), 4),
            }

        return {
            'zone_distribution': zone_stats,
            'total_predictions': len(predictions),
            'specialist_review_count': sum(1 for p in predictions if p['specialist_review_needed']),
            'specialist_review_pct': round(
                sum(1 for p in predictions if p['specialist_review_needed']) / len(predictions) * 100, 1
            ) if predictions else 0,
            'mean_uncertainty': round(
                float(np.mean([p['uncertainty_decomposition']['total'] for p in predictions])), 4
            ),
        }

    def feature_importance_gile(self, model=None) -> Dict:
        """Map feature importances to GILE dimensions."""
        if model is None:
            model = self.models.get('random_forest') or self.models.get('gradient_boosting')
        if model is None:
            raise RuntimeError("No tree-based model available for feature importance.")

        if not hasattr(model, 'feature_importances_'):
            if hasattr(model, 'coef_'):
                importances = np.abs(model.coef_[0])
            else:
                return {'error': 'Model does not expose feature importances'}
        else:
            importances = model.feature_importances_

        if len(importances) != len(self.feature_columns):
            return {'error': f'Importance length {len(importances)} != feature count {len(self.feature_columns)}'}

        feature_imp = dict(zip(self.feature_columns, [round(float(v), 4) for v in importances]))

        gile_importance = {'G': 0.0, 'I': 0.0, 'L': 0.0, 'E': 0.0}
        gile_features_detail = {'G': {}, 'I': {}, 'L': {}, 'E': {}}

        for dim, info in GILE_FEATURE_MAP.items():
            for feat in info['primary']:
                if feat in feature_imp:
                    gile_importance[dim] += feature_imp[feat]
                    gile_features_detail[dim][feat] = feature_imp[feat]

        gile_scores = ['G_score', 'I_score', 'L_score', 'E_score']
        for score_name in gile_scores:
            if score_name in feature_imp:
                dim = score_name[0]
                gile_importance[dim] += feature_imp[score_name]
                gile_features_detail[dim][score_name] = feature_imp[score_name]

        total = sum(gile_importance.values())
        if total > 0:
            gile_normalized = {k: round(v / total, 4) for k, v in gile_importance.items()}
        else:
            gile_normalized = {k: 0.25 for k in 'GILE'}

        tralse_weighted = {}
        for dim, norm_imp in gile_normalized.items():
            if norm_imp > 0.35:
                tralse_weighted[dim] = {'importance': norm_imp, 'confidence': 'True', 'zone': 'dominant'}
            elif norm_imp > 0.15:
                tralse_weighted[dim] = {'importance': norm_imp, 'confidence': 'Tralse', 'zone': 'moderate'}
            else:
                tralse_weighted[dim] = {'importance': norm_imp, 'confidence': 'False', 'zone': 'minor'}

        return {
            'individual_features': feature_imp,
            'gile_aggregated': {k: round(v, 4) for k, v in gile_importance.items()},
            'gile_normalized': gile_normalized,
            'gile_detail': gile_features_detail,
            'tralse_weighted_importance': tralse_weighted,
            'top_features': sorted(feature_imp.items(), key=lambda x: x[1], reverse=True)[:10],
        }

    def generate_kaggle_submission(self, test_df: pd.DataFrame, output_path: str = 'kaggle/submissions/heart_disease_submission.csv') -> str:
        """Generate Kaggle-format submission CSV."""
        if not self.is_trained:
            raise RuntimeError("Models not trained.")

        test_enhanced = self.engineer_gile_features(test_df)

        missing = [c for c in self.feature_columns if c not in test_enhanced.columns]
        if missing:
            raise ValueError(f"Test data missing columns: {missing}")

        X_test = test_enhanced[self.feature_columns].values
        X_test_scaled = self.scaler.transform(X_test)

        model = self.models.get(self.best_model_name, self.ensemble)
        probas = model.predict_proba(X_test_scaled)[:, 1]
        preds = (probas >= 0.5).astype(int)

        submission = pd.DataFrame({
            'Id': range(1, len(preds) + 1),
            'target': preds,
            'probability': probas.round(4),
        })

        import os
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        submission.to_csv(output_path, index=False)

        return output_path

    def cross_validate(self, X: np.ndarray, y: np.ndarray, cv: int = 5) -> Dict:
        """K-fold cross-validation for all models."""
        if not self.is_trained:
            raise RuntimeError("Models not trained.")

        skf = StratifiedKFold(n_splits=cv, shuffle=True, random_state=42)
        cv_results = {}

        for name, model in self.models.items():
            try:
                scores_acc = cross_val_score(model, X, y, cv=skf, scoring='accuracy')
                scores_auc = cross_val_score(model, X, y, cv=skf, scoring='roc_auc')
                scores_f1 = cross_val_score(model, X, y, cv=skf, scoring='f1')

                cv_results[name] = {
                    'accuracy_mean': round(float(scores_acc.mean()), 4),
                    'accuracy_std': round(float(scores_acc.std()), 4),
                    'auc_mean': round(float(scores_auc.mean()), 4),
                    'auc_std': round(float(scores_auc.std()), 4),
                    'f1_mean': round(float(scores_f1.mean()), 4),
                    'f1_std': round(float(scores_f1.std()), 4),
                    'fold_accuracies': [round(float(s), 4) for s in scores_acc],
                    'fold_aucs': [round(float(s), 4) for s in scores_auc],
                }
            except Exception as e:
                cv_results[name] = {'error': str(e)}

        return cv_results

    def generate_eda_report(self, df: pd.DataFrame) -> Dict:
        """Generate exploratory data analysis report."""
        report = {
            'shape': {'rows': df.shape[0], 'columns': df.shape[1]},
            'columns': list(df.columns),
            'missing_values': df.isnull().sum().to_dict(),
            'dtypes': {k: str(v) for k, v in df.dtypes.to_dict().items()},
            'feature_stats': {},
        }

        for col in df.columns:
            stats = {}
            if df[col].dtype in ['int64', 'float64']:
                desc = df[col].describe()
                stats = {
                    'mean': round(float(desc['mean']), 4),
                    'std': round(float(desc['std']), 4),
                    'min': round(float(desc['min']), 4),
                    'q25': round(float(desc['25%']), 4),
                    'median': round(float(desc['50%']), 4),
                    'q75': round(float(desc['75%']), 4),
                    'max': round(float(desc['max']), 4),
                    'skew': round(float(df[col].skew()), 4),
                    'kurtosis': round(float(df[col].kurtosis()), 4),
                }

                if col in FEATURE_DESCRIPTIONS:
                    stats['description'] = FEATURE_DESCRIPTIONS[col]

                n_unique = df[col].nunique()
                if n_unique <= 10:
                    stats['value_counts'] = df[col].value_counts().to_dict()
                    stats['type'] = 'categorical'
                else:
                    stats['type'] = 'continuous'

            report['feature_stats'][col] = stats

        if 'target' in df.columns:
            target_counts = df['target'].value_counts().to_dict()
            report['target_distribution'] = {
                'counts': target_counts,
                'percentages': {
                    k: round(v / df.shape[0] * 100, 1)
                    for k, v in target_counts.items()
                },
                'balance_ratio': round(
                    min(target_counts.values()) / max(target_counts.values()), 3
                ) if len(target_counts) == 2 else None,
            }

        if 'target' in df.columns:
            correlations = {}
            for col in FEATURE_COLUMNS:
                if col in df.columns:
                    corr = df[col].corr(df['target'])
                    correlations[col] = round(float(corr), 4) if not np.isnan(corr) else 0.0
            report['target_correlations'] = dict(
                sorted(correlations.items(), key=lambda x: abs(x[1]), reverse=True)
            )

        return report

    def plot_roc_data(self, y_true: np.ndarray, y_pred_proba: np.ndarray) -> Dict:
        """Return ROC curve data points for Streamlit visualization."""
        fpr, tpr, thresholds = roc_curve(y_true, y_pred_proba)
        auc = roc_auc_score(y_true, y_pred_proba)

        optimal_idx = np.argmax(tpr - fpr)
        optimal_threshold = float(thresholds[optimal_idx])

        return {
            'fpr': [round(float(x), 4) for x in fpr],
            'tpr': [round(float(x), 4) for x in tpr],
            'thresholds': [round(float(x), 4) for x in thresholds],
            'auc': round(float(auc), 4),
            'optimal_threshold': round(optimal_threshold, 4),
            'optimal_point': {
                'fpr': round(float(fpr[optimal_idx]), 4),
                'tpr': round(float(tpr[optimal_idx]), 4),
            },
            'diagonal': {'x': [0, 1], 'y': [0, 1]},
        }

    def get_model_comparison(self) -> Dict:
        """Compare all trained models with their metrics."""
        if not self.is_trained:
            return {'error': 'No models trained yet'}

        comparison = {
            'models': {},
            'best_model': self.best_model_name,
            'training_summary': self.training_metrics,
        }

        for name, metrics in self.model_comparison.items():
            if isinstance(metrics, dict) and 'accuracy' in metrics:
                comparison['models'][name] = {
                    'accuracy': metrics.get('accuracy', 0),
                    'precision': metrics.get('precision', 0),
                    'recall': metrics.get('recall', 0),
                    'f1': metrics.get('f1', 0),
                    'auc_roc': metrics.get('auc_roc', 0),
                }

        return comparison

    def get_gile_analysis(self, df: pd.DataFrame) -> Dict:
        """Comprehensive GILE dimension analysis of the dataset."""
        enhanced = self.engineer_gile_features(df)
        gile_cols = ['G_score', 'I_score', 'L_score', 'E_score']

        analysis = {}
        for col in gile_cols:
            dim = col[0]
            analysis[dim] = {
                'mean': round(float(enhanced[col].mean()), 4),
                'std': round(float(enhanced[col].std()), 4),
                'min': round(float(enhanced[col].min()), 4),
                'max': round(float(enhanced[col].max()), 4),
                'description': GILE_FEATURE_MAP[dim]['description'],
                'primary_features': GILE_FEATURE_MAP[dim]['primary'],
                'weight': GILE_FEATURE_MAP[dim]['weight'],
            }

        if 'target' in enhanced.columns:
            for col in gile_cols:
                dim = col[0]
                pos = enhanced[enhanced['target'] == 1][col]
                neg = enhanced[enhanced['target'] == 0][col]
                analysis[dim]['positive_mean'] = round(float(pos.mean()), 4) if len(pos) > 0 else None
                analysis[dim]['negative_mean'] = round(float(neg.mean()), 4) if len(neg) > 0 else None
                analysis[dim]['discriminative_power'] = round(
                    abs(float(pos.mean()) - float(neg.mean())), 4
                ) if len(pos) > 0 and len(neg) > 0 else None

        analysis['composite'] = {
            'mean': round(float(enhanced['GILE_composite'].mean()), 4),
            'std': round(float(enhanced['GILE_composite'].std()), 4),
        }

        if 'target' in enhanced.columns:
            analysis['composite']['correlation_with_target'] = round(
                float(enhanced['GILE_composite'].corr(enhanced['target'])), 4
            )

        return analysis

    def run_full_pipeline(self, filepath: str = None) -> Dict:
        """Run the complete prediction pipeline end-to-end."""
        df = self.load_data(filepath)
        eda = self.generate_eda_report(df)
        gile_analysis = self.get_gile_analysis(df)

        X_train, X_test, y_train, y_test = self.preprocess(df)
        training_results = self.train_ensemble(X_train, y_train)
        eval_results = self.evaluate(X_test, y_test)
        cv_results = self.cross_validate(X_train, y_train, cv=5)

        best_model = self.models.get(self.best_model_name, self.ensemble)
        best_proba = best_model.predict_proba(X_test)[:, 1]
        roc_data = self.plot_roc_data(y_test, best_proba)

        importance = self.feature_importance_gile()
        tralse_predictions = self.predict_with_tralse(X_test)

        return {
            'dataset_info': {
                'rows': df.shape[0],
                'features': len(FEATURE_COLUMNS),
                'gile_features': len(self.gile_feature_names),
                'total_features': len(self.feature_columns),
            },
            'eda_report': eda,
            'gile_analysis': gile_analysis,
            'training_results': training_results,
            'evaluation': eval_results,
            'cross_validation': cv_results,
            'roc_data': roc_data,
            'feature_importance': importance,
            'tralse_summary': self._tralse_summary(tralse_predictions, y_test),
            'model_comparison': self.get_model_comparison(),
            'best_model': self.best_model_name,
            'sample_predictions': tralse_predictions[:10],
        }

    def get_patient_report(self, patient_data: Dict) -> Dict:
        """Generate a single-patient risk report with Tralse scoring."""
        if not self.is_trained:
            raise RuntimeError("Models not trained.")

        row = pd.DataFrame([patient_data])
        enhanced = self.engineer_gile_features(row)

        X = enhanced[self.feature_columns].values
        X_scaled = self.scaler.transform(X)

        prediction = self.predict_with_tralse(X_scaled)[0]

        gile_profile = {
            'G_score': round(float(enhanced['G_score'].iloc[0]), 4),
            'I_score': round(float(enhanced['I_score'].iloc[0]), 4),
            'L_score': round(float(enhanced['L_score'].iloc[0]), 4),
            'E_score': round(float(enhanced['E_score'].iloc[0]), 4),
            'composite': round(float(enhanced['GILE_composite'].iloc[0]), 4),
        }

        risk_factors = []
        if patient_data.get('age', 0) > 55:
            risk_factors.append('Age > 55')
        if patient_data.get('chol', 0) > 240:
            risk_factors.append('High cholesterol (>240 mg/dl)')
        if patient_data.get('trestbps', 0) > 140:
            risk_factors.append('Hypertension (>140 mm Hg)')
        if patient_data.get('cp', -1) == 0:
            risk_factors.append('Asymptomatic chest pain (highest risk type)')
        if patient_data.get('exang', 0) == 1:
            risk_factors.append('Exercise-induced angina')
        if patient_data.get('oldpeak', 0) > 2.0:
            risk_factors.append('Significant ST depression')
        if patient_data.get('ca', 0) > 0:
            risk_factors.append(f'{patient_data["ca"]} major vessel(s) affected')
        if patient_data.get('thal', 0) == 3:
            risk_factors.append('Reversible thalassemia defect')
        if patient_data.get('fbs', 0) == 1:
            risk_factors.append('High fasting blood sugar')

        protective = []
        if patient_data.get('thalach', 0) > 150:
            protective.append('Good maximum heart rate')
        if patient_data.get('age', 100) < 45:
            protective.append('Younger age')
        if patient_data.get('chol', 300) < 200:
            protective.append('Healthy cholesterol')
        if patient_data.get('trestbps', 200) < 120:
            protective.append('Normal blood pressure')

        return {
            'prediction': prediction,
            'gile_profile': gile_profile,
            'risk_factors': risk_factors,
            'protective_factors': protective,
            'clinical_summary': self._generate_clinical_summary(prediction, gile_profile, risk_factors),
        }

    def _generate_clinical_summary(self, prediction: Dict, gile: Dict, risk_factors: List) -> str:
        """Generate human-readable clinical summary."""
        prob = prediction['probability']
        zone = prediction['tralse_zone']

        if zone == 'True':
            severity = "HIGH RISK"
            recommendation = "Immediate cardiology referral recommended."
        elif zone == 'Tralse':
            severity = "UNCERTAIN RISK"
            recommendation = "Additional diagnostic testing recommended. Consider stress test, echocardiogram."
        else:
            severity = "LOW RISK"
            recommendation = "Continue preventive care. Annual cardiovascular screening advised."

        summary = (
            f"Heart Disease Risk Assessment: {severity}\n"
            f"Predicted probability: {prob:.1%}\n"
            f"Confidence zone: {zone}\n"
            f"GILE composite score: {gile['composite']:.3f}\n"
            f"Number of risk factors identified: {len(risk_factors)}\n"
            f"Recommendation: {recommendation}"
        )
        return summary

    def get_tralse_thresholds(self) -> Dict:
        """Return the current Tralse threshold configuration."""
        return {
            **TRALSE_THRESHOLDS,
            'description': {
                'true_zone': 'Probability >= 0.75: High confidence positive prediction',
                'tralse_zone': 'Probability 0.35-0.75: Uncertain, flag for specialist review',
                'false_zone': 'Probability < 0.35: High confidence negative prediction',
            },
            'medical_rationale': (
                'In medical prediction, the cost of false negatives (missed disease) '
                'is much higher than false positives. The Tralse zone ensures uncertain '
                'cases receive additional clinical attention rather than algorithmic decisions.'
            ),
        }


def demo():
    """Run a standalone demo of the heart disease predictor."""
    predictor = HeartDiseasePredictor()

    print("=" * 70)
    print("TI-FRAMEWORK HEART DISEASE PREDICTOR — DEMO")
    print("=" * 70)

    df = predictor.generate_sample_data(500)
    print(f"\nGenerated {len(df)} samples")
    print(f"Target distribution: {df['target'].value_counts().to_dict()}")

    eda = predictor.generate_eda_report(df)
    print(f"\nEDA: {eda['shape']['rows']} rows, {eda['shape']['columns']} columns")
    if 'target_correlations' in eda:
        print("Top correlated features with target:")
        for feat, corr in list(eda['target_correlations'].items())[:5]:
            print(f"  {feat}: {corr:.4f}")

    gile = predictor.get_gile_analysis(df)
    print("\nGILE Dimension Analysis:")
    for dim in 'GILE':
        info = gile[dim]
        print(f"  {dim}: mean={info['mean']:.3f}, discriminative_power={info.get('discriminative_power', 'N/A')}")

    X_train, X_test, y_train, y_test = predictor.preprocess(df)
    print(f"\nTrain: {X_train.shape}, Test: {X_test.shape}")
    print(f"Features: {len(predictor.feature_columns)} (13 original + {len(predictor.gile_feature_names)} GILE)")

    training = predictor.train_ensemble(X_train, y_train)
    print("\nTraining Results:")
    for name, metrics in training.items():
        if metrics.get('status') == 'trained':
            print(f"  {name}: acc={metrics['train_accuracy']:.4f}, auc={metrics['train_auc']:.4f}")

    eval_results = predictor.evaluate(X_test, y_test)
    print("\nTest Evaluation:")
    for name, metrics in eval_results.items():
        if isinstance(metrics, dict) and 'accuracy' in metrics:
            print(f"  {name}: acc={metrics['accuracy']:.4f}, auc={metrics['auc_roc']:.4f}, f1={metrics['f1']:.4f}")

    tralse_preds = predictor.predict_with_tralse(X_test)
    tralse_dist = {}
    for p in tralse_preds:
        zone = p['tralse_zone']
        tralse_dist[zone] = tralse_dist.get(zone, 0) + 1
    print(f"\nTralse Zone Distribution: {tralse_dist}")
    print(f"Specialist reviews needed: {sum(1 for p in tralse_preds if p['specialist_review_needed'])}/{len(tralse_preds)}")

    importance = predictor.feature_importance_gile()
    print("\nGILE Feature Importance (normalized):")
    for dim, val in importance['gile_normalized'].items():
        tw = importance['tralse_weighted_importance'][dim]
        print(f"  {dim}: {val:.4f} [{tw['confidence']} confidence, {tw['zone']}]")

    cv = predictor.cross_validate(X_train, y_train, cv=5)
    print("\n5-Fold Cross-Validation:")
    for name, res in cv.items():
        if 'accuracy_mean' in res:
            print(f"  {name}: acc={res['accuracy_mean']:.4f}±{res['accuracy_std']:.4f}, "
                  f"auc={res['auc_mean']:.4f}±{res['auc_std']:.4f}")

    sample_patient = {
        'age': 63, 'sex': 1, 'cp': 0, 'trestbps': 145, 'chol': 233,
        'fbs': 1, 'restecg': 0, 'thalach': 150, 'exang': 0,
        'oldpeak': 2.3, 'slope': 0, 'ca': 0, 'thal': 1,
    }
    report = predictor.get_patient_report(sample_patient)
    print(f"\nSample Patient Report:")
    print(report['clinical_summary'])

    print("\n" + "=" * 70)
    print("DEMO COMPLETE")
    print("=" * 70)

    return predictor


if __name__ == '__main__':
    demo()
