"""
Kaggle Playground Series S6E2 - Heart Disease Submission Generator
===================================================================
Advanced ensemble pipeline targeting 96% accuracy for binary heart disease prediction.

Models: XGBoost, LightGBM, GradientBoosting, ExtraTrees, LogisticRegression
Pipeline: Feature engineering → SMOTE (inside CV) → Stacking + Voting ensemble

TI EXACT THRESHOLDS (Paper #322):
  TAU     = cos(π/8)       ≈ 0.9239
  EPSILON = cos²(π/8)      ≈ 0.8536
  GAMMA   = cos²(π/5)      ≈ 0.6545
  LAMBDA  = (√2+1)/4       ≈ 0.6036
  ETA     = √2−1           ≈ 0.4142
"""

import math
import os
import warnings
from typing import Optional, Tuple, Dict, Any

import numpy as np
import pandas as pd
from sklearn.datasets import load_wine
from sklearn.ensemble import (
    GradientBoostingClassifier,
    ExtraTreesClassifier,
    VotingClassifier,
    StackingClassifier,
)
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import (
    accuracy_score,
    precision_score,
    recall_score,
    f1_score,
    roc_auc_score,
    classification_report,
    confusion_matrix,
)
from sklearn.model_selection import (
    StratifiedKFold,
    cross_val_score,
    train_test_split,
)
from sklearn.preprocessing import StandardScaler, PolynomialFeatures
import xgboost as xgb
import lightgbm as lgb
from imblearn.over_sampling import SMOTE
from imblearn.pipeline import Pipeline as ImbPipeline

warnings.filterwarnings("ignore")

TAU = math.cos(math.pi / 8)
EPSILON = math.cos(math.pi / 8) ** 2
GAMMA = math.cos(math.pi / 5) ** 2
LAMBDA = (math.sqrt(2) + 1) / 4
ETA = math.sqrt(2) - 1

FEATURE_COLUMNS = [
    "age", "sex", "cp", "trestbps", "chol", "fbs",
    "restecg", "thalach", "exang", "oldpeak", "slope", "ca", "thal",
]


class KaggleHeartDiseaseSubmission:
    """Kaggle Playground Series S6E2 heart disease submission generator.

    Builds an advanced stacking + voting ensemble with SMOTE applied
    inside cross-validation folds via imblearn Pipeline.
    """

    def __init__(self):
        self.train_df: Optional[pd.DataFrame] = None
        self.test_df: Optional[pd.DataFrame] = None
        self.X_train: Optional[np.ndarray] = None
        self.y_train: Optional[np.ndarray] = None
        self.X_test: Optional[np.ndarray] = None
        self.scaler = StandardScaler()
        self.ensemble = None
        self.voting_ensemble = None
        self.feature_names: list = []
        self.is_trained = False
        self.cv_results: Dict[str, Any] = {}
        self.test_ids: Optional[pd.Series] = None

    def load_data(
        self,
        train_path: Optional[str] = None,
        test_path: Optional[str] = None,
    ) -> Tuple[pd.DataFrame, Optional[pd.DataFrame]]:
        """Load training and optional test CSV files, or fall back to the built-in UCI dataset."""
        try:
            if train_path and os.path.exists(train_path):
                self.train_df = pd.read_csv(train_path)
                self._clean_dataframe(self.train_df)
                print(f"Loaded training data: {self.train_df.shape}")
            else:
                self.train_df = self._load_builtin_uci()
                print(f"Using built-in UCI dataset: {self.train_df.shape}")

            if test_path and os.path.exists(test_path):
                self.test_df = pd.read_csv(test_path)
                if "id" in self.test_df.columns:
                    self.test_ids = self.test_df["id"]
                elif "Id" in self.test_df.columns:
                    self.test_ids = self.test_df["Id"]
                self._clean_dataframe(self.test_df)
                print(f"Loaded test data: {self.test_df.shape}")

            return self.train_df, self.test_df

        except Exception as e:
            raise RuntimeError(f"Error loading data: {e}")

    def _clean_dataframe(self, df: pd.DataFrame) -> None:
        """Normalise column names and handle missing values in-place."""
        rename_map = {"num": "target", "goal": "target", "condition": "target", "disease": "target"}
        for old, new in rename_map.items():
            if old in df.columns:
                df.rename(columns={old: new}, inplace=True)

        if "target" in df.columns:
            df["target"] = (df["target"] > 0).astype(int)

        for col in ["ca", "thal"]:
            if col in df.columns:
                df[col] = pd.to_numeric(df[col], errors="coerce")
                df[col].fillna(df[col].median(), inplace=True)

        for col in FEATURE_COLUMNS:
            if col in df.columns:
                df[col] = pd.to_numeric(df[col], errors="coerce")
                df[col].fillna(df[col].median(), inplace=True)

    def _load_builtin_uci(self) -> pd.DataFrame:
        """Load UCI heart-disease data from a local CSV or generate synthetic data."""
        base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        csv_path = os.path.join(base, "data", "heart_cleveland.csv")
        if os.path.exists(csv_path):
            df = pd.read_csv(csv_path)
            self._clean_dataframe(df)
            return df

        print("UCI CSV not found — generating synthetic heart-disease data for demo.")
        return self._generate_synthetic_data()

    def _generate_synthetic_data(self, n: int = 800) -> pd.DataFrame:
        """Generate realistic synthetic heart-disease data."""
        rng = np.random.RandomState(42)
        ages = rng.normal(54, 9, n).clip(29, 77).astype(int)
        sex = rng.binomial(1, 0.68, n)
        cp = rng.choice([0, 1, 2, 3], n, p=[0.47, 0.17, 0.28, 0.08])
        trestbps = rng.normal(131, 17, n).clip(94, 200).astype(int)
        chol = rng.normal(246, 52, n).clip(126, 564).astype(int)
        fbs = rng.binomial(1, 0.15, n)
        restecg = rng.choice([0, 1, 2], n, p=[0.48, 0.48, 0.04])
        thalach = rng.normal(149, 23, n).clip(71, 202).astype(int)
        exang = rng.binomial(1, 0.33, n)
        oldpeak = np.abs(rng.normal(1.04, 1.16, n)).clip(0, 6.2).round(1)
        slope = rng.choice([0, 1, 2], n, p=[0.07, 0.46, 0.47])
        ca = rng.choice([0, 1, 2, 3], n, p=[0.58, 0.22, 0.13, 0.07])
        thal = rng.choice([1, 2, 3], n, p=[0.55, 0.13, 0.32])

        risk = np.zeros(n)
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

        prob = 1 / (1 + np.exp(-(risk + rng.normal(0, 0.08, n) - 0.35) * 5))
        target = (prob > rng.uniform(0, 1, n)).astype(int)

        return pd.DataFrame({
            "age": ages, "sex": sex, "cp": cp, "trestbps": trestbps,
            "chol": chol, "fbs": fbs, "restecg": restecg, "thalach": thalach,
            "exang": exang, "oldpeak": oldpeak, "slope": slope, "ca": ca,
            "thal": thal, "target": target,
        })

    def engineer_features(self, df: pd.DataFrame) -> pd.DataFrame:
        """Create engineered features: interactions, ratios, polynomials, TI thresholds."""
        result = df.copy()

        result["age_thalach"] = result["age"] * result["thalach"]
        result["chol_age_ratio"] = result["chol"] / (result["age"] + 1)
        result["trestbps_oldpeak"] = result["trestbps"] * result["oldpeak"]

        result["age_thalach_ratio"] = result["age"] / (result["thalach"] + 1)
        result["chol_bp_product"] = result["chol"] * result["trestbps"] / 10000
        result["oldpeak_slope"] = result["oldpeak"] * (result["slope"] + 1)
        result["exercise_risk"] = result["exang"] * result["oldpeak"]
        result["heart_reserve"] = (220 - result["age"] - result["thalach"]) / 220

        thalach_norm = (result["thalach"] - result["thalach"].min()) / (
            result["thalach"].max() - result["thalach"].min() + 1e-8
        )
        oldpeak_norm = result["oldpeak"] / (result["oldpeak"].max() + 1e-8)
        chol_norm = (result["chol"] - result["chol"].min()) / (
            result["chol"].max() - result["chol"].min() + 1e-8
        )

        composite = (thalach_norm + (1 - oldpeak_norm) + (1 - chol_norm)) / 3.0
        result["above_eta"] = (composite > ETA).astype(int)
        result["above_lambda"] = (composite > LAMBDA).astype(int)
        result["above_epsilon"] = (composite > EPSILON).astype(int)

        top_predictors = ["age", "thalach", "oldpeak", "chol", "trestbps"]
        available = [c for c in top_predictors if c in result.columns]
        if len(available) >= 2:
            poly = PolynomialFeatures(degree=2, interaction_only=False, include_bias=False)
            poly_data = poly.fit_transform(result[available])
            poly_names = poly.get_feature_names_out(available)
            new_cols = [n for n in poly_names if n not in available]
            for i, name in enumerate(poly_names):
                if name in new_cols:
                    col_idx = list(poly_names).index(name)
                    result[f"poly_{name}"] = poly_data[:, col_idx]

        self.feature_names = [
            c for c in result.columns if c not in ("target", "id", "Id")
        ]
        return result

    def build_ensemble(self) -> StackingClassifier:
        """Create the stacking ensemble with SMOTE-compatible base estimators."""
        xgb_model = xgb.XGBClassifier(
            n_estimators=300,
            max_depth=5,
            learning_rate=0.05,
            subsample=0.8,
            colsample_bytree=0.8,
            min_child_weight=3,
            gamma=0.1,
            reg_alpha=0.1,
            reg_lambda=1.0,
            random_state=42,
            eval_metric="logloss",
            n_jobs=-1,
        )

        lgb_model = lgb.LGBMClassifier(
            n_estimators=300,
            max_depth=5,
            learning_rate=0.05,
            subsample=0.8,
            colsample_bytree=0.8,
            min_child_samples=10,
            reg_alpha=0.1,
            reg_lambda=1.0,
            random_state=42,
            verbose=-1,
            n_jobs=-1,
        )

        gb_model = GradientBoostingClassifier(
            n_estimators=200,
            max_depth=4,
            learning_rate=0.05,
            subsample=0.8,
            min_samples_split=5,
            min_samples_leaf=3,
            random_state=42,
        )

        et_model = ExtraTreesClassifier(
            n_estimators=300,
            max_depth=12,
            min_samples_split=3,
            min_samples_leaf=2,
            random_state=42,
            n_jobs=-1,
        )

        lr_model = LogisticRegression(
            C=1.0, max_iter=2000, random_state=42, solver="lbfgs",
        )

        base_estimators = [
            ("xgb", xgb_model),
            ("lgb", lgb_model),
            ("gb", gb_model),
            ("et", et_model),
            ("lr", lr_model),
        ]

        meta_learner = LogisticRegression(C=1.0, max_iter=2000, random_state=42)

        self.ensemble = StackingClassifier(
            estimators=base_estimators,
            final_estimator=meta_learner,
            cv=StratifiedKFold(n_splits=5, shuffle=True, random_state=42),
            stack_method="predict_proba",
            n_jobs=-1,
        )

        self.voting_ensemble = VotingClassifier(
            estimators=base_estimators,
            voting="soft",
            weights=[0.25, 0.25, 0.20, 0.15, 0.15],
            n_jobs=-1,
        )

        return self.ensemble

    def _build_smote_pipeline(self, estimator) -> ImbPipeline:
        """Wrap an estimator in an imblearn Pipeline with SMOTE + scaling."""
        return ImbPipeline([
            ("scaler", StandardScaler()),
            ("smote", SMOTE(random_state=42, k_neighbors=3)),
            ("model", estimator),
        ])

    def train_and_evaluate(self) -> Dict[str, Any]:
        """Train the ensemble with proper CV and report metrics."""
        if self.train_df is None:
            raise RuntimeError("No training data loaded. Call load_data() first.")

        try:
            train_eng = self.engineer_features(self.train_df)
            feature_cols = self.feature_names

            X = train_eng[feature_cols].values
            y = train_eng["target"].values

            self.scaler.fit(X)
            X_scaled = self.scaler.transform(X)

            skf = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)

            smote_pipe = self._build_smote_pipeline(
                xgb.XGBClassifier(
                    n_estimators=200, max_depth=5, learning_rate=0.05,
                    subsample=0.8, colsample_bytree=0.8, random_state=42,
                    eval_metric="logloss", n_jobs=-1,
                )
            )

            cv_accuracy = cross_val_score(smote_pipe, X, y, cv=skf, scoring="accuracy", n_jobs=-1)
            cv_f1 = cross_val_score(smote_pipe, X, y, cv=skf, scoring="f1", n_jobs=-1)
            cv_auc = cross_val_score(smote_pipe, X, y, cv=skf, scoring="roc_auc", n_jobs=-1)

            print("\n=== 5-Fold Stratified CV (SMOTE inside folds) ===")
            print(f"  Accuracy:  {cv_accuracy.mean():.4f} ± {cv_accuracy.std():.4f}")
            print(f"  F1 Score:  {cv_f1.mean():.4f} ± {cv_f1.std():.4f}")
            print(f"  ROC AUC:   {cv_auc.mean():.4f} ± {cv_auc.std():.4f}")

            X_tr, X_val, y_tr, y_val = train_test_split(
                X, y, test_size=0.2, random_state=42, stratify=y
            )

            smote = SMOTE(random_state=42, k_neighbors=min(3, min(np.bincount(y_tr)) - 1))
            X_tr_res, y_tr_res = smote.fit_resample(X_tr, y_tr)

            X_tr_scaled = self.scaler.fit_transform(X_tr_res)
            X_val_scaled = self.scaler.transform(X_val)

            if self.ensemble is None:
                self.build_ensemble()

            self.ensemble.fit(X_tr_scaled, y_tr_res)
            self.voting_ensemble.fit(X_tr_scaled, y_tr_res)

            stack_preds = self.ensemble.predict(X_val_scaled)
            stack_proba = self.ensemble.predict_proba(X_val_scaled)[:, 1]

            vote_preds = self.voting_ensemble.predict(X_val_scaled)
            vote_proba = self.voting_ensemble.predict_proba(X_val_scaled)[:, 1]

            blended_proba = 0.6 * stack_proba + 0.4 * vote_proba
            blended_preds = (blended_proba >= 0.5).astype(int)

            print("\n=== Hold-Out Validation (20%) ===")
            for label, preds, proba in [
                ("Stacking", stack_preds, stack_proba),
                ("Voting", vote_preds, vote_proba),
                ("Blended", blended_preds, blended_proba),
            ]:
                acc = accuracy_score(y_val, preds)
                f1 = f1_score(y_val, preds)
                auc = roc_auc_score(y_val, proba)
                prec = precision_score(y_val, preds)
                rec = recall_score(y_val, preds)
                print(f"  {label:10s} — Acc: {acc:.4f}  F1: {f1:.4f}  AUC: {auc:.4f}  Prec: {prec:.4f}  Rec: {rec:.4f}")

            self.scaler.fit(X)
            X_all_scaled = self.scaler.transform(X)

            smote_all = SMOTE(random_state=42, k_neighbors=min(3, min(np.bincount(y)) - 1))
            X_all_res, y_all_res = smote_all.fit_resample(X_all_scaled, y)

            self.ensemble.fit(X_all_res, y_all_res)
            self.voting_ensemble.fit(X_all_res, y_all_res)
            self.X_train = X_all_scaled
            self.y_train = y
            self.is_trained = True

            self.cv_results = {
                "cv_accuracy_mean": round(float(cv_accuracy.mean()), 4),
                "cv_accuracy_std": round(float(cv_accuracy.std()), 4),
                "cv_f1_mean": round(float(cv_f1.mean()), 4),
                "cv_auc_mean": round(float(cv_auc.mean()), 4),
                "holdout_stacking_acc": round(float(accuracy_score(y_val, stack_preds)), 4),
                "holdout_voting_acc": round(float(accuracy_score(y_val, vote_preds)), 4),
                "holdout_blended_acc": round(float(accuracy_score(y_val, blended_preds)), 4),
            }

            print("\n=== TI Threshold Constants (Paper #322) ===")
            print(f"  TAU     = {TAU:.6f}")
            print(f"  EPSILON = {EPSILON:.6f}")
            print(f"  GAMMA   = {GAMMA:.6f}")
            print(f"  LAMBDA  = {LAMBDA:.6f}")
            print(f"  ETA     = {ETA:.6f}")

            return self.cv_results

        except Exception as e:
            raise RuntimeError(f"Training failed: {e}")

    def generate_submission(
        self,
        test_path: Optional[str] = None,
        output_path: str = "submission.csv",
    ) -> str:
        """Generate a Kaggle-format submission CSV for the test set."""
        if not self.is_trained:
            raise RuntimeError("Model not trained. Call train_and_evaluate() first.")

        try:
            if test_path and os.path.exists(test_path):
                test_df = pd.read_csv(test_path)
                test_ids = None
                if "id" in test_df.columns:
                    test_ids = test_df["id"]
                elif "Id" in test_df.columns:
                    test_ids = test_df["Id"]
                self._clean_dataframe(test_df)
            elif self.test_df is not None:
                test_df = self.test_df.copy()
                test_ids = self.test_ids
            else:
                raise RuntimeError("No test data available. Provide test_path or load test data first.")

            test_eng = self.engineer_features(test_df)
            X_test = test_eng[self.feature_names].values
            X_test_scaled = self.scaler.transform(X_test)

            stack_proba = self.ensemble.predict_proba(X_test_scaled)[:, 1]
            vote_proba = self.voting_ensemble.predict_proba(X_test_scaled)[:, 1]
            blended_proba = 0.6 * stack_proba + 0.4 * vote_proba
            predictions = (blended_proba >= 0.5).astype(int)

            submission = pd.DataFrame()
            if test_ids is not None:
                submission["id"] = test_ids.values
            else:
                submission["id"] = range(len(predictions))
            submission["target"] = predictions

            os.makedirs(os.path.dirname(os.path.abspath(output_path)), exist_ok=True) if os.path.dirname(output_path) else None
            submission.to_csv(output_path, index=False)
            print(f"\nSubmission saved to {output_path}")
            print(f"  Rows: {len(submission)}")
            print(f"  Predicted positive: {predictions.sum()} ({predictions.mean() * 100:.1f}%)")

            return output_path

        except Exception as e:
            raise RuntimeError(f"Submission generation failed: {e}")

    def run_full_pipeline(
        self,
        train_path: Optional[str] = None,
        test_path: Optional[str] = None,
        output_path: str = "submission.csv",
    ) -> Dict[str, Any]:
        """End-to-end pipeline: load → engineer → build → train → submit."""
        print("=" * 60)
        print("Kaggle S6E2 Heart Disease — Full Pipeline")
        print("=" * 60)

        self.load_data(train_path=train_path, test_path=test_path)

        results = self.train_and_evaluate()

        if self.test_df is not None or (test_path and os.path.exists(test_path)):
            self.generate_submission(test_path=test_path, output_path=output_path)
            results["submission_path"] = output_path

        print("\n" + "=" * 60)
        print("Pipeline complete.")
        print("=" * 60)
        return results


def demo():
    """Run the full pipeline on the built-in UCI dataset and print results."""
    print("\n" + "=" * 60)
    print("DEMO: Kaggle Heart Disease Submission Generator")
    print("=" * 60)

    engine = KaggleHeartDiseaseSubmission()
    engine.load_data()
    results = engine.train_and_evaluate()

    print("\n--- Demo Results Summary ---")
    for k, v in results.items():
        print(f"  {k}: {v}")

    return results


if __name__ == "__main__":
    demo()
