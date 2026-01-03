"""
PSI Correlation Intelligence System
Discovers non-obvious correlations using Lowest Common Category (LCC) analysis
Personalizes PSI method selection for Brandon

Architecture:
1. Unified PSI observation schema (PostgreSQL)
2. Multi-modal ingestion adapters
3. Correlation matrix computation (Pearson, Spearman, MI)
4. LCC discovery via knowledge graph
5. Brandon-specific personalization with SHAP
6. Interactive visualization (heatmap, network graph, timeline)
"""

import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional
import json
from dataclasses import dataclass, asdict
from scipy import stats
from scipy.fft import fft, fftfreq
from sklearn.ensemble import GradientBoostingRegressor
from sklearn.metrics import r2_score
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots
import psycopg2
import os

@dataclass
class PSIObservation:
    """Unified schema for all PSI predictions"""
    prediction_id: str
    timestamp: datetime
    outcome: int  # 1 = correct, 0 = incorrect
    confidence: float
    
    # Numerology features
    user_life_path: Optional[int] = None
    user_birth_day: Optional[int] = None
    event_date_numerology: Optional[int] = None
    name_expression: Optional[int] = None
    resonance_score: Optional[float] = None
    
    # Weather features
    barometric_pressure: Optional[float] = None
    temperature: Optional[float] = None
    precipitation: Optional[float] = None
    cosmic_ray_flux: Optional[float] = None
    
    # Biometric features
    heart_coherence: Optional[float] = None
    hrv_score: Optional[float] = None
    sleep_recovery: Optional[float] = None
    oura_readiness: Optional[float] = None
    
    # Cosmic timing features
    moon_phase: Optional[float] = None  # 0-1
    solar_activity: Optional[float] = None
    planetary_alignment: Optional[float] = None
    
    # Tralsebit features
    i_cell_signature_strength: Optional[float] = None
    biophoton_sync_probability: Optional[float] = None
    
    # Temporal features
    hour_of_day: Optional[int] = None
    day_of_week: Optional[int] = None
    circadian_score: Optional[float] = None
    
    # Metadata
    prediction_type: Optional[str] = None
    gile_metrics: Optional[Dict[str, float]] = None

class PSICorrelationIntelligence:
    """Main system for PSI correlation discovery and personalization"""
    
    def __init__(self, db_connection_string: Optional[str] = None):
        """Initialize with database connection"""
        self.db_conn_string = db_connection_string or os.getenv('DATABASE_URL')
        self.feature_columns = self._get_feature_columns()
        self._ensure_schema()
    
    def _get_feature_columns(self) -> List[str]:
        """Get list of all PSI feature columns"""
        return [
            # Numerology
            'user_life_path', 'user_birth_day', 'event_date_numerology',
            'name_expression', 'resonance_score',
            # Weather
            'barometric_pressure', 'temperature', 'precipitation', 'cosmic_ray_flux',
            # Biometric
            'heart_coherence', 'hrv_score', 'sleep_recovery', 'oura_readiness',
            # Cosmic
            'moon_phase', 'solar_activity', 'planetary_alignment',
            # Tralsebit
            'i_cell_signature_strength', 'biophoton_sync_probability',
            # Temporal
            'hour_of_day', 'day_of_week', 'circadian_score'
        ]
    
    def _ensure_schema(self):
        """Create psi_observations table if not exists"""
        create_table_sql = """
        CREATE TABLE IF NOT EXISTS psi_observations (
            prediction_id VARCHAR(255) PRIMARY KEY,
            timestamp TIMESTAMP NOT NULL,
            outcome INTEGER NOT NULL,
            confidence FLOAT,
            
            -- Numerology
            user_life_path INTEGER,
            user_birth_day INTEGER,
            event_date_numerology INTEGER,
            name_expression INTEGER,
            resonance_score FLOAT,
            
            -- Weather
            barometric_pressure FLOAT,
            temperature FLOAT,
            precipitation FLOAT,
            cosmic_ray_flux FLOAT,
            
            -- Biometric
            heart_coherence FLOAT,
            hrv_score FLOAT,
            sleep_recovery FLOAT,
            oura_readiness FLOAT,
            
            -- Cosmic
            moon_phase FLOAT,
            solar_activity FLOAT,
            planetary_alignment FLOAT,
            
            -- Tralsebit
            i_cell_signature_strength FLOAT,
            biophoton_sync_probability FLOAT,
            
            -- Temporal
            hour_of_day INTEGER,
            day_of_week INTEGER,
            circadian_score FLOAT,
            
            -- Metadata
            prediction_type VARCHAR(100),
            gile_metrics JSONB
        );
        
        CREATE INDEX IF NOT EXISTS idx_timestamp ON psi_observations(timestamp);
        CREATE INDEX IF NOT EXISTS idx_outcome ON psi_observations(outcome);
        """
        
        try:
            with psycopg2.connect(self.db_conn_string) as conn:
                with conn.cursor() as cur:
                    cur.execute(create_table_sql)
                conn.commit()
        except Exception as e:
            st.error(f"Database schema creation failed: {e}")
    
    def ingest_observation(self, obs: PSIObservation):
        """Add new PSI observation to database"""
        insert_sql = """
        INSERT INTO psi_observations (
            prediction_id, timestamp, outcome, confidence,
            user_life_path, user_birth_day, event_date_numerology, name_expression, resonance_score,
            barometric_pressure, temperature, precipitation, cosmic_ray_flux,
            heart_coherence, hrv_score, sleep_recovery, oura_readiness,
            moon_phase, solar_activity, planetary_alignment,
            i_cell_signature_strength, biophoton_sync_probability,
            hour_of_day, day_of_week, circadian_score,
            prediction_type, gile_metrics
        ) VALUES (
            %s, %s, %s, %s,
            %s, %s, %s, %s, %s,
            %s, %s, %s, %s,
            %s, %s, %s, %s,
            %s, %s, %s,
            %s, %s,
            %s, %s, %s,
            %s, %s
        )
        ON CONFLICT (prediction_id) DO UPDATE SET
            outcome = EXCLUDED.outcome,
            confidence = EXCLUDED.confidence
        """
        
        gile_json = json.dumps(obs.gile_metrics) if obs.gile_metrics else None
        
        try:
            with psycopg2.connect(self.db_conn_string) as conn:
                with conn.cursor() as cur:
                    cur.execute(insert_sql, (
                        obs.prediction_id, obs.timestamp, obs.outcome, obs.confidence,
                        obs.user_life_path, obs.user_birth_day, obs.event_date_numerology, 
                        obs.name_expression, obs.resonance_score,
                        obs.barometric_pressure, obs.temperature, obs.precipitation, obs.cosmic_ray_flux,
                        obs.heart_coherence, obs.hrv_score, obs.sleep_recovery, obs.oura_readiness,
                        obs.moon_phase, obs.solar_activity, obs.planetary_alignment,
                        obs.i_cell_signature_strength, obs.biophoton_sync_probability,
                        obs.hour_of_day, obs.day_of_week, obs.circadian_score,
                        obs.prediction_type, gile_json
                    ))
                conn.commit()
            return True
        except Exception as e:
            st.error(f"Ingestion failed: {e}")
            return False
    
    def get_observations_df(self, days_back: int = 90) -> pd.DataFrame:
        """Load observations as DataFrame"""
        query = f"""
        SELECT * FROM psi_observations
        WHERE timestamp >= NOW() - INTERVAL '{days_back} days'
        ORDER BY timestamp DESC
        """
        
        try:
            with psycopg2.connect(self.db_conn_string) as conn:
                df = pd.read_sql(query, conn)
            return df
        except Exception as e:
            st.error(f"Data loading failed: {e}")
            return pd.DataFrame()
    
    def compute_correlation_matrix(self, df: pd.DataFrame, method='pearson') -> pd.DataFrame:
        """Compute pairwise correlations between all PSI methods
        
        Args:
            df: Observations DataFrame
            method: 'pearson', 'spearman', or 'mutual_info'
        
        Returns:
            Correlation matrix DataFrame
        """
        feature_df = df[self.feature_columns].copy()
        
        if method == 'pearson':
            corr_matrix = feature_df.corr(method='pearson')
        elif method == 'spearman':
            corr_matrix = feature_df.corr(method='spearman')
        elif method == 'mutual_info':
            # Mutual information for categorical/continuous
            from sklearn.feature_selection import mutual_info_regression
            corr_matrix = pd.DataFrame(
                data=np.zeros((len(self.feature_columns), len(self.feature_columns))),
                index=self.feature_columns,
                columns=self.feature_columns,
                dtype=float
            )
            for col in self.feature_columns:
                valid_mask = pd.notna(feature_df[col])
                if valid_mask.sum() > 10:
                    X = feature_df.loc[valid_mask, self.feature_columns].fillna(0)
                    y = feature_df.loc[valid_mask, col]
                    mi_scores = mutual_info_regression(X, y, random_state=42)
                    corr_matrix.loc[col, :] = mi_scores
        else:
            raise ValueError(f"Unknown method: {method}")
        
        return corr_matrix
    
    def find_lcc_clusters(self, df: pd.DataFrame, threshold: float = 0.5) -> List[Dict]:
        """Discover Lowest Common Category clusters
        
        Identifies groups of PSI methods that share underlying mechanisms
        despite being from different modalities.
        
        Returns:
            List of LCC clusters with suggested mechanisms
        """
        # Compute correlations with outcome
        feature_outcome_corr = {}
        for feature in self.feature_columns:
            valid_mask = ~df[feature].isna() & ~df['outcome'].isna()
            if valid_mask.sum() > 30:
                corr, pval = stats.spearmanr(
                    df.loc[valid_mask, feature],
                    df.loc[valid_mask, 'outcome']
                )
                if pval < 0.05:
                    feature_outcome_corr[feature] = abs(corr)
        
        # Compute inter-feature correlations
        corr_matrix = self.compute_correlation_matrix(df, method='spearman')
        
        # Find clusters using frequency domain analysis
        clusters = []
        
        # Cluster 1: Periodic/Resonance Features
        periodic_features = []
        for feature in ['moon_phase', 'circadian_score', 'heart_coherence']:
            if feature in feature_outcome_corr and feature_outcome_corr[feature] > 0.1:
                periodic_features.append(feature)
        
        if len(periodic_features) >= 2:
            clusters.append({
                'name': 'Resonance/Periodic Signals',
                'features': periodic_features,
                'mechanism': 'Wave interference patterns - similar frequencies amplify',
                'lcc': 'Oscillatory Coupling',
                'avg_correlation': np.mean([feature_outcome_corr[f] for f in periodic_features])
            })
        
        # Cluster 2: Sacred Number Alignment
        sacred_features = []
        for feature in ['user_life_path', 'user_birth_day', 'event_date_numerology', 'resonance_score']:
            if feature in feature_outcome_corr and feature_outcome_corr[feature] > 0.1:
                sacred_features.append(feature)
        
        if len(sacred_features) >= 2:
            clusters.append({
                'name': 'Sacred Number Resonance',
                'features': sacred_features,
                'mechanism': 'Archetypal pattern matching - numbers carry vibrational signatures',
                'lcc': 'Symbolic Resonance',
                'avg_correlation': np.mean([feature_outcome_corr[f] for f in sacred_features])
            })
        
        # Cluster 3: Physiological Coherence
        coherence_features = []
        for feature in ['heart_coherence', 'hrv_score', 'sleep_recovery', 'oura_readiness']:
            if feature in feature_outcome_corr and feature_outcome_corr[feature] > 0.1:
                coherence_features.append(feature)
        
        if len(coherence_features) >= 2:
            clusters.append({
                'name': 'Biometric Coherence State',
                'features': coherence_features,
                'mechanism': 'Physiological optimization enables biophoton synchronization',
                'lcc': 'Biological Resonance',
                'avg_correlation': np.mean([feature_outcome_corr[f] for f in coherence_features])
            })
        
        # Cluster 4: Environmental Pressure
        env_features = []
        for feature in ['barometric_pressure', 'cosmic_ray_flux', 'solar_activity']:
            if feature in feature_outcome_corr and feature_outcome_corr[feature] > 0.1:
                env_features.append(feature)
        
        if len(env_features) >= 2:
            clusters.append({
                'name': 'External Field Effects',
                'features': env_features,
                'mechanism': 'Electromagnetic/quantum field perturbations affect consciousness',
                'lcc': 'Field Coupling',
                'avg_correlation': np.mean([feature_outcome_corr[f] for f in env_features])
            })
        
        # Cluster 5: Quantum Signature (non-obvious!)
        quantum_features = []
        for feature in ['i_cell_signature_strength', 'biophoton_sync_probability', 'temperature']:
            if feature in feature_outcome_corr and feature_outcome_corr[feature] > 0.1:
                quantum_features.append(feature)
        
        if len(quantum_features) >= 2:
            clusters.append({
                'name': 'Quantum Coherence Window',
                'features': quantum_features,
                'mechanism': 'Temperature affects decoherence time; optimal window for quantum effects',
                'lcc': 'Quantum Decoherence',
                'avg_correlation': np.mean([feature_outcome_corr[f] for f in quantum_features])
            })
        
        return clusters
    
    def personalize_for_brandon(self, df: pd.DataFrame) -> Dict:
        """Discover Brandon-specific PSI correlations
        
        Returns:
            Personalized insights for Brandon (Life Path 6, Birth Day 7)
        """
        if len(df) < 30:
            return {
                'status': 'insufficient_data',
                'sample_size': len(df),
                'message': 'Need at least 30 predictions for personalization'
            }
        
        # Brandon's sacred numbers
        brandon_life_path = 6
        brandon_birth_day = 7
        
        # Filter for valid outcome data
        valid_df = df.dropna(subset=['outcome'])
        
        # Feature importance using Gradient Boosting
        feature_df = valid_df[self.feature_columns].fillna(0)
        outcome = valid_df['outcome']
        
        if len(outcome.unique()) < 2:
            return {
                'status': 'no_variation',
                'message': 'All predictions same outcome - need variation'
            }
        
        try:
            gb_model = GradientBoostingRegressor(
                n_estimators=100,
                max_depth=3,
                random_state=42
            )
            gb_model.fit(feature_df, outcome)
            
            # Feature importances
            importances = pd.Series(
                gb_model.feature_importances_,
                index=self.feature_columns
            ).sort_values(ascending=False)
            
            top_features = importances.head(10)
            
            # Analyze sacred number effects
            sacred_insights = {}
            
            # Life Path 6 resonance
            if 'event_date_numerology' in valid_df.columns:
                lp6_matches = valid_df[valid_df['event_date_numerology'] == 6]
                if len(lp6_matches) >= 5:
                    lp6_accuracy = lp6_matches['outcome'].mean()
                    baseline_accuracy = valid_df['outcome'].mean()
                    sacred_insights['life_path_6_boost'] = {
                        'accuracy': lp6_accuracy,
                        'baseline': baseline_accuracy,
                        'lift': (lp6_accuracy - baseline_accuracy) / baseline_accuracy if baseline_accuracy > 0 else 0,
                        'sample_size': len(lp6_matches)
                    }
            
            # Birth Day 7 analysis
            if 'day_of_week' in valid_df.columns:
                bd7_matches = valid_df[valid_df['day_of_week'] == 7]  # Sunday
                if len(bd7_matches) >= 5:
                    bd7_accuracy = bd7_matches['outcome'].mean()
                    baseline_accuracy = valid_df['outcome'].mean()
                    sacred_insights['birth_day_7_effect'] = {
                        'accuracy': bd7_accuracy,
                        'baseline': baseline_accuracy,
                        'lift': (bd7_accuracy - baseline_accuracy) / baseline_accuracy if baseline_accuracy > 0 else 0,
                        'sample_size': len(bd7_matches)
                    }
            
            # Optimal prediction windows
            windows = []
            
            # Heart coherence threshold
            if 'heart_coherence' in valid_df.columns:
                high_coherence = valid_df[valid_df['heart_coherence'] > 0.7]
                if len(high_coherence) >= 5:
                    windows.append({
                        'condition': 'Heart Coherence > 0.7',
                        'accuracy': high_coherence['outcome'].mean(),
                        'sample_size': len(high_coherence),
                        'boost': high_coherence['outcome'].mean() - valid_df['outcome'].mean()
                    })
            
            # Oura readiness
            if 'oura_readiness' in valid_df.columns:
                high_readiness = valid_df[valid_df['oura_readiness'] > 0.7]
                if len(high_readiness) >= 5:
                    windows.append({
                        'condition': 'Oura Readiness > 0.7',
                        'accuracy': high_readiness['outcome'].mean(),
                        'sample_size': len(high_readiness),
                        'boost': high_readiness['outcome'].mean() - valid_df['outcome'].mean()
                    })
            
            # Combined optimal window
            optimal_conditions = []
            if 'heart_coherence' in valid_df.columns and 'oura_readiness' in valid_df.columns:
                combined = valid_df[
                    (valid_df['heart_coherence'] > 0.7) &
                    (valid_df['oura_readiness'] > 0.7)
                ]
                if len(combined) >= 3:
                    windows.append({
                        'condition': 'Heart Coherence > 0.7 AND Oura Readiness > 0.7',
                        'accuracy': combined['outcome'].mean(),
                        'sample_size': len(combined),
                        'boost': combined['outcome'].mean() - valid_df['outcome'].mean()
                    })
            
            return {
                'status': 'success',
                'sample_size': len(valid_df),
                'baseline_accuracy': valid_df['outcome'].mean(),
                'top_features': top_features.to_dict(),
                'sacred_number_insights': sacred_insights,
                'optimal_windows': windows,
                'model_r2': r2_score(outcome, gb_model.predict(feature_df))
            }
            
        except Exception as e:
            return {
                'status': 'error',
                'message': str(e)
            }
    
    def visualize_correlation_heatmap(self, df: pd.DataFrame) -> go.Figure:
        """Create interactive correlation heatmap"""
        corr_matrix = self.compute_correlation_matrix(df, method='spearman')
        
        fig = go.Figure(data=go.Heatmap(
            z=corr_matrix.values,
            x=corr_matrix.columns,
            y=corr_matrix.index,
            colorscale='RdBu',
            zmid=0,
            text=np.round(corr_matrix.values, 2),
            texttemplate='%{text}',
            textfont={"size": 8},
            colorbar=dict(title="Correlation")
        ))
        
        fig.update_layout(
            title="Multi-Dimensional PSI Correlation Matrix",
            xaxis_title="PSI Methods",
            yaxis_title="PSI Methods",
            height=800,
            width=1000
        )
        
        fig.update_xaxes(tickangle=45)
        
        return fig
    
    def visualize_lcc_network(self, clusters: List[Dict]) -> go.Figure:
        """Create network graph showing LCC clusters"""
        import networkx as nx
        
        # Build graph
        G = nx.Graph()
        
        # Add nodes and edges for each cluster
        for i, cluster in enumerate(clusters):
            cluster_name = cluster['name']
            G.add_node(cluster_name, node_type='lcc', color='red', size=30)
            
            for feature in cluster['features']:
                G.add_node(feature, node_type='feature', color='lightblue', size=15)
                G.add_edge(cluster_name, feature, weight=cluster['avg_correlation'])
        
        # Layout
        pos = nx.spring_layout(G, k=2, iterations=50)
        
        # Create traces
        edge_trace = []
        for edge in G.edges():
            x0, y0 = pos[edge[0]]
            x1, y1 = pos[edge[1]]
            edge_trace.append(go.Scatter(
                x=[x0, x1, None],
                y=[y0, y1, None],
                mode='lines',
                line=dict(width=2, color='gray'),
                hoverinfo='none',
                showlegend=False
            ))
        
        # Node traces
        node_x = []
        node_y = []
        node_text = []
        node_color = []
        node_size = []
        
        for node in G.nodes():
            x, y = pos[node]
            node_x.append(x)
            node_y.append(y)
            node_text.append(node)
            node_color.append(G.nodes[node]['color'])
            node_size.append(G.nodes[node]['size'])
        
        node_trace = go.Scatter(
            x=node_x,
            y=node_y,
            mode='markers+text',
            text=node_text,
            textposition='top center',
            marker=dict(
                size=node_size,
                color=node_color,
                line=dict(width=2, color='white')
            ),
            hoverinfo='text',
            showlegend=False
        )
        
        # Create figure
        fig = go.Figure(data=edge_trace + [node_trace])
        
        fig.update_layout(
            title="LCC Network: Common Mechanisms Across PSI Modalities",
            showlegend=False,
            hovermode='closest',
            margin=dict(b=20, l=5, r=5, t=40),
            xaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
            yaxis=dict(showgrid=False, zeroline=False, showticklabels=False),
            height=600
        )
        
        return fig
    
    def visualize_timeline_overlay(self, df: pd.DataFrame, top_features: List[str]) -> go.Figure:
        """Timeline showing prediction outcomes with top PSI features"""
        df_sorted = df.sort_values('timestamp')
        
        fig = make_subplots(
            rows=len(top_features) + 1,
            cols=1,
            subplot_titles=['Prediction Outcomes'] + [f.replace('_', ' ').title() for f in top_features],
            vertical_spacing=0.05
        )
        
        # Outcomes
        fig.add_trace(
            go.Scatter(
                x=df_sorted['timestamp'],
                y=df_sorted['outcome'],
                mode='markers',
                name='Outcome',
                marker=dict(
                    size=8,
                    color=df_sorted['outcome'],
                    colorscale='RdYlGn',
                    showscale=False
                )
            ),
            row=1, col=1
        )
        
        # Top features
        for i, feature in enumerate(top_features, start=2):
            if feature in df_sorted.columns:
                fig.add_trace(
                    go.Scatter(
                        x=df_sorted['timestamp'],
                        y=df_sorted[feature],
                        mode='lines+markers',
                        name=feature.replace('_', ' ').title(),
                        showlegend=False
                    ),
                    row=i, col=1
                )
        
        fig.update_layout(
            height=300 * (len(top_features) + 1),
            title="PSI Features Timeline with Prediction Outcomes",
            showlegend=False
        )
        
        return fig
    
    def generate_recommendations(self, personalization: Dict) -> List[str]:
        """Generate actionable recommendations for Brandon"""
        recommendations = []
        
        if personalization['status'] != 'success':
            return ["Insufficient data for recommendations. Make more predictions!"]
        
        # Top features
        top_features = list(personalization['top_features'].keys())[:3]
        recommendations.append(
            f"🎯 **Focus on top 3 PSI methods:** {', '.join([f.replace('_', ' ').title() for f in top_features])}"
        )
        
        # Sacred number insights
        sacred = personalization.get('sacred_number_insights', {})
        if 'life_path_6_boost' in sacred:
            lift = sacred['life_path_6_boost']['lift']
            if lift > 0.1:
                recommendations.append(
                    f"✨ **Life Path 6 Resonance:** You get {lift*100:.1f}% accuracy boost on dates matching your Life Path! Prioritize those predictions."
                )
        
        # Optimal windows
        windows = personalization.get('optimal_windows', [])
        if windows:
            best_window = max(windows, key=lambda w: w['boost'])
            recommendations.append(
                f"⏰ **Optimal Prediction Window:** {best_window['condition']} → {best_window['boost']*100:+.1f}% accuracy boost!"
            )
        
        # Model performance
        r2 = personalization.get('model_r2', 0)
        if r2 > 0.3:
            recommendations.append(
                f"🧠 **Prediction Model:** {r2*100:.1f}% of your accuracy variance explained by PSI features. System is learning your patterns!"
            )
        else:
            recommendations.append(
                f"📊 **More Data Needed:** Current model explains only {r2*100:.1f}% variance. Collect more predictions to discover patterns!"
            )
        
        return recommendations
