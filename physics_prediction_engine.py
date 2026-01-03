"""
Physics-Based Stock Prediction Engine
Treats market predictions as relative truths vs objective truths

Position = What people think NOW (current market sentiment)
Velocity = Speed toward/against GILE (trend direction)
Acceleration = What's changing the speed (momentum shifts)

Uses Myrion Resolution (MR) to resolve objective vs relative truth contradictions
"""

from typing import Dict, List, Tuple, Optional
import numpy as np
from datetime import datetime, timedelta

class PhysicsPredictionEngine:
    """
    Physics-based prediction using position/velocity/acceleration framework
    
    Position (x): Current market GILE rating (what people think now)
    Velocity (v): Rate of change toward/against true GILE (dGILE/dt)
    Acceleration (a): Momentum shift (d²GILE/dt²)
    
    Handles relative truth (flawed human opinions) vs objective truth (fundamentals)
    """
    
    def __init__(self):
        self.prediction_windows = {
            'weekly_start': 7,      # Monday predictions
            'weekly_end': 7,        # Friday evaluations
            'monthly': 30           # 30-day paper prediction cadence
        }
    
    def calculate_market_physics(self, 
                                 company_data: Dict,
                                 historical_gile: List[Tuple[datetime, float]],
                                 market_sentiment: float) -> Dict:
        """
        Calculate position/velocity/acceleration for a company
        
        Args:
            company_data: Current company KPIs and fundamentals
            historical_gile: [(timestamp, gile_score), ...] ordered oldest to newest
            market_sentiment: Current market opinion (0-1 normalized)
        
        Returns: {
            'position': float,          # Current market GILE
            'velocity': float,          # dGILE/dt
            'acceleration': float,      # d²GILE/dt²
            'objective_truth': float,   # Fundamental GILE (what it SHOULD be)
            'relative_truth': float,    # Market sentiment GILE (what people THINK)
            'dissonance': float,        # Gap between objective and relative
            'mr_required': bool         # Does this need Myrion Resolution?
        }
        """
        # Position: Current market-perceived GILE (relative truth)
        # This is what the market THINKS based on flawed low-GILE humans
        position = market_sentiment * 2.5 - 1.25  # Map 0-1 to GILE scale (-2.5 to +1.25)
        
        # Velocity: Rate of GILE change over time (trending toward or away from truth)
        if len(historical_gile) >= 2:
            recent = historical_gile[-1][1]
            older = historical_gile[-2][1]
            time_delta = (historical_gile[-1][0] - historical_gile[-2][0]).total_seconds() / (24 * 3600)  # Days
            velocity = (recent - older) / max(time_delta, 1.0)  # GILE change per day
        else:
            velocity = 0.0
        
        # Acceleration: Rate of velocity change (momentum shifts)
        if len(historical_gile) >= 3:
            v2 = (historical_gile[-1][1] - historical_gile[-2][1]) / max((historical_gile[-1][0] - historical_gile[-2][0]).total_seconds() / (24 * 3600), 1.0)
            v1 = (historical_gile[-2][1] - historical_gile[-3][1]) / max((historical_gile[-2][0] - historical_gile[-3][0]).total_seconds() / (24 * 3600), 1.0)
            time_delta2 = (historical_gile[-1][0] - historical_gile[-2][0]).total_seconds() / (24 * 3600)
            acceleration = (v2 - v1) / max(time_delta2, 1.0)
        else:
            acceleration = 0.0
        
        # Objective Truth: What GILE SHOULD be based on fundamentals (TI Framework analysis)
        # This is the TRUE company GILE independent of market opinion
        from contextual_gile_calculator import ContextualGILECalculator
        gile_calc = ContextualGILECalculator(ecosystem_type='company')
        objective_gile, _, _ = gile_calc.calculate_company_gile(company_data)  # Returns (gile, sigma, raw_metrics)
        
        # Relative Truth: What people THINK (market sentiment)
        relative_truth = position
        
        # Dissonance: Gap between what IS (objective) and what people THINK (relative)
        dissonance = objective_gile - relative_truth
        
        # Myrion Resolution Required? (Large contradiction = indeterminate)
        # If objective and relative disagree by >1.0 GILE units, needs MR
        mr_required = abs(dissonance) > 1.0
        
        return {
            'position': position,
            'velocity': velocity,
            'acceleration': acceleration,
            'objective_truth': objective_gile,
            'relative_truth': relative_truth,
            'dissonance': dissonance,
            'mr_required': mr_required,
            'timestamp': datetime.now()
        }
    
    def myrion_resolution(self, 
                         objective_truth: float,
                         relative_truth: float,
                         velocity: float,
                         acceleration: float,
                         depth: int = 1) -> Dict:
        """
        Apply Myrion Resolution to resolve objective vs relative truth contradictions
        
        Uses Pareto Dimension (PD) scoring:
        - Objective truth gets PD score based on fundamentals
        - Relative truth gets PD score based on momentum/sentiment
        - Higher PD wins the resolution
        
        Args:
            objective_truth: Fundamental GILE (what it SHOULD be)
            relative_truth: Market sentiment GILE (what people THINK)
            velocity: Rate toward/against GILE
            acceleration: Momentum shifts
            depth: MR depth (1=single, 2=double, 3=triple)
        
        Returns: {
            'resolved_gile': float,
            'resolution_type': str,  # 'objective', 'relative', 'indeterminate'
            'pd_objective': float,
            'pd_relative': float,
            'confidence': float,
            'depth_used': int
        }
        """
        # Calculate Pareto Dimension scores for each truth type
        
        # Objective Truth PD: Based on fundamental strength
        # Higher objective GILE = higher PD (fundamentals are sound)
        pd_objective = self._calculate_pd_score(
            base_value=objective_truth,
            modifiers={
                'fundamental_strength': objective_truth / 2.5,  # Normalize to 0-1
                'stability': 0.5  # Assume moderate stability for fundamentals
            }
        )
        
        # Relative Truth PD: Based on momentum and sentiment strength
        # Positive velocity toward GILE = higher PD (people are learning)
        # Negative velocity away from GILE = lower PD (delusion)
        pd_relative = self._calculate_pd_score(
            base_value=relative_truth,
            modifiers={
                'momentum': velocity / 0.5,  # Normalize velocity contribution
                'acceleration': acceleration / 0.1,  # Acceleration weight
                'sentiment_strength': abs(relative_truth) / 2.5  # How confident is market
            }
        )
        
        # Resolution logic
        if abs(pd_objective - pd_relative) < 0.5 and depth < 3:
            # Indeterminate at current depth - go deeper
            return self.myrion_resolution(
                objective_truth=objective_truth,
                relative_truth=relative_truth,
                velocity=velocity,
                acceleration=acceleration,
                depth=depth + 1
            )
        
        # Determine winner
        if pd_objective > pd_relative:
            resolved_gile = objective_truth
            resolution_type = 'objective'
            confidence = (pd_objective - pd_relative) / (pd_objective + pd_relative + 1e-9)
        elif pd_relative > pd_objective:
            resolved_gile = relative_truth
            resolution_type = 'relative'
            confidence = (pd_relative - pd_objective) / (pd_objective + pd_relative + 1e-9)
        else:
            # True indeterminate - blend with caution weighting
            resolved_gile = (objective_truth + relative_truth) / 2.0
            resolution_type = 'indeterminate'
            confidence = 0.0
        
        return {
            'resolved_gile': resolved_gile,
            'resolution_type': resolution_type,
            'pd_objective': pd_objective,
            'pd_relative': pd_relative,
            'confidence': confidence,
            'depth_used': depth,
            'indeterminate': resolution_type == 'indeterminate'
        }
    
    def _calculate_pd_score(self, base_value: float, modifiers: Dict[str, float]) -> float:
        """
        Calculate Pareto Dimension score
        
        PD = base_value + weighted_modifiers
        Clipped to [-3, +3] range
        """
        pd = base_value
        
        for modifier_name, modifier_value in modifiers.items():
            # Weight modifiers (can be tuned)
            weight = 0.3  # Default modifier weight
            pd += weight * np.clip(modifier_value, -1, 1)
        
        return np.clip(pd, -3.0, 3.0)
    
    def generate_prediction(self,
                           ticker: str,
                           company_data: Dict,
                           historical_gile: List[Tuple[datetime, float]],
                           market_sentiment: float,
                           prediction_window: str = 'monthly',
                           prediction_date: Optional[datetime] = None) -> Dict:
        """
        Generate physics-based prediction for a company
        
        Args:
            ticker: Stock ticker symbol
            company_data: Company KPIs
            historical_gile: Historical GILE time series
            market_sentiment: Current market sentiment (0-1)
            prediction_window: 'weekly_start', 'weekly_end', 'monthly'
            prediction_date: Date of prediction (default: now)
        
        Returns: {
            'ticker': str,
            'signal': 'BUY' | 'SELL' | 'HOLD',
            'target_change_pct': float,
            'physics': {...},
            'mr_result': {...},
            'window_days': int,
            'rationale': str
        }
        """
        # Use provided prediction_date or default to now
        if prediction_date is None:
            prediction_date = datetime.now()
        # Calculate physics
        physics = self.calculate_market_physics(company_data, historical_gile, market_sentiment)
        
        # Apply Myrion Resolution if needed
        if physics['mr_required']:
            mr_result = self.myrion_resolution(
                objective_truth=physics['objective_truth'],
                relative_truth=physics['relative_truth'],
                velocity=physics['velocity'],
                acceleration=physics['acceleration']
            )
        else:
            # No MR needed - objective and relative align
            mr_result = {
                'resolved_gile': physics['objective_truth'],
                'resolution_type': 'aligned',
                'confidence': 1.0,
                'indeterminate': False
            }
        
        # Generate signal based on resolved GILE + velocity + acceleration
        resolved_gile = mr_result['resolved_gile']
        
        # Signal logic:
        # BUY: High resolved GILE (>0.5) OR positive velocity+acceleration (heading toward GILE)
        # SELL: Low resolved GILE (<-0.5) OR negative velocity+acceleration (heading away from GILE)
        # HOLD: Moderate GILE OR indeterminate
        
        if mr_result['indeterminate']:
            # Indeterminate contradictions = HOLD (uncertainty)
            signal = 'HOLD'
            target_change_pct = 0.0
            rationale = f"INDETERMINATE: Objective ({physics['objective_truth']:.2f}) vs Relative ({physics['relative_truth']:.2f}) unresolvable at depth {mr_result['depth_used']}"
        
        elif resolved_gile > 0.8 or (physics['velocity'] > 0.1 and physics['acceleration'] > 0):
            # Strong fundamentals OR strong momentum toward GILE
            signal = 'BUY'
            # Velocity-weighted target: faster velocity = higher target
            target_change_pct = 10 + (physics['velocity'] * 20)
            rationale = f"BUY: Resolved GILE {resolved_gile:.2f}, v={physics['velocity']:.3f}, a={physics['acceleration']:.4f} ({mr_result['resolution_type']})"
        
        elif resolved_gile < -0.3 or (physics['velocity'] < -0.1 and physics['acceleration'] < 0):
            # Weak fundamentals OR strong momentum away from GILE
            signal = 'SELL'
            target_change_pct = -8 + (physics['velocity'] * 15)
            rationale = f"SELL: Resolved GILE {resolved_gile:.2f}, v={physics['velocity']:.3f}, a={physics['acceleration']:.4f} ({mr_result['resolution_type']})"
        
        else:
            # Middle ground
            signal = 'HOLD'
            target_change_pct = 0.0
            rationale = f"HOLD: Resolved GILE {resolved_gile:.2f}, stable momentum ({mr_result['resolution_type']})"
        
        window_days = self.prediction_windows[prediction_window]
        
        return {
            'ticker': ticker,
            'signal': signal,
            'target_change_pct': target_change_pct,
            'window_days': window_days,
            'physics': physics,
            'mr_result': mr_result,
            'rationale': rationale,
            'prediction_date': prediction_date,
            'evaluation_date': prediction_date + timedelta(days=window_days)
        }
    
    def identify_indeterminate_predictions(self, predictions: List[Dict]) -> List[Dict]:
        """
        Filter predictions that are indeterminate (require user review)
        
        Args:
            predictions: List of prediction dicts
        
        Returns: List of indeterminate predictions for user review
        """
        indeterminate = []
        
        for pred in predictions:
            if pred.get('mr_result', {}).get('indeterminate', False):
                indeterminate.append({
                    'ticker': pred['ticker'],
                    'objective_truth': pred['physics']['objective_truth'],
                    'relative_truth': pred['physics']['relative_truth'],
                    'dissonance': pred['physics']['dissonance'],
                    'mr_depth': pred['mr_result']['depth_used'],
                    'pd_objective': pred['mr_result']['pd_objective'],
                    'pd_relative': pred['mr_result']['pd_relative'],
                    'rationale': pred['rationale'],
                    'requires_review': True
                })
        
        return indeterminate
