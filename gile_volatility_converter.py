"""
GILE Sigma to Standard Deviation Converter
Translates TI Framework volatility metrics to conventional finance terms
"""

import numpy as np
from typing import Dict, Tuple

class GILEVolatilityConverter:
    """
    Converts GILE σ values to conventional standard deviation metrics
    """
    
    def __init__(self):
        # GILE σ mapping: σ = (GILE + 2.5) / 5
        # GILE ranges from -2.5 to +2.5
        # σ ranges from 0 to 1
        pass
    
    def gile_to_sigma(self, gile: float) -> float:
        """
        Convert GILE score to sigma (0-1 scale)
        
        Args:
            gile: GILE score (-2.5 to +2.5)
        
        Returns:
            Sigma value (0 to 1)
        """
        return (gile + 2.5) / 5.0
    
    def sigma_to_gile(self, sigma: float) -> float:
        """
        Convert sigma to GILE score
        
        Args:
            sigma: Sigma value (0 to 1)
        
        Returns:
            GILE score (-2.5 to +2.5)
        """
        return 5 * sigma - 2.5
    
    def gile_to_annualized_volatility(
        self, 
        gile_scores: np.ndarray,
        trading_days: int = 252
    ) -> float:
        """
        Convert GILE score trajectory to annualized volatility (%)
        
        This maps GILE variation to conventional stock volatility metrics
        
        Args:
            gile_scores: Array of GILE scores over time
            trading_days: Trading days per year (default 252)
        
        Returns:
            Annualized volatility as percentage
        """
        # Convert GILE to sigma
        sigma_scores = np.array([self.gile_to_sigma(g) for g in gile_scores])
        
        # Calculate daily volatility in sigma space
        daily_sigma_changes = np.diff(sigma_scores)
        sigma_volatility = np.std(daily_sigma_changes)
        
        # Map sigma volatility to stock price volatility
        # Empirical mapping: σ changes of 0.1 ≈ 10% stock move
        # This is calibrated to match typical i-cell company volatility
        daily_stock_volatility = sigma_volatility * 100  # Convert to percentage
        
        # Annualize
        annualized_vol = daily_stock_volatility * np.sqrt(trading_days)
        
        return annualized_vol
    
    def calculate_gile_sharpe_equivalent(
        self,
        gile_returns: np.ndarray,
        risk_free_rate: float = 0.04
    ) -> float:
        """
        Calculate Sharpe-like ratio using GILE metrics
        
        Args:
            gile_returns: Array of GILE-based return predictions
            risk_free_rate: Annual risk-free rate (default 4%)
        
        Returns:
            Sharpe ratio equivalent
        """
        mean_return = np.mean(gile_returns)
        std_return = np.std(gile_returns)
        
        if std_return == 0:
            return 0.0
        
        return (mean_return - risk_free_rate) / std_return
    
    def map_gile_to_stock_volatility_class(self, gile: float) -> Dict[str, any]:
        """
        Map GILE score to conventional volatility classifications
        
        Args:
            gile: GILE score
        
        Returns:
            Dict with volatility class and expected annualized volatility
        """
        sigma = self.gile_to_sigma(gile)
        
        # Empirical mapping based on i-cell company analysis
        if sigma < 0.3:
            vol_class = "Very High Risk"
            expected_vol = 45  # ~45% annualized
        elif sigma < 0.42:
            vol_class = "High Risk (Below Soul Threshold)"
            expected_vol = 35
        elif sigma < 0.5:
            vol_class = "Moderate-High Risk"
            expected_vol = 25
        elif sigma < 0.7:
            vol_class = "Moderate Risk"
            expected_vol = 20
        elif sigma < 0.85:
            vol_class = "Low-Moderate Risk"
            expected_vol = 15
        else:
            vol_class = "Low Risk (Defensive)"
            expected_vol = 10
        
        return {
            'gile': gile,
            'sigma': sigma,
            'volatility_class': vol_class,
            'expected_annual_volatility_pct': expected_vol,
            'soul_threshold_status': 'Above' if sigma >= 0.42 else 'Below'
        }
    
    def convert_gile_velocity_to_momentum(
        self,
        gile_velocity: float,
        time_period_days: int = 30
    ) -> Tuple[str, float]:
        """
        Convert GILE velocity to stock momentum classification
        
        Args:
            gile_velocity: dGILE/dt (GILE units per day)
            time_period_days: Period for momentum calculation
        
        Returns:
            Tuple of (momentum_class, expected_monthly_return_pct)
        """
        # GILE velocity units per month
        monthly_gile_change = gile_velocity * time_period_days
        
        # Map to expected stock return
        # Empirical: +0.5 GILE/month ≈ +10% stock return
        expected_return = monthly_gile_change * 20  # Percentage
        
        if monthly_gile_change > 0.3:
            momentum = "Strong Bullish"
        elif monthly_gile_change > 0.1:
            momentum = "Moderate Bullish"
        elif monthly_gile_change > -0.1:
            momentum = "Neutral/Consolidation"
        elif monthly_gile_change > -0.3:
            momentum = "Moderate Bearish"
        else:
            momentum = "Strong Bearish"
        
        return momentum, expected_return
    
    def generate_comparison_table(self, gile: float) -> str:
        """Generate formatted comparison table for research paper"""
        info = self.map_gile_to_stock_volatility_class(gile)
        
        return f"""
| Metric | TI Framework | Conventional Equivalent |
|--------|--------------|------------------------|
| **GILE Score** | {info['gile']:.2f} | N/A |
| **Sigma (σ)** | {info['sigma']:.3f} | N/A |
| **Volatility Class** | {info['volatility_class']} | {info['expected_annual_volatility_pct']}% annual vol |
| **Soul Threshold** | {info['soul_threshold_status']} (0.42) | N/A |
| **Risk Category** | Based on i-cell coherence | VIX-based classification |
"""
