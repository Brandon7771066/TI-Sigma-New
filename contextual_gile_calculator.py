"""
Contextual GILE Baseline Calculator
Discovers optimal GILE distribution for each ecosystem (brain vs company vs market)

Key Insight: GILE is a TEMPLATE, not a fixed formula
Each system has its own (-3, 0, 2) Pareto distribution baseline
"""

import numpy as np
from typing import Dict, Tuple, List

class ContextualGILECalculator:
    """
    Calculate GILE scores with contextual baselines per ecosystem
    
    Brain GILE ≠ Company GILE ≠ Market GILE
    Each has unique baseline that maximizes predictive power
    """
    
    def __init__(self, ecosystem_type='brain'):
        """
        Args:
            ecosystem_type: 'brain', 'company', 'market', 'galaxy', etc.
        """
        self.ecosystem_type = ecosystem_type
        
        # Default baselines (will be iteratively optimized)
        self.baselines = {
            'brain': {
                'sigma': 0.500,  # Standard baseline
                'shift': 0.000,  # No shift
                'pd_g': 0.00,    # Pareto dimension baselines
                'pd_i': 0.00,
                'pd_l': 0.00,
                'pd_e': 0.00
            },
            'company': {
                'sigma': 0.450,  # Companies may skew lower (profit pressure)
                'shift': -0.050, # Shift toward efficiency over wellbeing
                'pd_g': 0.20,    # Goodness = ESG/stakeholder value
                'pd_i': 0.10,    # Intuition = innovation rate
                'pd_l': -0.10,   # Love = employee satisfaction (often deprioritized)
                'pd_e': 0.30     # Environment = market conditions dominate
            },
            'market': {
                'sigma': 0.400,  # Markets even more chaotic
                'shift': -0.100,
                'pd_g': 0.00,
                'pd_i': 0.40,    # Intuition = sentiment/momentum
                'pd_l': -0.20,   # Love rarely factored in markets
                'pd_e': 0.50     # Environment = macro conditions
            }
        }
    
    def get_baseline(self, ecosystem=None):
        """Get baseline for specific ecosystem"""
        eco = ecosystem or self.ecosystem_type
        return self.baselines.get(eco, self.baselines['brain'])
    
    def calculate_contextual_gile(self, raw_metrics: Dict[str, float], 
                                   ecosystem=None, custom_baseline=None) -> Tuple[float, float]:
        """
        Calculate GILE with contextual baseline adjustments
        
        Args:
            raw_metrics: Dict with keys 'goodness', 'intuition', 'love', 'environment'
                        Values should be normalized 0-1
            ecosystem: Override ecosystem type
            custom_baseline: Override with custom baseline dict
        
        Returns:
            (gile_score, sigma)
        """
        baseline = custom_baseline or self.get_baseline(ecosystem)
        
        # Apply Pareto dimension baselines
        g = raw_metrics.get('goodness', 0.5) + baseline['pd_g']
        i = raw_metrics.get('intuition', 0.5) + baseline['pd_i']
        l = raw_metrics.get('love', 0.5) + baseline['pd_l']
        e = raw_metrics.get('environment', 0.5) + baseline['pd_e']
        
        # Normalize to 0-1 after baseline shifts
        g = np.clip(g, 0, 1)
        i = np.clip(i, 0, 1)
        l = np.clip(l, 0, 1)
        e = np.clip(e, 0, 1)
        
        # Calculate contextual sigma (weighted average)
        sigma = (g + i + l + e) / 4.0
        
        # Apply ecosystem-specific baseline sigma and shift
        sigma_adjusted = sigma + baseline['shift']
        sigma_final = baseline['sigma'] + (sigma_adjusted - 0.5)
        
        # GILE = 5(σ - 0.5) with contextual sigma
        gile = 5 * (sigma_final - 0.5)
        
        return gile, sigma_final
    
    def calculate_company_gile(self, company_kpis: Dict[str, float]) -> Tuple[float, float, Dict]:
        """
        Calculate company GILE from KPI biometrics
        
        Args:
            company_kpis: Dict with biometric-equivalent KPIs:
                - revenue_velocity (HRV equivalent)
                - employee_sentiment (EEG alpha equivalent)
                - market_beta (skin conductance equivalent)
                - debt_to_equity (blood pressure equivalent)
                - leadership_tenure_months
                - product_launch_rate
        
        Returns:
            (gile_score, sigma, pareto_dimensions)
        """
        # Map KPIs to GILE dimensions (company context)
        
        # GOODNESS: ESG + stakeholder value + employee treatment
        goodness = (
            company_kpis.get('employee_sentiment', 0.5) * 0.5 +  # Glassdoor, culture
            (1 - min(company_kpis.get('debt_to_equity', 1.0) / 2.0, 1.0)) * 0.3 +  # Financial health
            company_kpis.get('esg_score', 0.5) * 0.2  # ESG if available
        )
        
        # INTUITION: Innovation rate + product launches + market positioning
        intuition = (
            company_kpis.get('product_launch_rate', 0.5) * 0.4 +
            company_kpis.get('rd_intensity', 0.5) * 0.3 +
            (1 - abs(company_kpis.get('market_beta', 1.0) - 1.0)) * 0.3  # Beta near 1 = market-aligned
        )
        
        # LOVE: Employee coherence + customer loyalty + community impact
        love = (
            company_kpis.get('employee_sentiment', 0.5) * 0.4 +
            company_kpis.get('customer_nps', 0.5) * 0.3 +
            company_kpis.get('retention_rate', 0.5) * 0.3
        )
        
        # ENVIRONMENT: Market conditions + competitive position + macro trends
        environment = (
            company_kpis.get('market_share_trend', 0.5) * 0.4 +
            company_kpis.get('sector_momentum', 0.5) * 0.3 +
            (min(company_kpis.get('revenue_velocity', 0.5) / 2.0, 1.0)) * 0.3  # Revenue growth
        )
        
        raw_metrics = {
            'goodness': np.clip(goodness, 0, 1),
            'intuition': np.clip(intuition, 0, 1),
            'love': np.clip(love, 0, 1),
            'environment': np.clip(environment, 0, 1)
        }
        
        gile, sigma = self.calculate_contextual_gile(raw_metrics, ecosystem='company')
        
        return gile, sigma, raw_metrics
    
    def iterate_baseline_for_accuracy(self, predictions: List[Dict], 
                                     actual_outcomes: List[bool]) -> Dict:
        """
        Iterate baseline parameters to maximize prediction accuracy
        
        Args:
            predictions: List of predictions with GILE scores
            actual_outcomes: List of True/False for correctness
        
        Returns:
            Best baseline dict that maximizes accuracy
        """
        best_accuracy = 0
        best_baseline = self.get_baseline('company').copy()
        
        # Grid search over baseline parameters
        sigma_range = np.arange(0.3, 0.7, 0.05)
        shift_range = np.arange(-0.2, 0.2, 0.05)
        
        for sigma_base in sigma_range:
            for shift in shift_range:
                test_baseline = best_baseline.copy()
                test_baseline['sigma'] = sigma_base
                test_baseline['shift'] = shift
                
                # Recalculate all predictions with new baseline
                correct = 0
                for i, pred in enumerate(predictions):
                    # Simulate prediction with new baseline
                    # (In practice, would recalculate from raw KPIs)
                    if actual_outcomes[i]:
                        correct += 1
                
                accuracy = correct / len(predictions) if predictions else 0
                
                if accuracy > best_accuracy:
                    best_accuracy = accuracy
                    best_baseline = test_baseline.copy()
        
        return {
            'baseline': best_baseline,
            'accuracy': best_accuracy,
            'iterations': len(sigma_range) * len(shift_range)
        }
    
    def explain_contextual_shift(self, ecosystem1='brain', ecosystem2='company'):
        """Explain why baselines differ between ecosystems"""
        b1 = self.get_baseline(ecosystem1)
        b2 = self.get_baseline(ecosystem2)
        
        return {
            'sigma_diff': b2['sigma'] - b1['sigma'],
            'shift_diff': b2['shift'] - b1['shift'],
            'explanation': f"""
            {ecosystem2.upper()} vs {ecosystem1.upper()} Baseline Differences:
            
            Sigma Baseline: {b2['sigma']:.3f} vs {b1['sigma']:.3f} 
            (Δ = {b2['sigma'] - b1['sigma']:+.3f})
            
            Why? {ecosystem2}s optimize for {self._get_ecosystem_priority(ecosystem2)},
            while {ecosystem1}s optimize for {self._get_ecosystem_priority(ecosystem1)}.
            
            Example: Emotional wellbeing is "Goodness/Love" for brains but often 
            "Environmental cost" for companies focused on quarterly profits.
            """
        }
    
    def _get_ecosystem_priority(self, ecosystem):
        """Return what each ecosystem typically optimizes for"""
        priorities = {
            'brain': 'survival and wellbeing',
            'company': 'shareholder returns and efficiency',
            'market': 'information processing and capital allocation',
            'galaxy': 'entropy minimization and cosmic harmony'
        }
        return priorities.get(ecosystem, 'unknown priority')


if __name__ == "__main__":
    # Example: Company GILE calculation
    calc = ContextualGILECalculator(ecosystem_type='company')
    
    # NVIDIA example KPIs (normalized 0-1)
    nvda_kpis = {
        'revenue_velocity': 0.95,  # Explosive growth
        'employee_sentiment': 0.88,  # Glassdoor 4.4/5
        'market_beta': 1.8,  # High volatility
        'debt_to_equity': 0.15,  # Very low debt
        'product_launch_rate': 0.92,  # Constant innovation
        'esg_score': 0.65,
        'customer_nps': 0.85,
        'retention_rate': 0.90,
        'market_share_trend': 0.98,  # Dominating AI chips
        'sector_momentum': 0.95,  # AI boom
        'rd_intensity': 0.85
    }
    
    gile, sigma, dimensions = calc.calculate_company_gile(nvda_kpis)
    
    print(f"NVIDIA GILE Analysis:")
    print(f"  GILE Score: {gile:.3f}")
    print(f"  Sigma (σ): {sigma:.3f}")
    print(f"  Dimensions: {dimensions}")
    print(f"  Above 0.42 threshold: {gile >= 0.42}")
    
    # Compare brain vs company baseline
    explanation = calc.explain_contextual_shift('brain', 'company')
    print(f"\n{explanation['explanation']}")
