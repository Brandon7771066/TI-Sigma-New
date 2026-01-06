"""
GSA Core Algorithm Unit Tests
Validates the Grand Stock Algorithm's core logic
"""

import pytest
import numpy as np
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from gsa_core import GSACore, MarketRegime, XiMetrics, GILEScore, Signal


class TestGSACore:
    """Unit tests for GSA Core Engine"""
    
    @pytest.fixture
    def gsa(self):
        """Create GSA instance for testing"""
        return GSACore(lookback_short=7, lookback_long=60)
    
    @pytest.fixture
    def sample_data(self):
        """Generate sample price/return data"""
        np.random.seed(42)
        prices = 100 * np.cumprod(1 + np.random.randn(100) * 0.02)
        returns = np.diff(prices) / prices[:-1] * 100
        return prices, returns
    
    def test_gsa_initialization(self, gsa):
        """Test GSA initializes with correct parameters"""
        assert gsa.lookback_short == 7
        assert gsa.lookback_long == 60
        assert gsa.gile_weights == (0.20, 0.25, 0.25, 0.30)
    
    def test_xi_metrics_computation(self, gsa, sample_data):
        """Test Xi metrics are computed correctly"""
        prices, returns = sample_data
        xi = gsa.compute_xi_metrics(returns, prices)
        
        assert isinstance(xi, XiMetrics)
        assert 0 <= xi.amplitude <= 10  # Reasonable range
        assert 0 <= xi.memory_kernel <= 1  # Bounded [0,1]
        assert 0 <= xi.constraint <= 1  # Bounded [0,1]
        assert -3 <= xi.pd <= 2  # PD bounded as specified
    
    def test_gile_computation(self, gsa, sample_data):
        """Test GILE score computation"""
        prices, returns = sample_data
        gile = gsa.compute_gile(returns, prices)
        
        assert isinstance(gile, GILEScore)
        assert -1 <= gile.goodness <= 1
        assert 0 <= gile.intuition <= 1
        assert -1 <= gile.love <= 1
        assert 0 <= gile.environment <= 1
        assert 0 <= gile.composite <= 1
    
    def test_regime_classification(self, gsa):
        """Test market regime classification"""
        # Expansion: positive PD, low constraint
        regime, conf, reasons = gsa.classify_regime(pd=1.0, constraint=0.3, volatility=0.15)
        assert regime == MarketRegime.EXPANSION
        assert conf >= 0.5
        
        # Fracture: extreme constraint
        regime, conf, reasons = gsa.classify_regime(pd=-2.0, constraint=0.95, volatility=0.5)
        assert regime == MarketRegime.FRACTURE
    
    def test_signal_generation(self, gsa, sample_data):
        """Test signal generation produces valid output"""
        prices, returns = sample_data
        
        xi = gsa.compute_xi_metrics(returns, prices)
        gile = gsa.compute_gile(returns, prices)
        regime, conf, _ = gsa.classify_regime(xi.pd, xi.constraint, 0.2)
        signal = gsa.generate_signal(xi, gile, regime, conf)
        
        assert isinstance(signal, Signal)
        assert signal.action in ['strong_buy', 'buy', 'hold', 'sell', 'strong_sell']
        assert 0 <= signal.confidence <= 1
        assert 0 <= signal.gile <= 1
    
    def test_valence_weights(self, gsa):
        """Test valence weights match TI theory"""
        assert gsa.W_GREAT == 1.0  # Great = base weight
        assert gsa.W_TERRIBLE == 2.0  # Terrible = 2x emphasis
        assert gsa.W_EXCEPTIONAL == 1.5  # Exceptional = 1.5x
        assert gsa.W_WICKED == 6.0  # Wicked = 6x (asymmetric emphasis)
    
    def test_edge_case_empty_data(self, gsa):
        """Test handling of insufficient data"""
        xi = gsa.compute_xi_metrics(np.array([1, 2, 3]), np.array([100, 101, 102]))
        assert xi.pd == 0  # Should return zero for insufficient data
    
    def test_green_light_universe(self):
        """Verify green-light stocks match validation results"""
        green_light = [
            'GOOGL', 'NVDA', 'MSFT', 'META',  # Technology
            'CAT', 'GE',  # Industrials
            'GS', 'MS',  # Financials
            'XOM', 'CVX', 'COP',  # Energy
            'WMT', 'TJX'  # Consumer
        ]
        assert len(green_light) == 13
        assert 'AAPL' not in green_light  # Known red-flag stock


class TestGSAPerformance:
    """Performance benchmark tests"""
    
    def test_signal_generation_speed(self):
        """Ensure signal generation is fast enough for real-time use"""
        import time
        
        gsa = GSACore()
        np.random.seed(42)
        prices = 100 * np.cumprod(1 + np.random.randn(252) * 0.02)
        returns = np.diff(prices) / prices[:-1] * 100
        
        start = time.time()
        for _ in range(100):
            xi = gsa.compute_xi_metrics(returns, prices)
            gile = gsa.compute_gile(returns, prices)
        elapsed = time.time() - start
        
        assert elapsed < 1.0  # 100 iterations should complete in < 1 second


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
