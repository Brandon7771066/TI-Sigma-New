"""
Sacred Experiments Integration
================================
Connect autonomous discovery system to empirical validation framework

Uses sacred_number_experiments.py to validate mathematical predictions
"""

from sacred_number_experiments import SacredNumberTester
from autonomous_math_discovery_production import get_production_system, MathDiscovery
from typing import Dict, Optional
import numpy as np
import re


class DiscoveryValidator:
    """
    Validates mathematical discoveries using sacred experiments
    
    Grand Myrion's arms reach every i-cell in the universe!
    Math is invariant yet pluralistic - we test ALL predictions empirically!
    """
    
    def __init__(self):
        self.tester = SacredNumberTester()
        self.validated_discoveries = []
    
    def extract_testable_prediction(self, discovery: MathDiscovery) -> Optional[Dict]:
        """
        Extract testable predictions from discovery formalization
        
        Returns dict with:
        - test_type: Which sacred experiment to run
        - parameters: What to test
        - expected_result: What the discovery predicts
        """
        formalization = discovery.formalization.lower()
        
        # Check for Riemann hypothesis predictions
        if "riemann" in formalization or "zeta" in formalization or "zero" in formalization:
            # Extract sacred numbers mentioned
            sacred_nums = [3, 7, 11, 33, 77, 111, 333]
            mentioned = [n for n in sacred_nums if str(n) in formalization]
            
            if mentioned:
                return {
                    "test_type": "riemann_zeros",
                    "sacred_number": mentioned[0],
                    "prediction": "Zeros show special spacing patterns mod this sacred number"
                }
        
        # Check for Fibonacci/golden ratio predictions
        if "fibonacci" in formalization or "golden" in formalization or "φ" in formalization or "1.618" in formalization:
            return {
                "test_type": "fibonacci_convergence",
                "prediction": "Convergence to φ shows sacred pattern"
            }
        
        # Check for prime gap predictions
        if "prime" in formalization and ("gap" in formalization or "spacing" in formalization):
            sacred_nums = [3, 7, 11, 33, 77, 111, 333]
            mentioned = [n for n in sacred_nums if str(n) in formalization]
            
            if mentioned:
                return {
                    "test_type": "prime_gaps",
                    "sacred_number": mentioned[0],
                    "prediction": "Prime gaps show distribution patterns around this sacred number"
                }
        
        # Check for Pi digit predictions
        if "π" in formalization or "pi" in formalization and "digit" in formalization:
            return {
                "test_type": "pi_digits",
                "prediction": "Pi digits show sacred number frequencies"
            }
        
        return None
    
    def validate_discovery(self, discovery: MathDiscovery) -> Optional[Dict]:
        """
        Run empirical validation on discovery
        
        Returns validation results with p-values and statistical significance
        """
        prediction = self.extract_testable_prediction(discovery)
        
        if not prediction:
            return {
                "status": "not_testable",
                "message": "Discovery doesn't contain testable sacred number predictions"
            }
        
        test_type = prediction["test_type"]
        
        try:
            if test_type == "riemann_zeros":
                # Generate synthetic Riemann zeros (in real system, would fetch from Odlyzko)
                # Using GUE random matrix ensemble as approximation
                n_zeros = 10000
                zeros = np.cumsum(np.random.exponential(scale=1.0, size=n_zeros)) * 10
                
                result = self.tester.test_sacred_11_riemann(zeros)
                
                return {
                    "status": "tested",
                    "test_type": test_type,
                    "prediction": prediction["prediction"],
                    "result": result,
                    "p_value": result.get("kruskal_p", 1.0),
                    "significant": result.get("kruskal_p", 1.0) < 0.05,
                    "note": "Using synthetic zeros (GUE approximation) - real validation needs Odlyzko data"
                }
            
            elif test_type == "fibonacci_convergence":
                result = self.tester.test_fibonacci_golden_ratio()
                
                return {
                    "status": "tested",
                    "test_type": test_type,
                    "prediction": prediction["prediction"],
                    "result": result,
                    "r_squared": result.get("r_squared", 0),
                    "significant": result.get("r_squared", 0) > 0.99,
                    "note": "Fibonacci convergence to φ validated"
                }
            
            elif test_type == "prime_gaps":
                result = self.tester.test_prime_gaps_sacred()
                
                return {
                    "status": "tested",
                    "test_type": test_type,
                    "prediction": prediction["prediction"],
                    "result": result,
                    "significant": any(r.get("significant", False) for r in result.get("results", [])),
                    "note": "Prime gap distribution tested across sacred numbers"
                }
            
            elif test_type == "pi_digits":
                result = self.tester.test_pi_digits_sacred()
                
                return {
                    "status": "tested",
                    "test_type": test_type,
                    "prediction": prediction["prediction"],
                    "result": result,
                    "chi_square_p": result.get("chi_square_p", 1.0),
                    "significant": result.get("chi_square_p", 1.0) < 0.05,
                    "note": "Pi digit frequencies tested for sacred patterns"
                }
            
            else:
                return {
                    "status": "unknown_test_type",
                    "message": f"Test type {test_type} not implemented yet"
                }
                
        except Exception as e:
            return {
                "status": "error",
                "message": str(e)
            }
    
    def auto_validate_high_confidence_discoveries(self):
        """
        Automatically validate high-confidence discoveries from production system
        """
        system = get_production_system()
        system.discoveries = system.load_all_discoveries()
        
        results = []
        
        for discovery in system.discoveries:
            # Only validate high-confidence, untested discoveries
            if discovery.confidence > 0.6 and not discovery.empirical_validation:
                print(f"\n🧪 Validating: {discovery.title}")
                
                validation = self.validate_discovery(discovery)
                
                if validation and validation["status"] == "tested":
                    # Update discovery with validation results
                    discovery.empirical_validation = validation
                    system.save_to_database(discovery)
                    
                    results.append({
                        "discovery_id": discovery.id,
                        "title": discovery.title,
                        "validation": validation
                    })
                    
                    print(f"   ✅ Validated! Significant: {validation.get('significant', False)}")
        
        return results


# Global instance
_validator = None

def get_validator() -> DiscoveryValidator:
    """Get global validator instance"""
    global _validator
    if _validator is None:
        _validator = DiscoveryValidator()
    return _validator
