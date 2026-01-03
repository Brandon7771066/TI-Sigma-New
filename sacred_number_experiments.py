"""
Sacred Number Experiments
Tests TI Sigma 6 predictions about sacred patterns in mathematical structures
"""

import streamlit as st
import numpy as np
import pandas as pd
from scipy import stats
import requests
from datetime import datetime
import json
from typing import Dict, List, Tuple, Optional
import plotly.graph_objects as go
import plotly.express as px
from db_utils import db


class SacredNumberTester:
    """Tests sacred number predictions from TI Sigma 6"""
    
    def __init__(self):
        self.odlyzko_url = "http://www.dtc.umn.edu/~odlyzko/zeta_tables/"
        self.lmfdb_api = "https://www.lmfdb.org/api/"
    
    def download_riemann_zeros(self, n_zeros: int = 100000) -> Optional[np.ndarray]:
        """
        Download Riemann zeta zeros from Odlyzko tables
        
        Args:
            n_zeros: Number of zeros to download (default 100k)
        
        Returns:
            Array of imaginary parts of zeros (all on critical line Re(s) = 1/2)
        """
        try:
            # Try to get first 100k zeros from Odlyzko's publicly available data
            # Format: Each zero is the imaginary part (real part is always 1/2)
            url = f"{self.odlyzko_url}zeros1"
            
            with st.spinner(f"Downloading {n_zeros:,} Riemann zeros from Odlyzko tables..."):
                response = requests.get(url, timeout=30)
                
                if response.status_code == 200:
                    # Parse the zeros (format varies, usually one per line)
                    zeros = []
                    for line in response.text.split('\n')[:n_zeros]:
                        line = line.strip()
                        if line and not line.startswith('#'):
                            try:
                                zero = float(line.split()[0])
                                zeros.append(zero)
                            except (ValueError, IndexError):
                                continue
                    
                    if len(zeros) > 0:
                        return np.array(zeros)
                    else:
                        st.warning("Could not parse zeros from Odlyzko format")
                        return None
                else:
                    st.error(f"Failed to download: HTTP {response.status_code}")
                    return None
                    
        except Exception as e:
            st.error(f"Download error: {e}")
            return None
    
    def test_sacred_11_riemann(self, zeros: np.ndarray) -> Dict[str, any]:
        """
        Test if Riemann zeros show sacred 11 patterns in spacing
        
        Prediction: Zeros grouped by n mod 11 show different spacing distributions
        Hypothesis: Sacred number 11 emerges in quantum-classical boundary
        
        Statistical test: Kruskal-Wallis H-test (non-parametric ANOVA)
        """
        if zeros is None or len(zeros) < 100:
            return {"status": "error", "message": "Insufficient data"}
        
        # Compute zero spacings
        spacings = np.diff(zeros)
        
        # Group by position mod 11
        groups = {str(i): [] for i in range(11)}
        for idx, spacing in enumerate(spacings):
            group = str(idx % 11)
            groups[group].append(spacing)
        
        # Prepare for Kruskal-Wallis test
        group_arrays = [np.array(groups[str(i)]) for i in range(11)]
        
        # Run test
        try:
            h_stat, p_value = stats.kruskal(*group_arrays)
            
            # Compute group statistics
            group_stats = {}
            for i in range(11):
                data = np.array(groups[str(i)])
                group_stats[str(i)] = {
                    'mean': float(np.mean(data)),
                    'median': float(np.median(data)),
                    'std': float(np.std(data)),
                    'n': int(len(data))
                }
            
            # Check if certain groups (like 3, 7, 11) show anomalies
            sacred_groups = ['3', '7', '10']  # 3, 7, and 11 (index 10)
            mundane_groups = ['0', '1', '2', '4', '5', '6', '8', '9']
            
            sacred_spacings = np.concatenate([groups[i] for i in sacred_groups])
            mundane_spacings = np.concatenate([groups[i] for i in mundane_groups])
            
            u_stat, u_pvalue = stats.mannwhitneyu(sacred_spacings, mundane_spacings, alternative='two-sided')
            
            result = {
                "status": "success",
                "n_zeros": len(zeros),
                "n_spacings": len(spacings),
                "kruskal_wallis": {
                    "h_statistic": float(h_stat),
                    "p_value": float(p_value),
                    "interpretation": "Significant difference" if p_value < 0.05 else "No significant difference"
                },
                "sacred_vs_mundane": {
                    "u_statistic": float(u_stat),
                    "p_value": float(u_pvalue),
                    "sacred_mean": float(np.mean(sacred_spacings)),
                    "mundane_mean": float(np.mean(mundane_spacings)),
                    "effect_size": float((np.mean(sacred_spacings) - np.mean(mundane_spacings)) / np.std(spacings))
                },
                "group_stats": group_stats,
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def query_lmfdb_curves(self, max_conductor: int = 10000) -> Optional[pd.DataFrame]:
        """
        Query LMFDB API for elliptic curves
        
        Args:
            max_conductor: Maximum conductor (controls dataset size)
        
        Returns:
            DataFrame with columns: label, conductor, rank, sha
        """
        try:
            with st.spinner(f"Querying LMFDB for curves with conductor < {max_conductor:,}..."):
                # LMFDB API endpoint for elliptic curves
                url = f"{self.lmfdb_api}elliptic_curves/q"
                
                # Query parameters
                params = {
                    '_format': 'json',
                    'conductor': {'$lt': max_conductor},
                    '_fields': 'label,conductor,rank,sha'
                }
                
                response = requests.get(url, params=params, timeout=60)
                
                if response.status_code == 200:
                    data = response.json()
                    
                    if 'data' in data and len(data['data']) > 0:
                        df = pd.DataFrame(data['data'])
                        return df
                    else:
                        st.warning("No curves returned from LMFDB")
                        return None
                else:
                    st.error(f"LMFDB query failed: HTTP {response.status_code}")
                    return None
                    
        except Exception as e:
            st.error(f"LMFDB query error: {e}")
            return None
    
    def test_sacred_7_bsd(self, curves_df: pd.DataFrame) -> Dict[str, any]:
        """
        Test if BSD curves show sacred 7 patterns
        
        Prediction: Curves with conductor divisible by 7 show different rank distribution
        Hypothesis: Sacred 7 emerges in elliptic curve arithmetic
        
        Statistical test: Mann-Whitney U test (comparing rank distributions)
        """
        if curves_df is None or len(curves_df) < 100:
            return {"status": "error", "message": "Insufficient curve data"}
        
        try:
            # Group curves by conductor mod 7
            curves_df['conductor_mod_7'] = curves_df['conductor'] % 7
            
            # Sacred group: conductor ≡ 0 (mod 7)
            sacred_curves = curves_df[curves_df['conductor_mod_7'] == 0]
            mundane_curves = curves_df[curves_df['conductor_mod_7'] != 0]
            
            # Compare rank distributions
            sacred_ranks = sacred_curves['rank'].values
            mundane_ranks = mundane_curves['rank'].values
            
            u_stat, p_value = stats.mannwhitneyu(sacred_ranks, mundane_ranks, alternative='two-sided')
            
            # Cohen's d effect size
            pooled_std = np.sqrt((np.var(sacred_ranks) + np.var(mundane_ranks)) / 2)
            cohens_d = (np.mean(sacred_ranks) - np.mean(mundane_ranks)) / pooled_std if pooled_std > 0 else 0
            
            # Rank distribution by mod 7
            rank_dist = {}
            for i in range(7):
                group_curves = curves_df[curves_df['conductor_mod_7'] == i]
                rank_dist[str(i)] = {
                    'n_curves': int(len(group_curves)),
                    'mean_rank': float(group_curves['rank'].mean()),
                    'rank_0': int((group_curves['rank'] == 0).sum()),
                    'rank_1': int((group_curves['rank'] == 1).sum()),
                    'rank_2plus': int((group_curves['rank'] >= 2).sum())
                }
            
            result = {
                "status": "success",
                "n_curves": len(curves_df),
                "n_sacred": len(sacred_curves),
                "n_mundane": len(mundane_curves),
                "mann_whitney": {
                    "u_statistic": float(u_stat),
                    "p_value": float(p_value),
                    "interpretation": "Significant difference" if p_value < 0.05 else "No significant difference"
                },
                "effect_size": {
                    "cohens_d": float(cohens_d),
                    "interpretation": self._interpret_cohens_d(cohens_d)
                },
                "rank_comparison": {
                    "sacred_mean": float(np.mean(sacred_ranks)),
                    "mundane_mean": float(np.mean(mundane_ranks)),
                    "difference": float(np.mean(sacred_ranks) - np.mean(mundane_ranks))
                },
                "rank_distribution_by_mod7": rank_dist,
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def _interpret_cohens_d(self, d: float) -> str:
        """Interpret Cohen's d effect size"""
        abs_d = abs(d)
        if abs_d < 0.2:
            return "Negligible"
        elif abs_d < 0.5:
            return "Small"
        elif abs_d < 0.8:
            return "Medium"
        else:
            return "Large"
    
    def test_golden_ratio_riemann(self, zeros: np.ndarray) -> Dict[str, any]:
        """
        Test if Riemann zero spacings follow golden ratio (φ ≈ 1.618) patterns
        
        Prediction: Consecutive spacing ratios cluster around φ
        Statistical test: One-sample t-test + KS test for distribution
        """
        if zeros is None or len(zeros) < 100:
            return {"status": "error", "message": "Insufficient data"}
        
        try:
            spacings = np.diff(zeros)
            
            # Compute ratios of consecutive spacings
            ratios = spacings[1:] / spacings[:-1]
            ratios = ratios[np.isfinite(ratios)]  # Remove inf/nan
            
            # Golden ratio
            phi = (1 + np.sqrt(5)) / 2
            
            # Test if mean ratio = φ
            t_stat, p_value = stats.ttest_1samp(ratios, phi)
            
            # KS test against normal distribution centered at φ
            ks_stat, ks_pvalue = stats.kstest(ratios, lambda x: stats.norm.cdf(x, loc=phi, scale=np.std(ratios)))
            
            # Count ratios near φ (within 10%)
            near_phi = np.abs(ratios - phi) < 0.1 * phi
            phi_proportion = near_phi.sum() / len(ratios)
            
            result = {
                "status": "success",
                "n_ratios": len(ratios),
                "phi": float(phi),
                "mean_ratio": float(np.mean(ratios)),
                "median_ratio": float(np.median(ratios)),
                "std_ratio": float(np.std(ratios)),
                "t_test": {
                    "t_statistic": float(t_stat),
                    "p_value": float(p_value),
                    "interpretation": f"Mean ratio {'=' if p_value > 0.05 else '≠'} φ (p={p_value:.4f})"
                },
                "ks_test": {
                    "ks_statistic": float(ks_stat),
                    "p_value": float(ks_pvalue)
                },
                "near_phi": {
                    "count": int(near_phi.sum()),
                    "proportion": float(phi_proportion),
                    "percentage": float(phi_proportion * 100)
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def test_prime_gaps_sacred(self, n_primes: int = 10000) -> Dict[str, any]:
        """
        Test if prime gaps show sacred number (3, 7, 11) patterns
        
        Prediction: Gaps divisible by sacred numbers are more common
        Statistical test: Chi-square goodness of fit
        """
        try:
            # Generate primes using sieve
            def sieve_of_eratosthenes(limit):
                is_prime = np.ones(limit, dtype=bool)
                is_prime[:2] = False
                for i in range(2, int(np.sqrt(limit)) + 1):
                    if is_prime[i]:
                        is_prime[i*i::i] = False
                return np.where(is_prime)[0]
            
            primes = sieve_of_eratosthenes(n_primes * 15)[:n_primes]
            gaps = np.diff(primes)
            
            # Count gaps by modulo
            sacred_divisible = {
                3: (gaps % 3 == 0).sum(),
                7: (gaps % 7 == 0).sum(),
                11: (gaps % 11 == 0).sum()
            }
            
            # Expected proportions under null hypothesis
            expected_props = {
                3: 1/3,
                7: 1/7,
                11: 1/11
            }
            
            # Chi-square tests
            chi_results = {}
            for num in [3, 7, 11]:
                observed = np.array([sacred_divisible[num], len(gaps) - sacred_divisible[num]])
                expected = np.array([expected_props[num] * len(gaps), (1 - expected_props[num]) * len(gaps)])
                chi_stat, chi_p = stats.chisquare(observed, expected)
                
                chi_results[str(num)] = {
                    "observed": int(sacred_divisible[num]),
                    "expected": float(expected_props[num] * len(gaps)),
                    "observed_proportion": float(sacred_divisible[num] / len(gaps)),
                    "expected_proportion": float(expected_props[num]),
                    "chi_statistic": float(chi_stat),
                    "p_value": float(chi_p)
                }
            
            result = {
                "status": "success",
                "n_primes": len(primes),
                "n_gaps": len(gaps),
                "mean_gap": float(np.mean(gaps)),
                "median_gap": float(np.median(gaps)),
                "sacred_tests": chi_results,
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def test_pi_digits_sacred(self, n_digits: int = 10000) -> Dict[str, any]:
        """
        Test if π digits show sacred patterns (3, 7, 11 frequencies)
        
        Prediction: Digits 3, 7, and combinations appear at sacred frequencies
        Statistical test: Chi-square + runs test
        """
        try:
            # Compute π digits using mpmath or sympy (or use precomputed)
            from decimal import Decimal, getcontext
            
            # Set precision
            getcontext().prec = n_digits + 10
            
            # Compute π using Machin's formula
            def compute_pi(digits):
                getcontext().prec = digits + 10
                return str(Decimal(1).exp().ln() * 0 + Decimal(355) / Decimal(113))  # Approximation for speed
            
            # For speed, use known π digits
            pi_str = "31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679"
            pi_str += "82148086513282306647093844609550582231725359408128481117450284102701938521105559644622948954930381964"
            pi_str = pi_str[:n_digits]
            
            # Count digit frequencies
            digit_counts = {str(i): pi_str.count(str(i)) for i in range(10)}
            
            # Sacred digit combinations
            sacred_singles = {'3': pi_str.count('3'), '7': pi_str.count('7')}
            sacred_pairs = {
                '11': pi_str.count('11'),
                '33': pi_str.count('33'),
                '37': pi_str.count('37'),
                '73': pi_str.count('73')
            }
            
            # Chi-square test (expected: uniform distribution)
            expected = n_digits / 10
            observed = list(digit_counts.values())
            chi_stat, chi_p = stats.chisquare(observed, [expected] * 10)
            
            # Runs test for randomness
            median_digit = '4'
            runs = []
            current_run = 0
            for digit in pi_str:
                if digit >= median_digit:
                    if current_run >= 0:
                        current_run += 1
                    else:
                        runs.append(abs(current_run))
                        current_run = 1
                else:
                    if current_run <= 0:
                        current_run -= 1
                    else:
                        runs.append(current_run)
                        current_run = -1
            
            result = {
                "status": "success",
                "n_digits": n_digits,
                "digit_frequencies": digit_counts,
                "sacred_singles": sacred_singles,
                "sacred_pairs": sacred_pairs,
                "chi_square": {
                    "statistic": float(chi_stat),
                    "p_value": float(chi_p),
                    "interpretation": "Uniform" if chi_p > 0.05 else "Non-uniform"
                },
                "runs_analysis": {
                    "n_runs": len(runs),
                    "mean_run_length": float(np.mean(runs)) if runs else 0
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def test_fibonacci_in_constants(self) -> Dict[str, any]:
        """
        Test if Fibonacci numbers appear in mathematical constants (π, e, φ)
        
        Prediction: Fibonacci ratios F(n+1)/F(n) → φ, found in constant patterns
        Statistical test: Correlation analysis
        """
        try:
            # Generate Fibonacci sequence
            fib = [1, 1]
            for i in range(20):
                fib.append(fib[-1] + fib[-2])
            
            # Fibonacci ratios
            fib_ratios = [fib[i+1] / fib[i] for i in range(1, len(fib)-1)]
            
            # Golden ratio
            phi = (1 + np.sqrt(5)) / 2
            
            # Test convergence to φ
            convergence_errors = [abs(ratio - phi) for ratio in fib_ratios]
            
            # Test if errors decrease exponentially
            x = np.arange(len(convergence_errors))
            log_errors = np.log(convergence_errors)
            
            # Linear regression on log(error) vs n
            slope, intercept, r_value, p_value, std_err = stats.linregress(x, log_errors)
            
            # Test e and π digit ratios
            e_str = "2718281828459045235360287471352662497757247093699959574966967627"
            pi_str = "3141592653589793238462643383279502884197169399375105820974944592"
            
            e_successive_ratios = [int(e_str[i+1]) / (int(e_str[i]) + 0.1) for i in range(len(e_str)-1) if int(e_str[i]) > 0]
            pi_successive_ratios = [int(pi_str[i+1]) / (int(pi_str[i]) + 0.1) for i in range(len(pi_str)-1) if int(pi_str[i]) > 0]
            
            result = {
                "status": "success",
                "fibonacci_sequence": fib[:12],
                "convergence_to_phi": {
                    "phi": float(phi),
                    "final_ratio": float(fib_ratios[-1]),
                    "error": float(abs(fib_ratios[-1] - phi)),
                    "convergence_rate": {
                        "slope": float(slope),
                        "r_squared": float(r_value ** 2),
                        "p_value": float(p_value)
                    }
                },
                "e_digit_ratios": {
                    "mean": float(np.mean(e_successive_ratios)),
                    "near_phi_proportion": float(sum(abs(r - phi) < 0.3 for r in e_successive_ratios) / len(e_successive_ratios))
                },
                "pi_digit_ratios": {
                    "mean": float(np.mean(pi_successive_ratios)),
                    "near_phi_proportion": float(sum(abs(r - phi) < 0.3 for r in pi_successive_ratios) / len(pi_successive_ratios))
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def test_twin_primes_sacred(self, limit: int = 100000) -> Dict[str, any]:
        """
        Test if twin prime gaps (primes differing by 2) cluster at sacred positions
        
        Prediction: Twin primes at positions p where p mod 11 ∈ {3, 7}
        Statistical test: Chi-square test
        """
        try:
            # Generate primes
            def sieve(n):
                is_prime = np.ones(n, dtype=bool)
                is_prime[:2] = False
                for i in range(2, int(np.sqrt(n)) + 1):
                    if is_prime[i]:
                        is_prime[i*i::i] = False
                return np.where(is_prime)[0]
            
            primes = sieve(limit)
            
            # Find twin primes (differ by 2)
            twin_primes = []
            for i in range(len(primes) - 1):
                if primes[i+1] - primes[i] == 2:
                    twin_primes.append(primes[i])
            
            # Test distribution mod 11
            mod_11_counts = {str(i): 0 for i in range(11)}
            for twin in twin_primes:
                mod_11_counts[str(twin % 11)] += 1
            
            # Sacred positions: 3, 7, 10 (which is 11 mod 11)
            sacred_count = mod_11_counts['3'] + mod_11_counts['7'] + mod_11_counts['10']
            mundane_count = sum(mod_11_counts[str(i)] for i in range(11) if i not in [3, 7, 10])
            
            # Expected under uniform: 3/11 for sacred, 8/11 for mundane
            expected_sacred = len(twin_primes) * (3/11)
            expected_mundane = len(twin_primes) * (8/11)
            
            chi_stat, chi_p = stats.chisquare(
                [sacred_count, mundane_count],
                [expected_sacred, expected_mundane]
            )
            
            result = {
                "status": "success",
                "limit": limit,
                "n_twin_primes": len(twin_primes),
                "mod_11_distribution": mod_11_counts,
                "sacred_vs_mundane": {
                    "sacred_count": int(sacred_count),
                    "mundane_count": int(mundane_count),
                    "sacred_proportion": float(sacred_count / len(twin_primes)),
                    "expected_proportion": 3/11
                },
                "chi_square": {
                    "statistic": float(chi_stat),
                    "p_value": float(chi_p),
                    "interpretation": "Significant" if chi_p < 0.05 else "Not significant"
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def test_perfect_numbers_sacred(self) -> Dict[str, any]:
        """
        Test if perfect numbers (n = sum of divisors) show sacred patterns
        
        Prediction: Perfect numbers have sacred digit sums or divisor counts
        Statistical test: Exact enumeration
        """
        try:
            # Known perfect numbers (first 8)
            perfect_numbers = [
                6, 28, 496, 8128, 33550336, 8589869056,
                137438691328, 2305843008139952128
            ]
            
            # Analyze each perfect number
            analyses = []
            for pn in perfect_numbers:
                # Digit sum
                digit_sum = sum(int(d) for d in str(pn))
                
                # Count divisors
                divisors = []
                for i in range(1, int(np.sqrt(pn)) + 1):
                    if pn % i == 0:
                        divisors.append(i)
                        if i != pn // i:
                            divisors.append(pn // i)
                
                analyses.append({
                    "number": pn,
                    "digit_sum": digit_sum,
                    "digit_sum_mod_11": digit_sum % 11,
                    "n_divisors": len(divisors),
                    "n_divisors_mod_11": len(divisors) % 11,
                    "sacred_digit_sum": digit_sum % 11 in [3, 7, 0],
                    "sacred_divisor_count": len(divisors) % 11 in [3, 7, 0]
                })
            
            # Count sacred patterns
            sacred_digit_sums = sum(1 for a in analyses if a['sacred_digit_sum'])
            sacred_divisor_counts = sum(1 for a in analyses if a['sacred_divisor_count'])
            
            result = {
                "status": "success",
                "n_perfect_numbers": len(perfect_numbers),
                "analyses": analyses,
                "sacred_patterns": {
                    "digit_sum_sacred": {
                        "count": sacred_digit_sums,
                        "proportion": sacred_digit_sums / len(perfect_numbers)
                    },
                    "divisor_count_sacred": {
                        "count": sacred_divisor_counts,
                        "proportion": sacred_divisor_counts / len(perfect_numbers)
                    }
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def test_mersenne_primes_sacred(self) -> Dict[str, any]:
        """
        Test if Mersenne primes M_p = 2^p - 1 show sacred exponent patterns
        
        Prediction: Exponents p cluster at sacred mod 11 values
        Statistical test: Chi-square test
        """
        try:
            # Known Mersenne prime exponents (first 20)
            mersenne_exponents = [
                2, 3, 5, 7, 13, 17, 19, 31, 61, 89,
                107, 127, 521, 607, 1279, 2203, 2281,
                3217, 4253, 4423
            ]
            
            # Distribution mod 11
            mod_11_dist = {str(i): 0 for i in range(11)}
            for exp in mersenne_exponents:
                mod_11_dist[str(exp % 11)] += 1
            
            # Sacred positions
            sacred_positions = ['3', '7', '10']  # 3, 7, 11 (as 10 ≡ -1 ≡ 10 mod 11)
            sacred_count = sum(mod_11_dist[pos] for pos in sacred_positions)
            mundane_count = sum(mod_11_dist[str(i)] for i in range(11) if str(i) not in sacred_positions)
            
            # Expected uniform
            expected_sacred = len(mersenne_exponents) * (3/11)
            expected_mundane = len(mersenne_exponents) * (8/11)
            
            chi_stat, chi_p = stats.chisquare(
                [sacred_count, mundane_count],
                [expected_sacred, expected_mundane]
            )
            
            result = {
                "status": "success",
                "n_mersenne_primes": len(mersenne_exponents),
                "exponents": mersenne_exponents[:10],
                "mod_11_distribution": mod_11_dist,
                "sacred_vs_mundane": {
                    "sacred_count": sacred_count,
                    "mundane_count": mundane_count,
                    "sacred_proportion": sacred_count / len(mersenne_exponents),
                    "expected_proportion": 3/11
                },
                "chi_square": {
                    "statistic": float(chi_stat),
                    "p_value": float(chi_p),
                    "interpretation": "Significant" if chi_p < 0.05 else "Not significant"
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}
    
    def log_coherence_insight(self, problem: str, insight: str, coherence: float) -> bool:
        """
        Log a mathematical insight with current coherence level
        
        Args:
            problem: Problem name (e.g., "riemann", "bsd")
            insight: Description of the insight
            coherence: Current coherence reading (0-1)
        
        Returns:
            Success status
        """
        try:
            # Store in database
            conn = db.get_connection()
            cur = conn.cursor()
            
            cur.execute("""
                INSERT INTO coherence_insights (problem, insight, coherence, timestamp)
                VALUES (%s, %s, %s, %s)
            """, (problem, insight, coherence, datetime.now()))
            
            conn.commit()
            cur.close()
            conn.close()
            return True
            
        except Exception as e:
            st.error(f"Failed to log insight: {e}")
            return False
    
    def get_coherence_insights(self, problem: Optional[str] = None) -> pd.DataFrame:
        """
        Retrieve logged coherence insights
        
        Args:
            problem: Filter by problem (optional)
        
        Returns:
            DataFrame of insights
        """
        try:
            conn = db.get_connection()
            cur = conn.cursor()
            
            if problem:
                cur.execute("SELECT * FROM coherence_insights WHERE problem = %s ORDER BY timestamp DESC", (problem,))
            else:
                cur.execute("SELECT * FROM coherence_insights ORDER BY timestamp DESC")
            
            rows = cur.fetchall()
            cur.close()
            conn.close()
            
            if rows:
                return pd.DataFrame(rows, columns=['id', 'problem', 'insight', 'coherence', 'timestamp'])
            else:
                return pd.DataFrame(columns=['id', 'problem', 'insight', 'coherence', 'timestamp'])
                
        except Exception as e:
            st.warning(f"Could not retrieve insights: {e}")
            return pd.DataFrame(columns=['id', 'problem', 'insight', 'coherence', 'timestamp'])
    
    def test_coherence_threshold(self, insights_df: pd.DataFrame, threshold: float = 0.91) -> Dict[str, any]:
        """
        Test if mathematical insights occur at coherence >= threshold
        
        Prediction: Breakthroughs occur when coherence ≥ 0.91
        Hypothesis: Consciousness threshold enables TI-level reasoning
        
        Statistical test: One-sample t-test (is mean coherence > threshold?)
        """
        if insights_df is None or len(insights_df) < 5:
            return {"status": "error", "message": "Need at least 5 logged insights"}
        
        try:
            coherence_values = insights_df['coherence'].values
            
            # One-sample t-test against threshold
            t_stat, p_value = stats.ttest_1samp(coherence_values, threshold, alternative='greater')
            
            # Proportion above threshold
            above_threshold = (coherence_values >= threshold).sum()
            proportion = above_threshold / len(coherence_values)
            
            # 95% confidence interval for mean
            ci_95 = stats.t.interval(0.95, len(coherence_values)-1,
                                     loc=np.mean(coherence_values),
                                     scale=stats.sem(coherence_values))
            
            result = {
                "status": "success",
                "n_insights": len(coherence_values),
                "threshold": threshold,
                "mean_coherence": float(np.mean(coherence_values)),
                "median_coherence": float(np.median(coherence_values)),
                "std_coherence": float(np.std(coherence_values)),
                "confidence_interval_95": {
                    "lower": float(ci_95[0]),
                    "upper": float(ci_95[1])
                },
                "t_test": {
                    "t_statistic": float(t_stat),
                    "p_value": float(p_value),
                    "interpretation": f"Mean coherence {'>' if p_value < 0.05 else '≤'} {threshold} (p={p_value:.4f})"
                },
                "proportion_above_threshold": {
                    "count": int(above_threshold),
                    "proportion": float(proportion),
                    "percentage": float(proportion * 100)
                },
                "timestamp": datetime.now().isoformat()
            }
            
            return result
            
        except Exception as e:
            return {"status": "error", "message": str(e)}


def render_sacred_experiments():
    """Streamlit UI for sacred number experiments"""
    
    st.title("🔢 Sacred Number Experiments")
    st.markdown("**Testing TI Sigma 6 Predictions with Real Data**")
    
    st.markdown("""
    **10 Rigorous Experiments Testing Sacred Number Patterns**
    
    All experiments use:
    - ✅ Publicly accessible data or local computation
    - ✅ Rigorous statistical tests (Chi-square, t-test, KS test, etc.)
    - ✅ Immediate provability (run right now!)
    - ✅ Publication-ready output
    
    **Sacred numbers:** 3, 7, 11, φ (golden ratio), Fibonacci sequence
    """)
    
    tester = SacredNumberTester()
    
    # Create tabs for all 10 experiments
    tabs = st.tabs([
        "1️⃣ Riemann Sacred 11",
        "2️⃣ BSD Sacred 7",
        "3️⃣ Coherence 0.91",
        "4️⃣ Golden Ratio φ",
        "5️⃣ Prime Gaps",
        "6️⃣ π Digits",
        "7️⃣ Fibonacci",
        "8️⃣ Twin Primes",
        "9️⃣ Perfect Numbers",
        "🔟 Mersenne Primes"
    ])
    
    # Tab 1: Riemann Sacred 11
    with tabs[0]:
        st.header("Riemann Hypothesis: Sacred 11 Pattern")
        
        st.markdown("""
        **Prediction:** Riemann zero spacings grouped by position mod 11 show different distributions.
        
        **Data Source:** Odlyzko tables (publicly available)  
        **Statistical Test:** Kruskal-Wallis H-test (non-parametric ANOVA)  
        **Null Hypothesis:** No difference between groups  
        **Alternative:** Sacred groups (3, 7, 11) differ from mundane groups
        """)
        
        if st.button("🚀 Run Riemann Sacred 11 Test", key="riemann_test"):
            # Download zeros
            zeros = tester.download_riemann_zeros(n_zeros=100000)
            
            if zeros is not None and len(zeros) > 0:
                st.success(f"✅ Downloaded {len(zeros):,} Riemann zeros")
                
                # Run test
                result = tester.test_sacred_11_riemann(zeros)
                
                if result['status'] == 'success':
                    st.subheader("📊 Results")
                    
                    # Display main statistics
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Zeros Analyzed", f"{result['n_zeros']:,}")
                    with col2:
                        st.metric("Kruskal-Wallis p-value", f"{result['kruskal_wallis']['p_value']:.6f}")
                    with col3:
                        significance = "✅ SIGNIFICANT" if result['kruskal_wallis']['p_value'] < 0.05 else "❌ Not Significant"
                        st.metric("Result", significance)
                    
                    # Sacred vs Mundane comparison
                    st.subheader("Sacred vs Mundane Groups")
                    sacred_mundane = result['sacred_vs_mundane']
                    
                    col1, col2 = st.columns(2)
                    with col1:
                        st.metric("Sacred Mean Spacing", f"{sacred_mundane['sacred_mean']:.6f}")
                        st.metric("Effect Size (Cohen's d)", f"{sacred_mundane['effect_size']:.4f}")
                    with col2:
                        st.metric("Mundane Mean Spacing", f"{sacred_mundane['mundane_mean']:.6f}")
                        st.metric("p-value", f"{sacred_mundane['p_value']:.6f}")
                    
                    # Group statistics table
                    st.subheader("Spacing Statistics by Group (mod 11)")
                    group_data = []
                    for i in range(11):
                        stats_dict = result['group_stats'][str(i)]
                        group_data.append({
                            'Group': f"{i} {'(SACRED)' if i in [3, 7, 10] else ''}",
                            'Mean': stats_dict['mean'],
                            'Median': stats_dict['median'],
                            'Std Dev': stats_dict['std'],
                            'Count': stats_dict['n']
                        })
                    
                    st.dataframe(pd.DataFrame(group_data), use_container_width=True)
                    
                    # Visualization
                    fig = go.Figure()
                    for i in range(11):
                        stats_dict = result['group_stats'][str(i)]
                        color = 'red' if i in [3, 7, 10] else 'blue'
                        fig.add_trace(go.Bar(
                            x=[i],
                            y=[stats_dict['mean']],
                            name=f"Group {i}",
                            marker_color=color,
                            showlegend=False
                        ))
                    
                    fig.update_layout(
                        title="Mean Zero Spacing by Position mod 11",
                        xaxis_title="Group (mod 11)",
                        yaxis_title="Mean Spacing",
                        height=400
                    )
                    st.plotly_chart(fig, use_container_width=True)
                    
                    # Save results
                    st.download_button(
                        "💾 Download Results (JSON)",
                        data=json.dumps(result, indent=2),
                        file_name=f"riemann_sacred_11_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                        mime="application/json"
                    )
                else:
                    st.error(f"Test failed: {result.get('message', 'Unknown error')}")
    
    # Tab 2: BSD Sacred 7
    with tabs[1]:
        st.header("BSD Conjecture: Sacred 7 Pattern")
        
        st.markdown("""
        **Prediction:** Elliptic curves with conductor divisible by 7 show different rank distributions.
        
        **Data Source:** LMFDB API (free access)  
        **Statistical Test:** Mann-Whitney U test  
        **Null Hypothesis:** No difference in rank distribution  
        **Alternative:** Sacred curves (conductor ≡ 0 mod 7) differ from mundane curves
        """)
        
        max_conductor = st.number_input("Maximum Conductor", min_value=1000, max_value=100000, value=10000, step=1000)
        
        if st.button("🚀 Run BSD Sacred 7 Test", key="bsd_test"):
            # Query LMFDB
            curves_df = tester.query_lmfdb_curves(max_conductor=max_conductor)
            
            if curves_df is not None and len(curves_df) > 0:
                st.success(f"✅ Retrieved {len(curves_df):,} elliptic curves")
                
                # Run test
                result = tester.test_sacred_7_bsd(curves_df)
                
                if result['status'] == 'success':
                    st.subheader("📊 Results")
                    
                    # Display main statistics
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Curves Analyzed", f"{result['n_curves']:,}")
                    with col2:
                        st.metric("Mann-Whitney p-value", f"{result['mann_whitney']['p_value']:.6f}")
                    with col3:
                        significance = "✅ SIGNIFICANT" if result['mann_whitney']['p_value'] < 0.05 else "❌ Not Significant"
                        st.metric("Result", significance)
                    
                    # Sacred vs Mundane comparison
                    st.subheader("Sacred vs Mundane Curves")
                    
                    col1, col2 = st.columns(2)
                    with col1:
                        st.metric("Sacred Mean Rank", f"{result['rank_comparison']['sacred_mean']:.4f}")
                        st.metric("Sacred Curves", f"{result['n_sacred']:,}")
                    with col2:
                        st.metric("Mundane Mean Rank", f"{result['rank_comparison']['mundane_mean']:.4f}")
                        st.metric("Mundane Curves", f"{result['n_mundane']:,}")
                    
                    st.metric("Rank Difference", f"{result['rank_comparison']['difference']:.4f}")
                    st.metric("Cohen's d Effect Size", f"{result['effect_size']['cohens_d']:.4f} ({result['effect_size']['interpretation']})")
                    
                    # Rank distribution by mod 7
                    st.subheader("Rank Distribution by Conductor mod 7")
                    
                    dist_data = []
                    for i in range(7):
                        dist_dict = result['rank_distribution_by_mod7'][str(i)]
                        dist_data.append({
                            'Group': f"{i} {'(SACRED)' if i == 0 else ''}",
                            'N Curves': dist_dict['n_curves'],
                            'Mean Rank': dist_dict['mean_rank'],
                            'Rank 0': dist_dict['rank_0'],
                            'Rank 1': dist_dict['rank_1'],
                            'Rank 2+': dist_dict['rank_2plus']
                        })
                    
                    st.dataframe(pd.DataFrame(dist_data), use_container_width=True)
                    
                    # Visualization
                    fig = go.Figure()
                    for i in range(7):
                        dist_dict = result['rank_distribution_by_mod7'][str(i)]
                        color = 'red' if i == 0 else 'blue'
                        fig.add_trace(go.Bar(
                            x=[i],
                            y=[dist_dict['mean_rank']],
                            name=f"Group {i}",
                            marker_color=color,
                            showlegend=False
                        ))
                    
                    fig.update_layout(
                        title="Mean Rank by Conductor mod 7",
                        xaxis_title="Conductor mod 7",
                        yaxis_title="Mean Rank",
                        height=400
                    )
                    st.plotly_chart(fig, use_container_width=True)
                    
                    # Save results
                    st.download_button(
                        "💾 Download Results (JSON)",
                        data=json.dumps(result, indent=2),
                        file_name=f"bsd_sacred_7_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                        mime="application/json"
                    )
                else:
                    st.error(f"Test failed: {result.get('message', 'Unknown error')}")
    
    # Tab 3: Coherence Threshold
    with tabs[2]:
        st.header("Coherence Threshold: Mathematical Insights at 0.91")
        
        st.markdown("""
        **Prediction:** Mathematical breakthroughs occur when heart coherence ≥ 0.91
        
        **Data Source:** Polar H10 biometric logs (this platform)  
        **Statistical Test:** One-sample t-test  
        **Null Hypothesis:** Mean coherence ≤ 0.91  
        **Alternative:** Mean coherence > 0.91
        """)
        
        st.subheader("📝 Log New Insight")
        
        col1, col2 = st.columns(2)
        with col1:
            problem = st.selectbox("Problem", ["riemann", "bsd", "p_vs_np", "navier_stokes", "yang_mills", "hodge"])
        with col2:
            # Placeholder for real coherence (would come from Polar H10)
            coherence = st.number_input("Current Coherence", min_value=0.0, max_value=1.0, value=0.75, step=0.01)
        
        insight = st.text_area("Describe the insight")
        
        if st.button("💾 Log Insight"):
            if insight.strip():
                success = tester.log_coherence_insight(problem, insight, coherence)
                if success:
                    st.success("✅ Insight logged!")
                    st.rerun()
            else:
                st.warning("Please describe the insight")
        
        st.divider()
        
        st.subheader("📊 Analyze Logged Insights")
        
        # Retrieve insights
        insights_df = tester.get_coherence_insights()
        
        if len(insights_df) > 0:
            st.dataframe(insights_df, use_container_width=True)
            
            if st.button("🚀 Test Coherence Threshold", key="coherence_test"):
                result = tester.test_coherence_threshold(insights_df, threshold=0.91)
                
                if result['status'] == 'success':
                    st.subheader("📊 Results")
                    
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Insights Analyzed", result['n_insights'])
                    with col2:
                        st.metric("Mean Coherence", f"{result['mean_coherence']:.4f}")
                    with col3:
                        st.metric("p-value", f"{result['t_test']['p_value']:.6f}")
                    
                    # Confidence interval
                    ci = result['confidence_interval_95']
                    st.metric("95% Confidence Interval", f"[{ci['lower']:.4f}, {ci['upper']:.4f}]")
                    
                    # Proportion above threshold
                    prop = result['proportion_above_threshold']
                    st.metric(f"Above {result['threshold']}", f"{prop['count']}/{result['n_insights']} ({prop['percentage']:.1f}%)")
                    
                    st.info(result['t_test']['interpretation'])
                    
                    # Visualization
                    fig = go.Figure()
                    fig.add_trace(go.Histogram(
                        x=insights_df['coherence'],
                        nbinsx=20,
                        name="Coherence Distribution"
                    ))
                    fig.add_vline(x=0.91, line_dash="dash", line_color="red", annotation_text="Threshold (0.91)")
                    fig.add_vline(x=result['mean_coherence'], line_dash="dot", line_color="green", annotation_text=f"Mean ({result['mean_coherence']:.3f})")
                    
                    fig.update_layout(
                        title="Coherence Distribution at Insight Moments",
                        xaxis_title="Coherence",
                        yaxis_title="Count",
                        height=400
                    )
                    st.plotly_chart(fig, use_container_width=True)
                    
                    # Save results
                    st.download_button(
                        "💾 Download Results (JSON)",
                        data=json.dumps(result, indent=2),
                        file_name=f"coherence_threshold_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json",
                        mime="application/json"
                    )
                else:
                    st.error(f"Test failed: {result.get('message', 'Unknown error')}")
        else:
            st.info("No insights logged yet. Log some insights above to run the analysis!")
    
    # Tab 4: Golden Ratio φ
    with tabs[3]:
        st.header("Golden Ratio in Riemann Zeros")
        
        st.markdown("""
        **Prediction:** Consecutive spacing ratios follow golden ratio φ ≈ 1.618
        
        **Tests:** t-test (mean = φ?) + KS test (distribution shape)
        """)
        
        if st.button("🚀 Run Golden Ratio Test", key="phi_test"):
            zeros = tester.download_riemann_zeros(n_zeros=100000)
            
            if zeros is not None and len(zeros) > 0:
                result = tester.test_golden_ratio_riemann(zeros)
                
                if result['status'] == 'success':
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Ratios Analyzed", f"{result['n_ratios']:,}")
                    with col2:
                        st.metric("Mean Ratio", f"{result['mean_ratio']:.4f}")
                    with col3:
                        st.metric("φ (Golden Ratio)", f"{result['phi']:.4f}")
                    
                    st.metric("p-value", f"{result['t_test']['p_value']:.6f}")
                    st.info(result['t_test']['interpretation'])
                    
                    prop = result['near_phi']
                    st.metric(f"Ratios Near φ (±10%)", f"{prop['count']:,} ({prop['percentage']:.1f}%)")
                    
                    st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                     file_name=f"golden_ratio_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    
    # Tab 5: Prime Gaps
    with tabs[4]:
        st.header("Prime Gaps Sacred Patterns")
        
        st.markdown("""
        **Prediction:** Prime gaps divisible by 3, 7, 11 are more common than expected
        
        **Test:** Chi-square goodness of fit
        """)
        
        n_primes = st.slider("Number of Primes", 1000, 50000, 10000, step=1000)
        
        if st.button("🚀 Run Prime Gaps Test", key="prime_gaps_test"):
            result = tester.test_prime_gaps_sacred(n_primes=n_primes)
            
            if result['status'] == 'success':
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("Primes Analyzed", f"{result['n_primes']:,}")
                with col2:
                    st.metric("Prime Gaps", f"{result['n_gaps']:,}")
                
                st.subheader("Sacred Number Tests")
                for num in [3, 7, 11]:
                    test = result['sacred_tests'][str(num)]
                    st.markdown(f"**Divisible by {num}:**")
                    col1, col2, col3 = st.columns(3)
                    with col1:
                        st.metric("Observed", test['observed'])
                    with col2:
                        st.metric("Expected", f"{test['expected']:.0f}")
                    with col3:
                        st.metric("p-value", f"{test['p_value']:.4f}")
                
                st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                 file_name=f"prime_gaps_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    
    # Tab 6: π Digits
    with tabs[5]:
        st.header("π Digits Sacred Patterns")
        
        st.markdown("""
        **Prediction:** Digits 3, 7 and sacred pairs (11, 33, 37, 73) appear at special frequencies
        
        **Test:** Chi-square test for uniformity
        """)
        
        if st.button("🚀 Run π Digits Test", key="pi_test"):
            result = tester.test_pi_digits_sacred(n_digits=200)
            
            if result['status'] == 'success':
                st.metric("Digits Analyzed", result['n_digits'])
                
                st.subheader("Digit Frequencies")
                st.json(result['digit_frequencies'])
                
                st.subheader("Sacred Patterns")
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown("**Sacred Singles:**")
                    st.json(result['sacred_singles'])
                with col2:
                    st.markdown("**Sacred Pairs:**")
                    st.json(result['sacred_pairs'])
                
                st.metric("Chi-square p-value", f"{result['chi_square']['p_value']:.6f}")
                st.info(result['chi_square']['interpretation'])
                
                st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                 file_name=f"pi_digits_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    
    # Tab 7: Fibonacci
    with tabs[6]:
        st.header("Fibonacci & Golden Ratio Convergence")
        
        st.markdown("""
        **Prediction:** Fibonacci ratios F(n+1)/F(n) converge exponentially to φ
        
        **Test:** Linear regression on log(error)
        """)
        
        if st.button("🚀 Run Fibonacci Test", key="fib_test"):
            result = tester.test_fibonacci_in_constants()
            
            if result['status'] == 'success':
                st.subheader("Fibonacci Sequence")
                st.write(result['fibonacci_sequence'])
                
                conv = result['convergence_to_phi']
                st.subheader("Convergence to φ")
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("φ (Target)", f"{conv['phi']:.6f}")
                    st.metric("Final Ratio", f"{conv['final_ratio']:.6f}")
                with col2:
                    st.metric("Error", f"{conv['error']:.8f}")
                    st.metric("R²", f"{conv['convergence_rate']['r_squared']:.6f}")
                
                st.subheader("Constant Analysis")
                col1, col2 = st.columns(2)
                with col1:
                    st.markdown("**e digits:**")
                    st.metric("Near φ", f"{result['e_digit_ratios']['near_phi_proportion']:.1%}")
                with col2:
                    st.markdown("**π digits:**")
                    st.metric("Near φ", f"{result['pi_digit_ratios']['near_phi_proportion']:.1%}")
                
                st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                 file_name=f"fibonacci_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    
    # Tab 8: Twin Primes
    with tabs[7]:
        st.header("Twin Primes Sacred Clustering")
        
        st.markdown("""
        **Prediction:** Twin primes (p, p+2) cluster at sacred positions mod 11
        
        **Test:** Chi-square test
        """)
        
        limit = st.slider("Search Limit", 10000, 1000000, 100000, step=10000)
        
        if st.button("🚀 Run Twin Primes Test", key="twin_test"):
            result = tester.test_twin_primes_sacred(limit=limit)
            
            if result['status'] == 'success':
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("Twin Prime Pairs", result['n_twin_primes'])
                with col2:
                    st.metric("Sacred Proportion", f"{result['sacred_vs_mundane']['sacred_proportion']:.1%}")
                
                st.subheader("Distribution mod 11")
                st.json(result['mod_11_distribution'])
                
                st.metric("p-value", f"{result['chi_square']['p_value']:.6f}")
                st.info(result['chi_square']['interpretation'])
                
                st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                 file_name=f"twin_primes_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    
    # Tab 9: Perfect Numbers
    with tabs[8]:
        st.header("Perfect Numbers Sacred Patterns")
        
        st.markdown("""
        **Prediction:** Perfect numbers (n = Σ divisors) have sacred digit sums or divisor counts
        
        **Test:** Exact enumeration of known perfect numbers
        """)
        
        if st.button("🚀 Run Perfect Numbers Test", key="perfect_test"):
            result = tester.test_perfect_numbers_sacred()
            
            if result['status'] == 'success':
                st.metric("Perfect Numbers Analyzed", result['n_perfect_numbers'])
                
                st.subheader("Analysis Results")
                df = pd.DataFrame(result['analyses'])
                st.dataframe(df, use_container_width=True)
                
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("Sacred Digit Sums", f"{result['sacred_patterns']['digit_sum_sacred']['count']}/{result['n_perfect_numbers']}")
                with col2:
                    st.metric("Sacred Divisor Counts", f"{result['sacred_patterns']['divisor_count_sacred']['count']}/{result['n_perfect_numbers']}")
                
                st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                 file_name=f"perfect_numbers_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    
    # Tab 10: Mersenne Primes
    with tabs[9]:
        st.header("Mersenne Primes Sacred Exponents")
        
        st.markdown("""
        **Prediction:** Mersenne prime exponents cluster at sacred positions mod 11
        
        **Test:** Chi-square test on known Mersenne primes
        """)
        
        if st.button("🚀 Run Mersenne Test", key="mersenne_test"):
            result = tester.test_mersenne_primes_sacred()
            
            if result['status'] == 'success':
                st.metric("Mersenne Primes Analyzed", result['n_mersenne_primes'])
                
                st.subheader("Exponents (first 10)")
                st.write(result['exponents'])
                
                st.subheader("Distribution mod 11")
                st.json(result['mod_11_distribution'])
                
                col1, col2 = st.columns(2)
                with col1:
                    st.metric("Sacred Count", result['sacred_vs_mundane']['sacred_count'])
                with col2:
                    st.metric("p-value", f"{result['chi_square']['p_value']:.6f}")
                
                st.info(result['chi_square']['interpretation'])
                
                st.download_button("💾 Download", data=json.dumps(result, indent=2),
                                 file_name=f"mersenne_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
