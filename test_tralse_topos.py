"""
Test suite for Tralse Topos implementation
Validates associativity, distributivity, and absorption properties
"""

import numpy as np
from tralse_topos_engine import (
    TralseVector, TralseTopos,
    T_PURE, F_PURE, PHI_TYPICAL, PSI_PURE
)

def test_associativity():
    """
    Test (A ∧ B) ∧ C = A ∧ (B ∧ C) and (A ∨ B) ∨ C = A ∨ (B ∨ C)
    """
    print("Testing Associativity...")
    
    # Test states
    states = [
        T_PURE,
        F_PURE,
        PHI_TYPICAL,
        TralseVector(0.6, 0.2, 0.2, 0.0),
        TralseVector(0.3, 0.3, 0.3, 0.1)
    ]
    
    failures = []
    
    for A in states:
        for B in states:
            for C in states:
                # AND associativity
                left = TralseTopos.tralse_and(TralseTopos.tralse_and(A, B), C)
                right = TralseTopos.tralse_and(A, TralseTopos.tralse_and(B, C))
                
                diff_and = np.linalg.norm(left.to_array() - right.to_array())
                if diff_and > 0.01:  # Tolerance for numerical precision
                    failures.append(f"AND associativity failed: ({A} AND {B}) AND {C} ≠ {A} AND ({B} AND {C}), diff={diff_and:.4f}")
                
                # OR associativity
                left = TralseTopos.tralse_or(TralseTopos.tralse_or(A, B), C)
                right = TralseTopos.tralse_or(A, TralseTopos.tralse_or(B, C))
                
                diff_or = np.linalg.norm(left.to_array() - right.to_array())
                if diff_or > 0.01:
                    failures.append(f"OR associativity failed: ({A} OR {B}) OR {C} ≠ {A} OR ({B} OR {C}), diff={diff_or:.4f}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures[:5]:  # Show first 5
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Associativity holds")

def test_commutativity():
    """
    Test A ∧ B = B ∧ A and A ∨ B = B ∨ A
    """
    print("Testing Commutativity...")
    
    states = [
        T_PURE,
        F_PURE,
        PHI_TYPICAL,
        TralseVector(0.6, 0.2, 0.2, 0.0)
    ]
    
    failures = []
    
    for A in states:
        for B in states:
            # AND commutativity
            ab = TralseTopos.tralse_and(A, B)
            ba = TralseTopos.tralse_and(B, A)
            
            diff_and = np.linalg.norm(ab.to_array() - ba.to_array())
            if diff_and > 0.01:
                failures.append(f"AND commutativity failed: {A} AND {B} ≠ {B} AND {A}, diff={diff_and:.4f}")
            
            # OR commutativity
            ab = TralseTopos.tralse_or(A, B)
            ba = TralseTopos.tralse_or(B, A)
            
            diff_or = np.linalg.norm(ab.to_array() - ba.to_array())
            if diff_or > 0.01:
                failures.append(f"OR commutativity failed: {A} OR {B} ≠ {B} OR {A}, diff={diff_or:.4f}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures[:5]:
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Commutativity holds")

def test_distributivity():
    """
    Test A ∧ (B ∨ C) = (A ∧ B) ∨ (A ∧ C)
    """
    print("Testing Distributivity...")
    
    states = [
        T_PURE,
        F_PURE,
        PHI_TYPICAL,
        TralseVector(0.6, 0.2, 0.2, 0.0)
    ]
    
    failures = []
    
    for A in states:
        for B in states:
            for C in states:
                left = TralseTopos.tralse_and(A, TralseTopos.tralse_or(B, C))
                right = TralseTopos.tralse_or(
                    TralseTopos.tralse_and(A, B),
                    TralseTopos.tralse_and(A, C)
                )
                
                diff = np.linalg.norm(left.to_array() - right.to_array())
                if diff > 0.01:
                    failures.append(f"Distributivity failed: {A} AND ({B} OR {C}) ≠ ({A} AND {B}) OR ({A} AND {C}), diff={diff:.4f}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures[:5]:
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Distributivity holds")

def test_absorption():
    """
    Test A ∧ (A ∨ B) = A
    """
    print("Testing Absorption...")
    
    states = [
        T_PURE,
        F_PURE,
        PHI_TYPICAL,
        TralseVector(0.6, 0.2, 0.2, 0.0)
    ]
    
    failures = []
    
    for A in states:
        for B in states:
            result = TralseTopos.tralse_and(A, TralseTopos.tralse_or(A, B))
            
            diff = np.linalg.norm(result.to_array() - A.to_array())
            if diff > 0.01:
                failures.append(f"Absorption failed: {A} AND ({A} OR {B}) ≠ {A}, diff={diff:.4f}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures[:5]:
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Absorption holds")

def test_identity():
    """
    Test A ∧ T = A, A ∨ F = A
    """
    print("Testing Identity...")
    
    states = [
        T_PURE,
        F_PURE,
        PHI_TYPICAL,
        TralseVector(0.6, 0.2, 0.2, 0.0)
    ]
    
    failures = []
    
    for A in states:
        # A ∧ T = A
        result = TralseTopos.tralse_and(A, T_PURE)
        diff = np.linalg.norm(result.to_array() - A.to_array())
        if diff > 0.01:
            failures.append(f"AND identity failed: {A} AND T ≠ {A}, diff={diff:.4f}")
        
        # A ∨ F = A
        result = TralseTopos.tralse_or(A, F_PURE)
        diff = np.linalg.norm(result.to_array() - A.to_array())
        if diff > 0.01:
            failures.append(f"OR identity failed: {A} OR F ≠ {A}, diff={diff:.4f}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures[:5]:
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Identity holds")

def test_double_negation():
    """
    Test ¬¬T = T, ¬¬F = F, ¬¬Φ = Φ, ¬¬Ψ = Ψ
    """
    print("Testing Double Negation...")
    
    states = [
        T_PURE,
        F_PURE,
        PHI_TYPICAL,
        PSI_PURE,
        TralseVector(0.6, 0.2, 0.2, 0.0)
    ]
    
    failures = []
    
    for A in states:
        result = TralseTopos.tralse_not(TralseTopos.tralse_not(A))
        diff = np.linalg.norm(result.to_array() - A.to_array())
        if diff > 0.01:
            failures.append(f"Double negation failed: ¬¬{A} ≠ {A}, diff={diff:.4f}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures[:5]:
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Double Negation holds")

def test_myrion_resolution_convergence():
    """
    Test that Myrion Resolution converges to balanced Φ state
    """
    print("Testing Myrion Resolution Convergence...")
    
    # Test cases
    test_cases = [
        (TralseVector(0.8, 0.1, 0.1, 0.0), TralseVector(0.7, 0.2, 0.1, 0.0), "Free Will vs Determinism"),
        (T_PURE, F_PURE, "Pure contradiction"),
        (TralseVector(0.9, 0.05, 0.05, 0.0), TralseVector(0.1, 0.8, 0.1, 0.0), "Strong disagreement")
    ]
    
    failures = []
    
    for tau_A, tau_B, description in test_cases:
        resolution = TralseTopos.myrion_resolution(tau_A, tau_B, iterations=100)
        
        # Check that resolution is balanced (not too binary)
        if resolution.p_T > 0.7 or resolution.p_F > 0.7:
            failures.append(f"{description}: Resolution too binary - {resolution}")
        
        # Check that resolution has substantial Φ component
        if resolution.p_Phi < 0.1:
            failures.append(f"{description}: Resolution lacks Φ component - {resolution}")
    
    if failures:
        print(f"  ❌ FAILED: {len(failures)} violations")
        for f in failures:
            print(f"    {f}")
    else:
        print("  ✅ PASSED: Myrion Resolution converges properly")

def run_all_tests():
    """
    Run complete test suite for Tralse Topos algebraic properties
    """
    print("=" * 60)
    print("TRALSE TOPOS ALGEBRAIC PROPERTY TESTS")
    print("=" * 60)
    
    test_commutativity()
    test_associativity()
    test_distributivity()
    test_absorption()
    test_identity()
    test_double_negation()
    test_myrion_resolution_convergence()
    
    print("=" * 60)
    print("TEST SUITE COMPLETE")
    print("=" * 60)

if __name__ == "__main__":
    run_all_tests()
