"""
Ternary Computation Framework
Based on Tralse Quadruplet Logic (T, F, Φ, Ψ)

Foundation: 3-11-33 sacred cascade
- Base-3 (ternary) radix
- 11 ternary digits per half-tralsebit
- 22 total (2 × 11 master numbers)
- 33 bits information capacity

Created: November 11, 2025
"""

import numpy as np
from typing import List, Tuple, Union
from enum import Enum


class TralseState(Enum):
    """
    Four-state tralse logic
    """
    T = 1      # True (classical affirmation)
    F = 0      # False (classical negation)
    PHI = -1   # Φ (Unknown but determinable)
    PSI = 0.5  # Ψ (Superposition - simultaneously T and F)


class TernaryDigit:
    """
    Base-3 digit: 0, 1, 2
    Maps to tralse states:
    - 0 → F (False)
    - 1 → Φ (Unknown/Indeterminate)
    - 2 → T (True)
    """
    
    def __init__(self, value: int):
        if value not in [0, 1, 2]:
            raise ValueError("Ternary digit must be 0, 1, or 2")
        self.value = value
    
    def to_tralse(self) -> TralseState:
        """Convert ternary to tralse state"""
        mapping = {
            0: TralseState.F,
            1: TralseState.PHI,
            2: TralseState.T
        }
        return mapping[self.value]
    
    def __repr__(self):
        return f"T3({self.value})"


class Tralsebit:
    """
    22 ternary digits = 1 tralsebit
    Information capacity: ~33 bits
    
    Structure:
    - 2 half-tralsebits (11 ternary digits each)
    - Sacred 3-11-33 cascade
    """
    
    def __init__(self, ternary_digits: List[int] | None = None):
        if ternary_digits is None:
            # Initialize with all Φ (unknown)
            ternary_digits = [1] * 22
        
        if len(ternary_digits) != 22:
            raise ValueError("Tralsebit requires exactly 22 ternary digits")
        
        self.digits = [TernaryDigit(d) for d in ternary_digits]
    
    def get_half_tralsebits(self) -> Tuple[List[TernaryDigit], List[TernaryDigit]]:
        """Split into two 11-digit half-tralsebits (master number!)"""
        return self.digits[:11], self.digits[11:]
    
    def to_binary_approximate(self) -> int:
        """
        Convert to approximate binary (33 bits)
        Each ternary digit encodes log2(3) ≈ 1.585 bits
        22 digits × 1.585 ≈ 34.87 bits (compressed to 33)
        """
        # Convert ternary to decimal
        decimal = 0
        for i, digit in enumerate(reversed(self.digits)):
            decimal += digit.value * (3 ** i)
        
        # Decimal range: 0 to 3^22 - 1 = 31,381,059,608
        # Map to 33 bits: 0 to 2^33 - 1 = 8,589,934,591
        # Scaling factor: 2^33 / 3^22 ≈ 0.2736
        
        max_ternary = 3 ** 22
        max_binary = 2 ** 33
        binary_value = int((decimal / max_ternary) * max_binary)
        
        return binary_value
    
    def from_binary(self, binary_value: int) -> None:
        """
        Convert 33-bit binary to tralsebit
        Inverse of to_binary_approximate
        """
        if binary_value < 0 or binary_value >= 2**33:
            raise ValueError("Binary value must be in range [0, 2^33)")
        
        max_ternary = 3 ** 22
        max_binary = 2 ** 33
        
        # Scale back to ternary range
        decimal = int((binary_value / max_binary) * max_ternary)
        
        # Convert decimal to ternary
        ternary_digits = []
        for _ in range(22):
            ternary_digits.append(decimal % 3)
            decimal //= 3
        
        ternary_digits.reverse()
        self.digits = [TernaryDigit(d) for d in ternary_digits]
    
    def extract_i_cell_signature(self, ecg_samples: List[float]) -> 'Tralsebit':
        """
        Extract I-Cell signature from ECG waveform
        
        Method:
        1. Normalize ECG to [0, 1]
        2. Discretize into 3 levels (ternary encoding)
        3. Take 22-sample chunks
        4. Each chunk = 1 tralsebit
        
        Returns first complete tralsebit signature
        """
        if len(ecg_samples) < 22:
            raise ValueError("Need at least 22 ECG samples for signature")
        
        # Normalize
        min_val = min(ecg_samples)
        max_val = max(ecg_samples)
        
        # Handle flat/constant signal (cardiac arrest, sensor dropout, calibration)
        if abs(max_val - min_val) < 1e-10:
            # Flat signal → All Φ (unknown) state (middle value = 1)
            normalized = [0.5] * 22  # Will map to all Φ
        else:
            normalized = [(s - min_val) / (max_val - min_val) for s in ecg_samples[:22]]
        
        # Ternary encoding (3 voltage levels)
        ternary = []
        for val in normalized:
            if val < 0.33:
                ternary.append(0)  # Low → F
            elif val < 0.67:
                ternary.append(1)  # Mid → Φ
            else:
                ternary.append(2)  # High → T
        
        self.digits = [TernaryDigit(d) for d in ternary]
        return self
    
    def __repr__(self):
        half1, half2 = self.get_half_tralsebits()
        return f"Tralsebit([{''.join(str(d.value) for d in half1)}|{''.join(str(d.value) for d in half2)}])"


class TernaryGate:
    """
    Ternary logic gates (3-valued logic)
    Inputs/outputs: 0 (F), 1 (Φ), 2 (T)
    """
    
    @staticmethod
    def AND(a: int, b: int) -> int:
        """Ternary AND: min(a, b)"""
        return min(a, b)
    
    @staticmethod
    def OR(a: int, b: int) -> int:
        """Ternary OR: max(a, b)"""
        return max(a, b)
    
    @staticmethod
    def NOT(a: int) -> int:
        """Ternary NOT: 2-a (inverts T↔F, Φ→Φ)"""
        return 2 - a
    
    @staticmethod
    def CONSENSUS(a: int, b: int) -> int:
        """
        Ternary CONSENSUS (unique to 3-valued logic)
        Truth table:
        C(0,0)=0, C(0,1)=1, C(0,2)=1
        C(1,0)=1, C(1,1)=1, C(1,2)=1
        C(2,0)=1, C(2,1)=1, C(2,2)=2
        
        Meaning: Returns Φ except when both agree
        """
        if a == b:
            return a
        else:
            return 1  # Φ (unknown when disagreement)
    
    @staticmethod
    def MYRION_RESOLVE(a: int, b: int) -> int:
        """
        Myrion Resolution for contradictions
        Averages the contradiction (harmonic resolution)
        
        Example: FIRE (2) vs DON'T_FIRE (0) → MAYBE_FIRE (1)
        """
        return (a + b) // 2


class TralseLogicGate:
    """
    4-valued Tralse logic gates
    Handles T, F, Φ, Ψ (superposition)
    """
    
    @staticmethod
    def AND(a: TralseState, b: TralseState) -> TralseState:
        """
        Tralse AND truth table
        """
        # If either is F, result is F
        if a == TralseState.F or b == TralseState.F:
            return TralseState.F
        
        # If both are T, result is T
        if a == TralseState.T and b == TralseState.T:
            return TralseState.T
        
        # If either is Ψ (superposition), result is Ψ
        if a == TralseState.PSI or b == TralseState.PSI:
            return TralseState.PSI
        
        # Otherwise Φ (unknown)
        return TralseState.PHI
    
    @staticmethod
    def OR(a: TralseState, b: TralseState) -> TralseState:
        """
        Tralse OR truth table
        """
        # If either is T, result is T
        if a == TralseState.T or b == TralseState.T:
            return TralseState.T
        
        # If both are F, result is F
        if a == TralseState.F and b == TralseState.F:
            return TralseState.F
        
        # If either is Ψ (superposition), result is Ψ
        if a == TralseState.PSI or b == TralseState.PSI:
            return TralseState.PSI
        
        # Otherwise Φ (unknown)
        return TralseState.PHI
    
    @staticmethod
    def NOT(a: TralseState) -> TralseState:
        """
        Tralse NOT:
        T → F
        F → T
        Φ → Φ (unknown stays unknown)
        Ψ → Ψ (superposition stays superposition)
        """
        mapping = {
            TralseState.T: TralseState.F,
            TralseState.F: TralseState.T,
            TralseState.PHI: TralseState.PHI,
            TralseState.PSI: TralseState.PSI
        }
        return mapping[a]
    
    @staticmethod
    def COLLAPSE(a: TralseState, probability: float = 0.5) -> TralseState:
        """
        Collapse Ψ (superposition) to T or F
        Simulates quantum measurement / free will injection
        
        Args:
            a: Tralse state
            probability: P(collapse to T) if in superposition
        
        Returns:
            T or F if originally Ψ, otherwise unchanged
        """
        if a == TralseState.PSI:
            # Quantum collapse via free will choice
            return TralseState.T if np.random.random() < probability else TralseState.F
        return a


class TernaryAdder:
    """
    Ternary arithmetic (balanced ternary: -1, 0, 1)
    More efficient than binary for some operations
    """
    
    @staticmethod
    def balanced_add(a: int, b: int) -> Tuple[int, int]:
        """
        Add two balanced ternary digits (-1, 0, 1)
        Returns (sum_digit, carry)
        """
        total = a + b
        
        if total == -2:
            return (1, -1)  # -2 = 1 - 3
        elif total == -1:
            return (-1, 0)
        elif total == 0:
            return (0, 0)
        elif total == 1:
            return (1, 0)
        elif total == 2:
            return (-1, 1)  # 2 = -1 + 3
        else:
            raise ValueError(f"Invalid balanced ternary sum: {total}")
    
    @staticmethod
    def to_balanced_ternary(decimal: int) -> List[int]:
        """
        Convert decimal to balanced ternary
        Uses digits: -1, 0, 1
        """
        if decimal == 0:
            return [0]
        
        digits = []
        n = abs(decimal)
        
        while n > 0:
            if n % 3 == 0:
                digits.append(0)
                n //= 3
            elif n % 3 == 1:
                digits.append(1)
                n //= 3
            else:  # n % 3 == 2
                digits.append(-1)
                n = (n + 1) // 3
        
        if decimal < 0:
            digits = [-d for d in digits]
        
        digits.reverse()
        return digits
    
    @staticmethod
    def from_balanced_ternary(digits: List[int]) -> int:
        """
        Convert balanced ternary to decimal
        """
        decimal = 0
        for i, digit in enumerate(reversed(digits)):
            decimal += digit * (3 ** i)
        return decimal


class NeuronTralsebit:
    """
    Neuron as living tralsebit
    Maps neural states to tralse logic
    """
    
    def __init__(self, resting_potential: float = -70.0, threshold: float = -55.0):
        self.resting_potential = resting_potential  # mV
        self.threshold = threshold  # mV
        self.current_potential = resting_potential
        self.state = TralseState.F  # Resting = False
    
    def set_voltage(self, voltage: float) -> TralseState:
        """
        Map neuron voltage to tralse state
        
        Mapping:
        - Below threshold: F (not firing)
        - At threshold (graded): Φ (unknown if will fire)
        - Above threshold: T (firing)
        - Quantum coherent state: Ψ (superposition)
        """
        self.current_potential = voltage
        
        if voltage < self.threshold - 5:
            self.state = TralseState.F
        elif voltage < self.threshold:
            self.state = TralseState.PHI  # Sub-threshold graded potential
        else:
            self.state = TralseState.T  # Action potential
        
        return self.state
    
    def quantum_coherent(self) -> None:
        """
        Put neuron in quantum coherent superposition (Penrose-Hameroff)
        Microtubules in Ψ state
        """
        self.state = TralseState.PSI
    
    def collapse_wavefunction(self, free_will_bias: float = 0.5) -> TralseState:
        """
        Consciousness injects free will to collapse Ψ → T or F
        
        Args:
            free_will_bias: Probability of choosing to fire
        
        Returns:
            Collapsed state (T or F)
        """
        if self.state == TralseState.PSI:
            self.state = TralseLogicGate.COLLAPSE(self.state, free_will_bias)
        return self.state
    
    def encode_tralsebit(self, spike_train: List[float]) -> Tralsebit:
        """
        Encode spike train as tralsebit
        
        Method:
        - Take 22 time windows
        - Classify each as F, Φ, or T based on voltage
        - Construct tralsebit
        
        Returns 33 bits of information!
        """
        if len(spike_train) < 22:
            raise ValueError("Need at least 22 time samples")
        
        ternary = []
        for voltage in spike_train[:22]:
            if voltage < self.threshold - 5:
                ternary.append(0)  # F
            elif voltage < self.threshold:
                ternary.append(1)  # Φ
            else:
                ternary.append(2)  # T
        
        return Tralsebit(ternary)


# Example usage and tests
if __name__ == "__main__":
    print("=== TERNARY COMPUTATION FRAMEWORK ===\n")
    
    # 1. Ternary gates
    print("1. TERNARY LOGIC GATES:")
    print(f"AND(2,1) = {TernaryGate.AND(2, 1)} (T AND Φ = Φ)")
    print(f"OR(2,0) = {TernaryGate.OR(2, 0)} (T OR F = T)")
    print(f"NOT(2) = {TernaryGate.NOT(2)} (NOT T = F)")
    print(f"CONSENSUS(0,2) = {TernaryGate.CONSENSUS(0, 2)} (Disagreement = Φ)")
    print(f"MYRION_RESOLVE(2,0) = {TernaryGate.MYRION_RESOLVE(2, 0)} (FIRE vs DON'T_FIRE = MAYBE)")
    print()
    
    # 2. Tralsebit creation
    print("2. TRALSEBIT (22 ternary digits = 33 bits):")
    tb = Tralsebit([2,1,0,2,1,1,0,2,0,1,2,  # First half (11 digits)
                    1,0,2,1,2,0,1,1,2,0,1])  # Second half (11 digits)
    print(f"Tralsebit: {tb}")
    print(f"Binary approximation (33 bits): {tb.to_binary_approximate()}")
    half1, half2 = tb.get_half_tralsebits()
    print(f"Half-tralsebits (11 each): {len(half1)}, {len(half2)}")
    print()
    
    # 3. I-Cell signature from ECG
    print("3. I-CELL SIGNATURE EXTRACTION:")
    # Simulated ECG (heart coherent state)
    ecg_coherent = [0.5 + 0.3*np.sin(2*np.pi*i/22) for i in range(22)]
    signature = Tralsebit().extract_i_cell_signature(ecg_coherent)
    print(f"I-Cell signature from ECG: {signature}")
    print()
    
    # 4. Tralse logic gates
    print("4. TRALSE LOGIC (4-state):")
    print(f"T AND F = {TralseLogicGate.AND(TralseState.T, TralseState.F)}")
    print(f"Ψ OR Φ = {TralseLogicGate.OR(TralseState.PSI, TralseState.PHI)}")
    print(f"NOT(T) = {TralseLogicGate.NOT(TralseState.T)}")
    print(f"COLLAPSE(Ψ) = {TralseLogicGate.COLLAPSE(TralseState.PSI, 0.7)} (70% → T)")
    print()
    
    # 5. Neuron as tralsebit
    print("5. NEURON AS LIVING TRALSEBIT:")
    neuron = NeuronTralsebit()
    print(f"Resting (-70mV): {neuron.set_voltage(-70)}")
    print(f"Graded (-60mV): {neuron.set_voltage(-60)}")
    print(f"Firing (-40mV): {neuron.set_voltage(-40)}")
    neuron.quantum_coherent()
    print(f"Quantum coherent: {neuron.state}")
    print(f"Free will collapse: {neuron.collapse_wavefunction(0.8)}")
    print()
    
    # 6. Balanced ternary arithmetic
    print("6. BALANCED TERNARY ARITHMETIC:")
    bt = TernaryAdder()
    print(f"Decimal 42 → Balanced ternary: {bt.to_balanced_ternary(42)}")
    print(f"Back to decimal: {bt.from_balanced_ternary(bt.to_balanced_ternary(42))}")
    print(f"Decimal -17 → Balanced ternary: {bt.to_balanced_ternary(-17)}")
    print()
    
    # 7. Sacred 3-11-33 cascade
    print("7. SACRED 3-11-33 CASCADE:")
    print("✅ Base radix: 3 (ternary)")
    print("✅ Structural unit: 11 (half-tralsebit, master number)")
    print("✅ Total capacity: 22 × log₂(3) ≈ 33 bits")
    print("✅ Master numbers: 2 × 11 = 22 ternary digits")
    print()
    
    print("=== TERNARY FRAMEWORK COMPLETE! ===")
    print("Ready for:")
    print("- Ternary neural networks")
    print("- Consciousness-aware computing")
    print("- Quantum-classical hybrid algorithms")
    print("- I-cell signature processing")
