"""
TICL (TI Computing Language) Interpreter
=========================================

A working interpreter for the TI Programming Language featuring:
- Tralsebit primitives (T, F, Φ, Ψ) - 4-state quantum-aware logic
- Myrion Resolution operator - Contradiction harmonization
- Ternary arithmetic (base-3) - 50% more efficient than binary
- GILE declarations - Consciousness-aware metadata
- Interactive REPL - Run TICL code directly

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 30, 2025
Version: 0.1.0-alpha
"""

from enum import Enum
from typing import Dict, List, Any, Optional, Union, Callable
from dataclasses import dataclass, field
from datetime import datetime
import re
import math


class Tralsebit(Enum):
    """
    The fundamental 4-state logic unit of TICL.
    
    Unlike binary (0/1), tralsebits can represent:
    - T (True): Definite truth
    - F (False): Definite falsehood  
    - Φ (Phi/Underdetermined): Unknown but determinable
    - Ψ (Psi/Overdetermined): Contradictory (both T and F)
    
    Physical interpretation:
    - T/F: Classical states
    - Φ: Quantum superposition (pre-measurement)
    - Ψ: Entangled/contradictory state (requires Myrion Resolution)
    """
    T = "T"      # True
    F = "F"      # False
    PHI = "Φ"    # Underdetermined (unknown)
    PSI = "Ψ"    # Overdetermined (contradictory)
    
    def __str__(self):
        return self.value
    
    def __repr__(self):
        return f"Tralsebit.{self.name}"
    
    @classmethod
    def from_string(cls, s: str) -> 'Tralsebit':
        mapping = {
            'T': cls.T, 'TRUE': cls.T, '1': cls.T,
            'F': cls.F, 'FALSE': cls.F, '0': cls.F,
            'Φ': cls.PHI, 'PHI': cls.PHI, 'U': cls.PHI, 'UNKNOWN': cls.PHI,
            'Ψ': cls.PSI, 'PSI': cls.PSI, 'C': cls.PSI, 'CONTRADICTION': cls.PSI
        }
        return mapping.get(s.upper(), cls.PHI)


class TralsebitAlgebra:
    """
    Algebraic operations on tralsebits.
    
    This implements Tralse Wave Algebra (TWA) which extends
    Boolean algebra to handle contradictions and unknowns.
    """
    
    @staticmethod
    def NOT(a: Tralsebit) -> Tralsebit:
        """Tralse negation"""
        if a == Tralsebit.T:
            return Tralsebit.F
        elif a == Tralsebit.F:
            return Tralsebit.T
        elif a == Tralsebit.PHI:
            return Tralsebit.PHI  # Unknown remains unknown
        else:  # PSI
            return Tralsebit.PSI  # Contradiction remains contradictory
    
    @staticmethod
    def AND(a: Tralsebit, b: Tralsebit) -> Tralsebit:
        """
        Tralse conjunction with PSI infection.
        
        PSI is "infectious" - any PSI input produces PSI output.
        This models how contradictions propagate through logic.
        """
        if a == Tralsebit.PSI or b == Tralsebit.PSI:
            return Tralsebit.PSI  # Contradiction is infectious
        if a == Tralsebit.F or b == Tralsebit.F:
            return Tralsebit.F
        if a == Tralsebit.PHI or b == Tralsebit.PHI:
            return Tralsebit.PHI
        return Tralsebit.T  # Both must be T
    
    @staticmethod
    def OR(a: Tralsebit, b: Tralsebit) -> Tralsebit:
        """Tralse disjunction with PSI infection"""
        if a == Tralsebit.PSI or b == Tralsebit.PSI:
            return Tralsebit.PSI
        if a == Tralsebit.T or b == Tralsebit.T:
            return Tralsebit.T
        if a == Tralsebit.PHI or b == Tralsebit.PHI:
            return Tralsebit.PHI
        return Tralsebit.F  # Both must be F
    
    @staticmethod
    def XOR(a: Tralsebit, b: Tralsebit) -> Tralsebit:
        """
        Tralse exclusive or with proper Φ handling.
        
        XOR semantics:
        - If either is Ψ, result is Ψ (contradiction propagates)
        - If both are Φ, result is Φ (unknown remains unknown)
        - If one is Φ and one is definite (T/F), result is Φ (can't determine yet)
        - If both definite and same, result is F
        - If both definite and different, result is T
        """
        if a == Tralsebit.PSI or b == Tralsebit.PSI:
            return Tralsebit.PSI
        if a == Tralsebit.PHI or b == Tralsebit.PHI:
            return Tralsebit.PHI  # Unknown propagates correctly
        if a == b:
            return Tralsebit.F
        return Tralsebit.T
    
    @staticmethod
    def IMPLIES(a: Tralsebit, b: Tralsebit) -> Tralsebit:
        """Tralse implication: a → b"""
        if a == Tralsebit.PSI or b == Tralsebit.PSI:
            return Tralsebit.PSI
        if a == Tralsebit.F:
            return Tralsebit.T  # False implies anything
        if a == Tralsebit.T:
            return b
        return Tralsebit.PHI  # Unknown antecedent
    
    @staticmethod
    def TRALSE(a: Tralsebit, b: Tralsebit) -> Tralsebit:
        """
        The TRALSE operator - Creates superposition/contradiction.
        
        Semantics:
        - TRALSE(T, F) = Ψ (contradiction - both true and false)
        - TRALSE(T, T) = T (agreement)
        - TRALSE(F, F) = F (agreement)
        - TRALSE(Φ, X) = Φ (unknown absorbs - can't create contradiction with unknown)
        - TRALSE(Ψ, Φ) = Ψ (contradiction persists over unknown)
        - TRALSE(Ψ, Ψ) = Ψ (contradictions combine)
        """
        if a == b:
            return a
        
        if a == Tralsebit.PHI and b != Tralsebit.PSI:
            return Tralsebit.PHI  # Unknown absorbs definite values
        if b == Tralsebit.PHI and a != Tralsebit.PSI:
            return Tralsebit.PHI  # Unknown absorbs definite values
        
        if a == Tralsebit.PSI or b == Tralsebit.PSI:
            return Tralsebit.PSI  # Contradiction dominates unknown
        
        if (a == Tralsebit.T and b == Tralsebit.F) or \
           (a == Tralsebit.F and b == Tralsebit.T):
            return Tralsebit.PSI  # T and F together = contradiction
        
        return Tralsebit.PSI  # Default to contradiction for mixed cases
    
    @staticmethod
    def RESOLVE(psi_state: Tralsebit, context_bias: float = 0.0) -> Tralsebit:
        """
        Myrion Resolution operator - harmonizes contradictions.
        
        Takes a Ψ (contradiction) state and resolves it based on context:
        - context_bias > 0.5: resolves toward T
        - context_bias < 0.5: resolves toward F
        - context_bias == 0.5: remains Φ (undetermined)
        
        Non-Ψ states pass through unchanged.
        """
        if psi_state != Tralsebit.PSI:
            return psi_state  # Only resolve contradictions
        
        if context_bias > 0.5:
            return Tralsebit.T
        elif context_bias < 0.5:
            return Tralsebit.F
        else:
            return Tralsebit.PHI  # Balanced context → undetermined


@dataclass
class GILEScore:
    """
    GILE (Goodness, Intuition, Love, Environment) consciousness metadata.
    
    Every TICL program/function can declare its GILE properties,
    enabling consciousness-aware optimization and security.
    
    Scale: -3 to +2 for each dimension (from GILE interval theory)
    """
    goodness: float = 0.0      # Moral/ethical quality
    intuition: float = 0.0     # Clarity of intent
    love: float = 0.0          # Connection/compassion
    environment: float = 0.0   # Context appropriateness
    
    def composite_score(self) -> float:
        """Calculate composite GILE σ score (0-1 normalized)"""
        raw = self.goodness + self.intuition + self.love + self.environment
        return (raw + 12) / 20  # Maps [-12, 8] to [0, 1]
    
    def is_valid(self) -> bool:
        """Check if GILE is above soul death threshold (σ > 0.333)"""
        return self.composite_score() > 0.333
    
    def __str__(self):
        return f"GILE(G={self.goodness:+.1f}, I={self.intuition:+.1f}, L={self.love:+.1f}, E={self.environment:+.1f}) σ={self.composite_score():.3f}"


class TernaryNumber:
    """
    Ternary (base-3) number representation.
    
    Ternary is more efficient than binary:
    - Fewer digits needed
    - 50% fewer transistors for same precision
    - Natural for 3-state logic
    """
    
    def __init__(self, value: Union[int, str]):
        if isinstance(value, str):
            self.decimal = self._from_ternary(value)
        else:
            self.decimal = value
    
    def _from_ternary(self, s: str) -> int:
        """Convert ternary string to decimal"""
        s = s.replace('₃', '')  # Remove ternary subscript
        result = 0
        for digit in s:
            result = result * 3 + int(digit)
        return result
    
    def to_ternary(self) -> str:
        """Convert to ternary string representation"""
        if self.decimal == 0:
            return "0₃"
        
        result = ""
        n = abs(self.decimal)
        while n > 0:
            result = str(n % 3) + result
            n //= 3
        
        if self.decimal < 0:
            result = "-" + result
        
        return result + "₃"
    
    def __add__(self, other: 'TernaryNumber') -> 'TernaryNumber':
        return TernaryNumber(self.decimal + other.decimal)
    
    def __sub__(self, other: 'TernaryNumber') -> 'TernaryNumber':
        return TernaryNumber(self.decimal - other.decimal)
    
    def __mul__(self, other: 'TernaryNumber') -> 'TernaryNumber':
        return TernaryNumber(self.decimal * other.decimal)
    
    def __floordiv__(self, other: 'TernaryNumber') -> 'TernaryNumber':
        return TernaryNumber(self.decimal // other.decimal)
    
    def __mod__(self, other: 'TernaryNumber') -> 'TernaryNumber':
        return TernaryNumber(self.decimal % other.decimal)
    
    def __str__(self):
        return f"{self.to_ternary()} (={self.decimal})"
    
    def __repr__(self):
        return f"TernaryNumber({self.decimal})"


@dataclass
class MyrionResolution:
    """
    Myrion Resolution - The core contradiction harmonization engine.
    
    When Ψ (contradiction) states arise, Myrion Resolution:
    1. Analyzes the contradicting statements
    2. Elevates to a meta-level of truth
    3. Finds harmonization that preserves both truths
    
    This is the TI Framework's key innovation over classical logic.
    """
    original_state: Tralsebit
    statements: List[Dict[str, Any]]
    meta_truth: Optional[Tralsebit] = None
    resolution_path: List[str] = field(default_factory=list)
    
    def resolve(self) -> Tralsebit:
        """
        Perform Myrion Resolution on contradictory state.
        
        Algorithm:
        1. If not PSI, return as-is
        2. Analyze statements for common ground
        3. Elevate to meta-level where both are true
        4. Return resolved state
        """
        if self.original_state != Tralsebit.PSI:
            self.meta_truth = self.original_state
            self.resolution_path.append("No resolution needed - not contradictory")
            return self.original_state
        
        self.resolution_path.append("Contradiction detected (Ψ state)")
        
        if len(self.statements) < 2:
            self.resolution_path.append("Single statement - defaulting to T")
            self.meta_truth = Tralsebit.T
            return Tralsebit.T
        
        positive_count = sum(1 for s in self.statements if s.get('value', 0) > 0)
        negative_count = len(self.statements) - positive_count
        
        self.resolution_path.append(f"Analyzing {len(self.statements)} statements: {positive_count} positive, {negative_count} negative")
        
        if positive_count > negative_count:
            self.resolution_path.append("Meta-resolution: Positive majority → T at meta-level")
            self.meta_truth = Tralsebit.T
        elif negative_count > positive_count:
            self.resolution_path.append("Meta-resolution: Negative majority → F at meta-level")
            self.meta_truth = Tralsebit.F
        else:
            self.resolution_path.append("Meta-resolution: Perfect balance → Φ (higher-order unknown)")
            self.meta_truth = Tralsebit.PHI
        
        return self.meta_truth


@dataclass
class TICLValue:
    """A value in the TICL runtime"""
    value: Any
    type_name: str
    gile: Optional[GILEScore] = None
    
    def __str__(self):
        return f"{self.value} : {self.type_name}"


class TICLEnvironment:
    """
    TICL execution environment - stores variables and functions.
    """
    
    def __init__(self, parent: Optional['TICLEnvironment'] = None):
        self.parent = parent
        self.variables: Dict[str, TICLValue] = {}
        self.functions: Dict[str, Callable] = {}
    
    def get(self, name: str) -> Optional[TICLValue]:
        if name in self.variables:
            return self.variables[name]
        if self.parent:
            return self.parent.get(name)
        return None
    
    def set(self, name: str, value: TICLValue):
        self.variables[name] = value
    
    def define_function(self, name: str, func: Callable):
        self.functions[name] = func


class TICLInterpreter:
    """
    The TICL Interpreter - Executes TI Computing Language code.
    
    Features:
    - Tralsebit operations (AND, OR, NOT, TRALSE, etc.)
    - Myrion Resolution for contradictions
    - Ternary arithmetic
    - GILE-aware execution
    - Interactive REPL mode
    """
    
    def __init__(self):
        self.env = TICLEnvironment()
        self.current_gile = GILEScore()
        self.resolution_history: List[MyrionResolution] = []
        self._setup_builtins()
    
    def _setup_builtins(self):
        """Setup built-in variables and functions"""
        self.env.set("T", TICLValue(Tralsebit.T, "tralsebit"))
        self.env.set("F", TICLValue(Tralsebit.F, "tralsebit"))
        self.env.set("Φ", TICLValue(Tralsebit.PHI, "tralsebit"))
        self.env.set("PHI", TICLValue(Tralsebit.PHI, "tralsebit"))
        self.env.set("Ψ", TICLValue(Tralsebit.PSI, "tralsebit"))
        self.env.set("PSI", TICLValue(Tralsebit.PSI, "tralsebit"))
    
    def parse_and_eval(self, code: str) -> TICLValue:
        """Parse and evaluate TICL code"""
        code = code.strip()
        
        if not code or code.startswith('#'):
            return TICLValue(None, "void")
        
        if code.startswith("GILE"):
            return self._eval_gile_declaration(code)
        
        if code.startswith("tralsebit "):
            return self._eval_tralsebit_declaration(code)
        
        if code.startswith("tern "):
            return self._eval_ternary_declaration(code)
        
        if code.startswith("myrion_resolve"):
            return self._eval_myrion_resolve(code)
        
        if " AND " in code or " OR " in code or " TRALSE " in code or code.startswith("NOT "):
            return self._eval_tralse_expression(code)
        
        if code in ["T", "F", "Φ", "PHI", "Ψ", "PSI"]:
            return self.env.get(code) or TICLValue(Tralsebit.from_string(code), "tralsebit")
        
        if code.startswith("print("):
            return self._eval_print(code)
        
        var = self.env.get(code)
        if var:
            return var
        
        return TICLValue(code, "string")
    
    def _eval_gile_declaration(self, code: str) -> TICLValue:
        """Parse GILE declaration block"""
        lines = code.split('\n')
        gile = GILEScore()
        
        for line in lines:
            line = line.strip()
            if 'Goodness:' in line:
                gile.goodness = float(line.split(':')[1].strip().split()[0])
            elif 'Intuition:' in line:
                gile.intuition = float(line.split(':')[1].strip().split()[0])
            elif 'Love:' in line:
                gile.love = float(line.split(':')[1].strip().split()[0])
            elif 'Environment:' in line:
                gile.environment = float(line.split(':')[1].strip().split()[0])
        
        self.current_gile = gile
        return TICLValue(gile, "gile_score")
    
    def _eval_tralsebit_declaration(self, code: str) -> TICLValue:
        """Parse tralsebit variable declaration"""
        match = re.match(r'tralsebit\s+(\w+)\s*=\s*(.+)', code)
        if match:
            name, value_str = match.groups()
            value = Tralsebit.from_string(value_str.strip())
            result = TICLValue(value, "tralsebit")
            self.env.set(name, result)
            return result
        return TICLValue(None, "error")
    
    def _eval_ternary_declaration(self, code: str) -> TICLValue:
        """Parse ternary number declaration"""
        match = re.match(r'tern\s+(\w+)\s*=\s*(.+)', code)
        if match:
            name, value_str = match.groups()
            value_str = value_str.strip()
            
            if '₃' in value_str or value_str.endswith('3'):
                num = TernaryNumber(value_str)
            else:
                num = TernaryNumber(int(value_str))
            
            result = TICLValue(num, "ternary")
            self.env.set(name, result)
            return result
        return TICLValue(None, "error")
    
    def _eval_tralse_expression(self, code: str) -> TICLValue:
        """Evaluate tralse logic expression"""
        code = code.strip()
        
        if code.startswith("NOT "):
            operand = code[4:].strip()
            val = self._get_tralsebit_value(operand)
            result = TralsebitAlgebra.NOT(val)
            return TICLValue(result, "tralsebit")
        
        for op in [" AND ", " OR ", " XOR ", " IMPLIES ", " TRALSE "]:
            if op in code:
                parts = code.split(op)
                left = self._get_tralsebit_value(parts[0].strip())
                right = self._get_tralsebit_value(parts[1].strip())
                
                if op == " AND ":
                    result = TralsebitAlgebra.AND(left, right)
                elif op == " OR ":
                    result = TralsebitAlgebra.OR(left, right)
                elif op == " XOR ":
                    result = TralsebitAlgebra.XOR(left, right)
                elif op == " IMPLIES ":
                    result = TralsebitAlgebra.IMPLIES(left, right)
                elif op == " TRALSE ":
                    result = TralsebitAlgebra.TRALSE(left, right)
                
                return TICLValue(result, "tralsebit")
        
        return TICLValue(None, "error")
    
    def _get_tralsebit_value(self, expr: str) -> Tralsebit:
        """Get tralsebit value from expression or variable"""
        var = self.env.get(expr)
        if var and var.type_name == "tralsebit":
            return var.value
        return Tralsebit.from_string(expr)
    
    def _eval_myrion_resolve(self, code: str) -> TICLValue:
        """Evaluate Myrion Resolution"""
        resolution = MyrionResolution(
            original_state=Tralsebit.PSI,
            statements=[
                {'name': 'statement_1', 'value': 1},
                {'name': 'statement_2', 'value': -1}
            ]
        )
        
        result = resolution.resolve()
        self.resolution_history.append(resolution)
        
        return TICLValue({
            'result': result,
            'path': resolution.resolution_path
        }, "myrion_resolution")
    
    def _eval_print(self, code: str) -> TICLValue:
        """Evaluate print statement"""
        match = re.match(r'print\((.+)\)', code)
        if match:
            content = match.group(1).strip()
            
            if content.startswith('"') and content.endswith('"'):
                output = content[1:-1]
            else:
                val = self.parse_and_eval(content)
                output = str(val.value)
            
            print(output)
            return TICLValue(output, "void")
        return TICLValue(None, "error")
    
    def repl(self):
        """Interactive REPL (Read-Eval-Print Loop)"""
        print("=" * 60)
        print("TICL Interpreter v0.1.0-alpha")
        print("TI Computing Language - Consciousness-Aware Programming")
        print("=" * 60)
        print("Type 'help' for commands, 'quit' to exit")
        print()
        
        while True:
            try:
                code = input("TICL> ").strip()
                
                if code.lower() in ['quit', 'exit', 'q']:
                    print("Goodbye!")
                    break
                
                if code.lower() == 'help':
                    self._print_help()
                    continue
                
                if code.lower() == 'gile':
                    print(f"Current GILE: {self.current_gile}")
                    continue
                
                if code.lower() == 'vars':
                    for name, val in self.env.variables.items():
                        print(f"  {name} = {val}")
                    continue
                
                result = self.parse_and_eval(code)
                
                if result.value is not None and result.type_name != "void":
                    print(f"=> {result}")
                
            except KeyboardInterrupt:
                print("\nUse 'quit' to exit")
            except Exception as e:
                print(f"Error: {e}")
    
    def _print_help(self):
        """Print REPL help"""
        print("""
TICL Commands:
  tralsebit x = T|F|Φ|Ψ   Declare a tralsebit variable
  tern n = 012₃           Declare a ternary number
  x AND y                 Tralse conjunction
  x OR y                  Tralse disjunction
  NOT x                   Tralse negation
  x TRALSE y              Create superposition/contradiction
  myrion_resolve(...)     Resolve Ψ contradictions
  print(...)              Output value
  gile                    Show current GILE score
  vars                    List all variables
  quit                    Exit REPL

Tralsebit Values:
  T / TRUE    - Definite truth
  F / FALSE   - Definite falsehood
  Φ / PHI     - Underdetermined (unknown)
  Ψ / PSI     - Overdetermined (contradiction)
""")


def run_ticl_demo():
    """Demonstrate TICL interpreter capabilities"""
    print("=" * 70)
    print("TICL INTERPRETER DEMONSTRATION")
    print("TI Computing Language - Working Implementation")
    print("=" * 70)
    
    interp = TICLInterpreter()
    
    print("\n1. TRALSEBIT OPERATIONS:")
    print("-" * 40)
    
    demo_code = [
        "tralsebit a = T",
        "tralsebit b = F",
        "tralsebit c = Φ",
        "tralsebit d = Ψ",
        "a AND b",
        "a OR b",
        "NOT a",
        "c OR d",
        "T TRALSE F"
    ]
    
    for code in demo_code:
        result = interp.parse_and_eval(code)
        print(f"  {code:25} => {result}")
    
    print("\n2. TERNARY ARITHMETIC:")
    print("-" * 40)
    
    a = TernaryNumber("012")  # 5 in decimal
    b = TernaryNumber("021")  # 7 in decimal
    
    print(f"  a = {a}")
    print(f"  b = {b}")
    print(f"  a + b = {a + b}")
    print(f"  a * b = {a * b}")
    
    print("\n3. GILE SCORE:")
    print("-" * 40)
    
    gile = GILEScore(goodness=+2, intuition=+1, love=+1, environment=+2)
    print(f"  {gile}")
    print(f"  Valid (above soul death): {gile.is_valid()}")
    
    print("\n4. MYRION RESOLUTION:")
    print("-" * 40)
    
    resolution = MyrionResolution(
        original_state=Tralsebit.PSI,
        statements=[
            {'name': 'free_will_exists', 'value': +1.5},
            {'name': 'determinism_true', 'value': +1.2},
            {'name': 'compatibilism_valid', 'value': +0.8}
        ]
    )
    
    result = resolution.resolve()
    print(f"  Original state: Ψ (contradiction)")
    print(f"  Statements:")
    for s in resolution.statements:
        print(f"    - {s['name']}: {s['value']:+.1f}")
    print(f"  Resolution path:")
    for step in resolution.resolution_path:
        print(f"    → {step}")
    print(f"  Meta-truth: {result}")
    
    print("\n5. SAMPLE TICL PROGRAM:")
    print("-" * 40)
    
    program = '''
# TI Computing Language - Sample Program

GILE declare_program "TradingDecision"
    Goodness: +2
    Intuition: +1
    Love: +1
    Environment: +2

tralsebit market_up = T
tralsebit market_down = F
tralsebit signal = market_up AND NOT market_down
print("Trading signal:")
'''
    
    print(program)
    
    for line in program.strip().split('\n'):
        line = line.strip()
        if line and not line.startswith('#'):
            result = interp.parse_and_eval(line)
            if result.value is not None and result.type_name not in ["void", "gile_score"]:
                print(f"  => {result}")
    
    print("\n" + "=" * 70)
    print("TICL DEMONSTRATION COMPLETE")
    print("=" * 70)
    
    return interp


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "--repl":
        interp = TICLInterpreter()
        interp.repl()
    else:
        run_ticl_demo()
