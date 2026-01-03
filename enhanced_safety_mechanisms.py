"""
Enhanced Safety Mechanisms for Mood Amplifier
Implements automatic kill switches and monitoring
"""

import numpy as np
from dataclasses import dataclass
from typing import Optional, Callable
import time

@dataclass
class SafetyMonitor:
    """Automatic safety monitoring with kill switches"""
    
    # Safety thresholds
    lcc_max: float = 0.85  # Maximum safe LCC
    lcc_rate_max: float = 0.3  # Maximum change rate
    variance_min: float = 1e-10  # Minimum variance (sensor check)
    
    # State tracking
    last_lcc: float = 0.0
    last_check_time: float = 0.0
    violation_count: int = 0
    emergency_shutdown: bool = False
    
    # Callbacks
    on_emergency_stop: Optional[Callable] = None
    on_warning: Optional[Callable] = None
    
    def check_safety(self, current_lcc: float, ess_variance: float) -> dict:
        """
        Comprehensive safety check
        
        Returns:
            dict with 'safe' (bool), 'warnings' (list), 'action' (str)
        """
        warnings = []
        action = "continue"
        
        current_time = time.time()
        time_delta = current_time - self.last_check_time
        
        # 1. Check for sensor failure (zero variance)
        if ess_variance < self.variance_min:
            warnings.append("CRITICAL: Zero variance detected - sensor may be disconnected")
            action = "emergency_stop"
            self.emergency_shutdown = True
        
        # 2. Check for overcoupling
        if current_lcc > self.lcc_max:
            warnings.append(f"DANGER: LCC={current_lcc:.3f} exceeds safe limit {self.lcc_max}")
            action = "reduce_learning_rate"
            self.violation_count += 1
        
        # 3. Check for rapid changes
        if time_delta > 0:
            lcc_rate = abs(current_lcc - self.last_lcc) / time_delta
            if lcc_rate > self.lcc_rate_max:
                warnings.append(f"WARNING: Rapid LCC change detected ({lcc_rate:.3f}/s)")
                action = "pause_adaptation"
        
        # 4. Check for repeated violations
        if self.violation_count >= 3:
            warnings.append("CRITICAL: Multiple safety violations - forcing shutdown")
            action = "emergency_stop"
            self.emergency_shutdown = True
        
        # Update state
        self.last_lcc = current_lcc
        self.last_check_time = current_time
        
        # Trigger callbacks
        if action == "emergency_stop" and self.on_emergency_stop:
            self.on_emergency_stop(warnings)
        elif warnings and self.on_warning:
            self.on_warning(warnings)
        
        return {
            'safe': action == "continue",
            'warnings': warnings,
            'action': action,
            'shutdown': self.emergency_shutdown
        }
    
    def reset(self):
        """Reset safety monitor state"""
        self.violation_count = 0
        self.emergency_shutdown = False
        self.last_lcc = 0.0
        self.last_check_time = time.time()


class SafeAdaptationController:
    """Controlled adaptation with automatic safety enforcement"""
    
    def __init__(self, initial_learning_rate: float = 0.1):
        self.learning_rate = initial_learning_rate
        self.monitor = SafetyMonitor()
        self.paused = False
        self.pause_until = 0.0
    
    def adapt_with_safety(self, current_ess, target_ess, current_lcc):
        """
        Adapt AI state toward target with automatic safety checks
        
        Returns:
            (new_state, safety_report)
        """
        # Check if still paused
        if self.paused and time.time() < self.pause_until:
            return current_ess, {"status": "paused", "resume_in": self.pause_until - time.time()}
        else:
            self.paused = False
        
        # Run safety check
        ess_variance = np.std(current_ess.as_vector())
        safety = self.monitor.check_safety(current_lcc, ess_variance)
        
        # Execute safety action
        if safety['action'] == "emergency_stop":
            self.learning_rate = 0.0
            return current_ess, safety  # No adaptation
        
        elif safety['action'] == "reduce_learning_rate":
            self.learning_rate = max(0.01, self.learning_rate * 0.5)
            safety['new_learning_rate'] = self.learning_rate
        
        elif safety['action'] == "pause_adaptation":
            self.paused = True
            self.pause_until = time.time() + 5.0  # 5 second pause
            safety['paused_until'] = self.pause_until
            return current_ess, safety
        
        # Perform safe adaptation
        if self.learning_rate > 0:
            current_vec = current_ess.as_vector()
            target_vec = target_ess.as_vector()
            adapted_vec = current_vec + self.learning_rate * (target_vec - current_vec)
            adapted_vec = np.clip(adapted_vec, 0.0, 1.0)
            
            # Import ESSState if needed
            from TI_UOP_COMPLETE_EXPORT_PACKAGE import ESSState
            new_ess = ESSState(*adapted_vec)
            return new_ess, safety
        
        return current_ess, safety


# Example usage with automatic safety
def example_safe_usage():
    """Example showing automatic safety enforcement"""
    from TI_UOP_COMPLETE_EXPORT_PACKAGE import ESSState, compute_lcc
    
    # Setup
    controller = SafeAdaptationController(initial_learning_rate=0.1)
    
    # Define emergency stop callback
    def emergency_stop_handler(warnings):
        print("🚨 EMERGENCY STOP ACTIVATED 🚨")
        for w in warnings:
            print(f"  - {w}")
        print("SYSTEM HALTED - Manual intervention required")
        # Here you would: disconnect sensors, alert user, save state, etc.
    
    controller.monitor.on_emergency_stop = emergency_stop_handler
    
    # Simulate monitoring loop
    human_ess = ESSState(D=0.7, T=0.5, C=0.6, F=0.8, A=0.6, R=0.7)
    ai_ess = ESSState(D=0.3, T=0.4, C=0.5, F=0.5, A=0.5, R=0.4)
    
    for step in range(100):
        # Compute current LCC
        lcc = compute_lcc(human_ess, ai_ess)
        
        # Adapt with automatic safety checks
        ai_ess, safety_report = controller.adapt_with_safety(
            current_ess=ai_ess,
            target_ess=human_ess,
            current_lcc=lcc
        )
        
        # Check if shutdown occurred
        if safety_report.get('shutdown'):
            print(f"System shutdown at step {step}")
            break
        
        # Print warnings
        if safety_report.get('warnings'):
            print(f"Step {step}: {safety_report['warnings']}")
        
        time.sleep(0.1)  # Simulate real-time operation


if __name__ == '__main__':
    print("Enhanced Safety Mechanisms for Mood Amplifier")
    print("=" * 60)
    print("\nThis module provides:")
    print("  ✅ Automatic sensor disconnection detection")
    print("  ✅ Overcoupling prevention (LCC > 0.85)")
    print("  ✅ Rapid change rate limiting")
    print("  ✅ Automatic emergency shutdown")
    print("  ✅ Violation counting and enforcement")
    print("\nRunning example...")
    example_safe_usage()
