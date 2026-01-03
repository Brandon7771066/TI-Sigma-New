# qc_guardian.py
"""
QC-GUARDIAN v6
Causal, informational, and crowding-aware QuantConnect research engine.

TI Framework Integration:
- Prioritizes CAUSE over CORRELATION (aligns with Myrion Resolution)
- Detects crowded/retail alpha (avoids Dark Pool exploitation)
- Information density check (follows GILE optimization principle)
"""

import os, re, time, subprocess, shutil, json
import datetime
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler

ROOT = "."
PY_EXT = ".py"

# ----------------------------------------
# Utilities
# ----------------------------------------
def run(cmd, label):
    print(f"\n--- {label} ---")
    subprocess.run(cmd, check=False)

def read_all_code():
    code = ""
    for root, _, files in os.walk(ROOT):
        for f in files:
            if f.endswith(PY_EXT):
                with open(os.path.join(root, f), "r", encoding="utf-8", errors="ignore") as file:
                    code += file.read() + "\n"
    return code

# ----------------------------------------
# Causality Analysis (TI: Cause > Correlation)
# ----------------------------------------
CAUSE_KEYWORDS = ["Volume", "ATR", "Volatility", "Liquidity", "Spread"]
CORRELATE_KEYWORDS = ["RSI", "SMA", "EMA", "MACD", "Stochastic"]

def causality_checks(code, warnings):
    cause_hits = sum(code.count(k) for k in CAUSE_KEYWORDS)
    corr_hits = sum(code.count(k) for k in CORRELATE_KEYWORDS)

    if corr_hits > cause_hits * 3:
        warnings.append("Causality risk: strategy dominated by correlation indicators")

# ----------------------------------------
# Redundant Alpha Detection
# ----------------------------------------
def redundancy_checks(code, warnings):
    indicators = ["RSI", "SMA", "EMA", "MACD", "ROC", "Momentum"]
    used = [i for i in indicators if i in code]

    if len(used) >= 4:
        warnings.append("Redundant alpha risk: multiple overlapping indicators")

# ----------------------------------------
# Information Density Estimate (TI: GILE optimization)
# ----------------------------------------
def information_density(code, warnings):
    logic_lines = len([l for l in code.splitlines() if "if " in l])
    indicator_calls = sum(code.count(i) for i in ["RSI", "SMA", "EMA", "MACD", "ATR"])

    if indicator_calls > logic_lines * 2:
        warnings.append("Low information density: many signals, little logic")

# ----------------------------------------
# Alpha Crowding Inference (TI: Avoid retail traps)
# ----------------------------------------
CROWDED_PATTERNS = ["RSI(", "SMA(", "EMA(", "MeanReversion", "Momentum"]

def crowding_checks(code, warnings):
    crowd_score = sum(code.count(p) for p in CROWDED_PATTERNS)
    if crowd_score > 8:
        warnings.append("Crowding risk: strategy resembles common retail alpha")

# ----------------------------------------
# Meta-Strategy Fragility
# ----------------------------------------
def fragility_checks(code, warnings):
    if code.count("if ") < 2:
        warnings.append("Fragility risk: single decision path")

    if "else" not in code:
        warnings.append("Fragility risk: no contingency logic")

# ----------------------------------------
# v5 Checks (Preserved from previous version)
# ----------------------------------------
def alpha_decay_checks(code, warnings):
    if code.count("Optimize") > 0:
        warnings.append("Alpha decay risk: optimization dependency detected")

    fast_indicators = ["EMA(", "ROC(", "Momentum("]
    if sum(code.count(i) for i in fast_indicators) > 5:
        warnings.append("Alpha decay risk: excessive fast-reacting indicators")

def regime_checks(code, warnings):
    if "ATR" not in code and "Volatility" not in code:
        warnings.append("Regime risk: no volatility awareness detected")

    if "Trend" in code and "Range" not in code:
        warnings.append("Regime risk: trend-only logic may fail in chop")

def walk_forward_checks(code, warnings):
    static_params = re.findall(r"=\s*\d+\.?\d*", code)
    if len(static_params) > 25 and "RollingWindow" not in code:
        warnings.append("Walk-forward risk: many static parameters without adaptation")

def slippage_checks(code, warnings):
    if "MarketOrder" in code and "SlippageModel" not in code:
        warnings.append("Execution risk: MarketOrder without slippage model")

    if code.count("MarketOrder") > 20:
        warnings.append("Execution risk: high turnover without liquidity checks")

def scaling_checks(code, warnings):
    if "SetHoldings" in code:
        percents = re.findall(r"SetHoldings\([^,]+,\s*(0\.\d+|1\.0)", code)
        if percents and float(percents[0]) > 0.25:
            warnings.append("Scaling risk: large capital concentration")

    if "SetLeverage" in code:
        lev = re.findall(r"SetLeverage\((\d+)", code)
        if lev and int(lev[0]) > 2:
            warnings.append("Scaling risk: leverage amplifies slippage at scale")

# ----------------------------------------
# Verdict Engine (v6 - TI Enhanced)
# ----------------------------------------
def verdict(score, warnings):
    severe = len([w for w in warnings if "risk" in w.lower()])

    if score >= 92 and severe <= 2:
        return "DEPLOYABLE"
    if score >= 80:
        return "RESEARCH-ONLY"
    if score >= 70:
        return "THEORETICAL-ONLY"
    if score >= 60:
        return "ILLUSORY-ALPHA"
    return "REJECT — NON-CAUSAL"

# ----------------------------------------
# Full Validation
# ----------------------------------------
def validate_all():
    code = read_all_code()
    warnings = []
    score = 100

    # v6 New Checks
    causality_checks(code, warnings)
    redundancy_checks(code, warnings)
    information_density(code, warnings)
    crowding_checks(code, warnings)
    fragility_checks(code, warnings)
    
    # v5 Preserved Checks
    alpha_decay_checks(code, warnings)
    regime_checks(code, warnings)
    walk_forward_checks(code, warnings)
    slippage_checks(code, warnings)
    scaling_checks(code, warnings)

    score -= len(warnings) * 5
    score = max(score, 0)

    final_verdict = verdict(score, warnings)

    print("\n--- QC-GUARDIAN v6 FINAL REPORT ---")
    print(f"Score: {score}/100")
    print(f"Verdict: {final_verdict}")

    for w in warnings:
        print(f"⚠️  {w}")

    report = {
        "score": score,
        "verdict": final_verdict,
        "warnings": warnings,
        "timestamp": datetime.datetime.utcnow().isoformat()
    }

    with open("QC_V6_FINAL_REPORT.json", "w") as f:
        json.dump(report, f, indent=2)

    run(["ruff", "check", "."], "Ruff Lint")
    run(["pyright"], "Pyright Type Check")

    if shutil.which("lean"):
        run(["lean", "backtest", "."], "Lean Backtest")

# ----------------------------------------
# Watcher
# ----------------------------------------
class Watcher(FileSystemEventHandler):
    def on_modified(self, event):
        src_path = str(event.src_path)
        if not event.is_directory and src_path.endswith(PY_EXT):
            print("\n[QC-GUARDIAN v6] Change detected — re-evaluating")
            validate_all()

def main():
    print("\n[QC-GUARDIAN v6] CAUSAL + INFORMATION MODE ACTIVE\n")
    print("TI Framework Integration:")
    print("  - Cause > Correlation (Myrion Resolution)")
    print("  - Crowding Detection (Dark Pool avoidance)")
    print("  - Information Density (GILE optimization)")
    print()
    observer = Observer()
    observer.schedule(Watcher(), ROOT, recursive=True)
    observer.start()
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        observer.stop()
    observer.join()

if __name__ == "__main__":
    main()
