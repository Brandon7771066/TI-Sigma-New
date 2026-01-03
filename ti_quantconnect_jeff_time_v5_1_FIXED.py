"""
TI FRAMEWORK V5.1: JEFF TIME 3D - FIXED
========================================
Keeps TI naming, restores V3's winning formula

WHAT WENT WRONG IN V5:
- clarity_factor DAMPENED high-volatility signals (killed 2020-2021 gains)
- Surprise bonus added noise
- Fixed weights removed V3's adaptive learning

V5.1 FIX:
- Remove clarity_factor (volatility can be good!)
- Remove surprise bonus (keep it simple)
- Restore V3's simpler formulas
- Keep TI naming (τ_I, τ_J, τ_C, L)

V3 BASELINE: 277.76%
TARGET: Match or beat V3

COPY EVERYTHING BELOW FOR QUANTCONNECT:
"""
