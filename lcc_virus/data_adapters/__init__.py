"""lcc_virus.data_adapters — free-data loaders for LCC-Virus experiments.

Implemented:
    yfinance_adapter — daily/monthly close prices for any yfinance symbol(s)

Stubbed (Pass-50+):
    fred_csv_adapter — direct FRED public-CSV fetch (no pandas-datareader needed)
    gdelt_adapter    — GDELT GKG event tone aggregator
    dandi_adapter    — DANDI archive neural data loader
"""
from __future__ import annotations
__all__ = ["yfinance_adapter"]
