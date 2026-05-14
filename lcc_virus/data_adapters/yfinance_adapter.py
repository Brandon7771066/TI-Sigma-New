"""yfinance free-data adapter for Program A dyads.

Returns a pandas DataFrame of close prices, indexed by trading day,
with one column per requested symbol. Auto-adjusted (split/div).
"""
from __future__ import annotations

from typing import Iterable
import pandas as pd
import yfinance as yf


def fetch_closes(symbols: Iterable[str], start: str, end: str) -> pd.DataFrame:
    syms = list(symbols)
    df = yf.download(syms, start=start, end=end, progress=False, auto_adjust=True)["Close"]
    if isinstance(df, pd.Series):
        df = df.to_frame(name=syms[0])
    return df.dropna()
