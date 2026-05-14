"""FRED public-CSV adapter — fetch any FRED series ID without an API key
or `pandas-datareader` dependency.

Uses the public CSV endpoint:
    https://fred.stlouisfed.org/graph/fredgraph.csv?id=SERIES_ID

This unblocks Pass-50 dyad #6 UMCSENT x SPY (the Program A primary
dyad) without installing `pandas-datareader` (which currently fails to
install due to the broken `github` build dependency in the workspace).
"""
from __future__ import annotations

import io
import urllib.request

import pandas as pd

FRED_CSV_URL = "https://fred.stlouisfed.org/graph/fredgraph.csv?id={series_id}"


def fetch_series(series_id: str, start: str | None = None, end: str | None = None) -> pd.Series:
    url = FRED_CSV_URL.format(series_id=series_id.upper())
    with urllib.request.urlopen(url, timeout=30) as resp:
        raw = resp.read().decode("utf-8")
    df = pd.read_csv(io.StringIO(raw))
    # FRED CSVs have columns ['DATE' or 'observation_date', SERIES_ID]; "."
    # marks missing observations.
    date_col = next((c for c in df.columns if c.lower() in ("date", "observation_date")), df.columns[0])
    df[date_col] = pd.to_datetime(df[date_col])
    df = df.set_index(date_col)
    s = df[series_id.upper()] if series_id.upper() in df.columns else df.iloc[:, 0]
    s = pd.to_numeric(s.replace({".": None}), errors="coerce").dropna()
    s.name = series_id.upper()
    if start is not None:
        s = s[s.index >= pd.to_datetime(start)]
    if end is not None:
        s = s[s.index <= pd.to_datetime(end)]
    return s
