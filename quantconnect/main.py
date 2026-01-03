# main.py
from AlgorithmImports import *
import numpy as np
import gsa_core as core

class TI_GSA_QC_Bridge(QCAlgorithm):
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 1)
        self.SetCash(100000)

        tickers = ["SPY", "QQQ", "AAPL", "MSFT", "GOOGL", "NVDA", "TSLA", "META", "AMZN"]
        self.symbols = [self.AddEquity(t, Resolution.Daily).Symbol for t in tickers]

        self.lb_short = 7
        self.lb_long = 30
        self.window = 80

        self.state = {}
        for s in self.symbols:
            self.state[s] = {
                "prices": RollingWindow[float](self.window),
                "returns": RollingWindow[float](self.window),
                "pd_hist": [],
                "c_hist": []
            }

        self.max_pos = 0.12
        self.top_k = 4

        self.SetWarmUp(self.window, Resolution.Daily)
        self.Schedule.On(self.DateRules.EveryDay("SPY"),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

    def OnData(self, data: Slice):
        for s in self.symbols:
            sec = self.Securities[s]
            if not sec.HasData or sec.Price <= 0:
                continue

            st = self.state[s]
            prev_price = st["prices"][0] if st["prices"].Count > 0 else None

            st["prices"].Add(float(sec.Price))
            if prev_price is not None and prev_price > 0:
                r = (float(sec.Price) / float(prev_price) - 1.0) * 100.0
                st["returns"].Add(float(r))
            else:
                st["returns"].Add(0.0)

    def Rebalance(self):
        if self.IsWarmingUp:
            return

        signals = []
        for s in self.symbols:
            st = self.state[s]
            if st["prices"].Count < self.lb_long or st["returns"].Count < self.lb_long:
                continue

            prices = np.array([st["prices"][i] for i in range(st["prices"].Count)][::-1], dtype=float)
            rets   = np.array([st["returns"][i] for i in range(st["returns"].Count)][::-1], dtype=float)

            xi = core.compute_xi(prices, rets, self.lb_short, self.lb_long)
            st["pd_hist"].append(xi["pd"])
            st["c_hist"].append(xi["C"])
            st["pd_hist"] = st["pd_hist"][-120:]
            st["c_hist"]  = st["c_hist"][-120:]

            regime, reg_conf = core.classify_regime(st["pd_hist"], st["c_hist"], rets)

            score = xi["pd"]

            if regime == core.MarketRegime.FRACTURE:
                score = -10

            signals.append((s, score, regime, reg_conf, xi))

        if not signals:
            return

        signals.sort(key=lambda x: x[1], reverse=True)
        buys = [x for x in signals if x[1] > 0.3][:self.top_k]

        selected = set([b[0] for b in buys])
        for kvp in self.Portfolio:
            sym = kvp.Key
            if kvp.Value.Invested and sym not in selected:
                self.Liquidate(sym, "Not in top set")

        if len(buys) == 0:
            return

        base_w = min(self.max_pos, 1.0 / len(buys))
        for (s, score, regime, reg_conf, xi) in buys:
            w = base_w * min(1.0, max(0.25, reg_conf))
            self.SetHoldings(s, w)

        self.Log(f"Rebalance: selected={[self.SymbolCache.GetTicker(s) for s in selected]}")
