from AlgorithmImports import *
import numpy as np

class TIFrameworkGTFEv6Algorithm(QCAlgorithm):
    """
    GTFE V6: PRESENT MOMENT EMBODIMENT
    
    PHILOSOPHICAL CORRECTIONS INTEGRATED:
    
    1. JEFF MOMENT = ALL WEIGHT
       The present is all that exists. "Past" = memories NOW, "Future" = predictions NOW.
       All temporal dimensions collapse into the present observation.
    
    2. t1, t2, t3 = ASPECTS OF PRESENT (Not Past/Present/Future!)
       - t1: POTENTIAL aspect (what COULD happen based on current state)
       - t2: ACTUALIZED aspect (what IS happening now)
       - t3: CONTEXTUAL aspect (the present environment/conditions)
       All three are evaluated NOW, representing different facets of the present moment.
    
    3. DYNAMIC WEIGHTS (No Constant Priors!)
       Weights shift based on what's working best IN THE PRESENT.
       Wu Wei: The algorithm embodies the present and shifts gently as conditions change.
       "If you're doing everything right in the present, you don't need to worry about the future."
    
    4. SACRED INTERVAL (-0.666, 0.333) = INDETERMINATE ZONE (Tralse)
       - Below -0.666: FALSE
       - Above 0.333: TRUE  
       - Inside interval: TRALSE (indeterminate)
    
    5. MR (Myrion Resolution) = Resolves contradictions using PD values directly
    
    6. LCC (Local Consciousness Correlation) = Synchronization via correlation (0.42+ threshold)
       MR and LCC are SEPARATE processes!
    
    The algorithm doesn't PREDICT - it EMBODIES the present and shifts gently over time.
    """
    
    def Initialize(self):
        self.SetStartDate(2020, 1, 1)
        self.SetEndDate(2024, 12, 31)
        self.SetCash(100000)
        
        self.SACRED_INTERVAL_MIN = -0.666
        self.SACRED_INTERVAL_MAX = 0.333
        self.TRUE_THRESHOLD = self.SACRED_INTERVAL_MAX
        self.FALSE_THRESHOLD = self.SACRED_INTERVAL_MIN
        self.LCC_MINIMUM = 0.42
        self.GILE_GREAT = 1.5
        self.GILE_GOOD = 0.3
        self.GILE_BAD = -0.3
        self.GILE_TERRIBLE = -1.5
        self.ULTRA_GREAT_THRESHOLD = 20.0
        self.ULTRA_TERRIBLE_THRESHOLD = -10.0
        self.GREAT_THRESHOLD = 5.0
        self.TERRIBLE_THRESHOLD = -5.0
        self.POTENTIAL_LOOKBACK = 3
        self.CONTEXT_SHORT = 20
        self.CONTEXT_LONG = 50
        self.max_position = 0.15
        
        self.symbols = [
            self.AddEquity("SPY", Resolution.Daily).Symbol,
            self.AddEquity("QQQ", Resolution.Daily).Symbol,
            self.AddEquity("AAPL", Resolution.Daily).Symbol,
            self.AddEquity("MSFT", Resolution.Daily).Symbol,
            self.AddEquity("GOOGL", Resolution.Daily).Symbol,
            self.AddEquity("TSLA", Resolution.Daily).Symbol,
            self.AddEquity("NVDA", Resolution.Daily).Symbol,
            self.AddEquity("AMD", Resolution.Daily).Symbol,
            self.AddEquity("META", Resolution.Daily).Symbol,
            self.AddEquity("AMZN", Resolution.Daily).Symbol,
        ]
        
        self.price_history = {symbol: [] for symbol in self.symbols}
        self.aspect_efficacy = {symbol: {'potential': [], 'actualized': [], 'contextual': []} for symbol in self.symbols}
        self.max_history = 60
        self.efficacy_window = 10
        self.SetWarmup(60, Resolution.Daily)
        self.Schedule.On(self.DateRules.EveryDay(), self.TimeRules.AfterMarketOpen("SPY", 30), self.PresentMomentRebalance)
        self.trade_count = 0
        self.winning_trades = 0
        self.lcc_synchronizations = 0
        
    def price_to_gile(self, pct_change):
        if pct_change > self.ULTRA_GREAT_THRESHOLD:
            return float(2.0 + np.log1p((pct_change - self.ULTRA_GREAT_THRESHOLD) / 20) * 0.5)
        elif pct_change < self.ULTRA_TERRIBLE_THRESHOLD:
            return float(-3.0 - np.log1p((abs(pct_change) - abs(self.ULTRA_TERRIBLE_THRESHOLD)) / 10) * 0.5)
        elif pct_change > self.GREAT_THRESHOLD:
            return float(1.5 + (pct_change - 5) / 15 * 0.5)
        elif pct_change < self.TERRIBLE_THRESHOLD:
            return float(-3.0 + (pct_change + 10) / 5 * 1.5)
        elif pct_change > self.SACRED_INTERVAL_MAX:
            return float(0.3 + (pct_change - 0.333) / 4.667 * 1.2)
        elif pct_change < self.SACRED_INTERVAL_MIN:
            return float(-1.5 + (pct_change + 5) / 4.334 * 1.2)
        else:
            return float((pct_change / 0.666) * 0.3) if pct_change < 0 else float((pct_change / 0.333) * 0.3)
    
    def calculate_potential_aspect(self, symbol):
        history = self.price_history.get(symbol, [])
        if len(history) < self.POTENTIAL_LOOKBACK:
            return 0.0
        recent = history[-self.POTENTIAL_LOOKBACK:]
        momentum = (recent[-1] - recent[0]) / recent[0] * 100 if recent[0] != 0 else 0
        returns = np.diff(recent) / recent[:-1] * 100 if len(recent) > 1 else [0]
        volatility = float(np.std(returns)) if len(returns) > 1 else 0.0
        return float(np.clip(self.price_to_gile(momentum) * (1 + volatility * 0.1), -3, 3))
    
    def calculate_actualized_aspect(self, symbol):
        history = self.price_history.get(symbol, [])
        if len(history) < 2:
            return 0.0
        today_change = (history[-1] - history[-2]) / history[-2] * 100 if history[-2] != 0 else 0
        return float(self.price_to_gile(today_change))
    
    def calculate_contextual_aspect(self, symbol):
        history = self.price_history.get(symbol, [])
        if len(history) < self.CONTEXT_LONG:
            return 0.0
        sma_short = float(np.mean(history[-self.CONTEXT_SHORT:]))
        sma_long = float(np.mean(history[-self.CONTEXT_LONG:]))
        trend_divergence = (sma_short - sma_long) / sma_long * 100 if sma_long != 0 else 0
        price_position = (history[-1] - sma_long) / sma_long * 100 if sma_long != 0 else 0
        return float(self.price_to_gile((trend_divergence + price_position) / 2))
    
    def calculate_dynamic_weights(self, symbol):
        efficacy = self.aspect_efficacy.get(symbol, {})
        potential_eff = efficacy.get('potential', [])
        actualized_eff = efficacy.get('actualized', [])
        contextual_eff = efficacy.get('contextual', [])
        
        if len(potential_eff) < 3 or len(actualized_eff) < 3 or len(contextual_eff) < 3:
            return {'potential': 0.33, 'actualized': 0.34, 'contextual': 0.33}
        
        pot_score = float(np.mean(potential_eff[-self.efficacy_window:])) if potential_eff else 0
        act_score = float(np.mean(actualized_eff[-self.efficacy_window:])) if actualized_eff else 0
        ctx_score = float(np.mean(contextual_eff[-self.efficacy_window:])) if contextual_eff else 0
        
        pot_score = max(pot_score, 0.01)
        act_score = max(act_score, 0.01)
        ctx_score = max(ctx_score, 0.01)
        
        total = pot_score + act_score + ctx_score
        if total == 0:
            return {'potential': 0.33, 'actualized': 0.34, 'contextual': 0.33}
        
        return {
            'potential': float(pot_score / total),
            'actualized': float(act_score / total),
            'contextual': float(ctx_score / total)
        }
    
    def update_aspect_efficacy(self, symbol, aspect_name, signal_value, actual_outcome):
        if aspect_name not in self.aspect_efficacy[symbol]:
            self.aspect_efficacy[symbol][aspect_name] = []
        efficacy = 1.0 if (signal_value > 0 and actual_outcome > 0) or (signal_value < 0 and actual_outcome < 0) else 0.0
        if signal_value != 0:
            magnitude_match = min(abs(signal_value), abs(actual_outcome)) / max(abs(signal_value), abs(actual_outcome), 0.01)
            efficacy *= magnitude_match
        self.aspect_efficacy[symbol][aspect_name].append(efficacy)
        if len(self.aspect_efficacy[symbol][aspect_name]) > self.efficacy_window * 2:
            self.aspect_efficacy[symbol][aspect_name] = self.aspect_efficacy[symbol][aspect_name][-self.efficacy_window * 2:]
    
    def myrion_resolution(self, potential_pd, actualized_pd, contextual_pd):
        aspects = [potential_pd, actualized_pd, contextual_pd]
        positive = [a for a in aspects if a > 0]
        negative = [a for a in aspects if a < 0]
        neutral = [a for a in aspects if a == 0]
        
        if len(positive) == 3 or len(negative) == 3:
            combined_pd = float(np.mean(aspects))
            return {'status': 'ALIGNED', 'pd': combined_pd, 'resolved': combined_pd}
        
        if len(neutral) == 3:
            return {'status': 'NEUTRAL', 'pd': 0.0, 'resolved': 0.0}
        
        if len(positive) > 0 and len(negative) > 0:
            pos_avg = float(np.mean(positive))
            neg_avg = float(np.mean(negative))
            net_pd = pos_avg + neg_avg
            if abs(pos_avg) > abs(neg_avg):
                resolved = net_pd * 0.75
                status = 'POSITIVE_DOMINANT'
            elif abs(neg_avg) > abs(pos_avg):
                resolved = net_pd * 0.75
                status = 'NEGATIVE_DOMINANT'
            else:
                resolved = 0.0
                status = 'BALANCED_CONFLICT'
            return {'status': status, 'pd': net_pd, 'resolved': float(resolved)}
        
        combined_pd = float(np.mean([a for a in aspects if a != 0])) if any(a != 0 for a in aspects) else 0.0
        return {'status': 'PARTIAL', 'pd': combined_pd, 'resolved': combined_pd}
    
    def calculate_lcc(self, symbol):
        if len(self.price_history.get(symbol, [])) < 21:
            return {'correlation': 0.0, 'synchronized': False}
        sym_history = self.price_history[symbol][-21:]
        sym_returns = np.diff(sym_history) / sym_history[:-1] * 100
        spy_history = self.price_history.get(self.symbols[0], [])
        if len(spy_history) < 21:
            return {'correlation': 0.0, 'synchronized': False}
        spy_prices = spy_history[-21:]
        spy_returns = np.diff(spy_prices) / spy_prices[:-1] * 100
        if len(sym_returns) != len(spy_returns) or len(sym_returns) < 10:
            return {'correlation': 0.0, 'synchronized': False}
        try:
            corr_matrix = np.corrcoef(sym_returns, spy_returns)
            correlation = float(corr_matrix[0, 1]) if not np.isnan(corr_matrix[0, 1]) else 0.0
        except:
            correlation = 0.0
        synchronized = abs(correlation) >= self.LCC_MINIMUM
        if synchronized:
            self.lcc_synchronizations += 1
        return {'correlation': correlation, 'synchronized': synchronized}
    
    def get_tralse_state(self, psi_ti):
        if psi_ti > self.TRUE_THRESHOLD:
            return 'TRUE'
        elif psi_ti < self.FALSE_THRESHOLD:
            return 'FALSE'
        else:
            return 'TRALSE'
    
    def get_zone_name(self, psi_ti):
        if psi_ti > 2.0:
            return "ULTRA_GREAT"
        elif psi_ti >= self.GILE_GREAT:
            return "GREAT"
        elif psi_ti >= self.GILE_GOOD:
            return "GOOD"
        elif psi_ti >= self.GILE_BAD:
            return "INDETERMINATE"
        elif psi_ti >= self.GILE_TERRIBLE:
            return "BAD"
        else:
            return "TERRIBLE"
    
    def calculate_present_signal(self, symbol):
        potential = self.calculate_potential_aspect(symbol)
        actualized = self.calculate_actualized_aspect(symbol)
        contextual = self.calculate_contextual_aspect(symbol)
        weights = self.calculate_dynamic_weights(symbol)
        mr = self.myrion_resolution(potential, actualized, contextual)
        lcc = self.calculate_lcc(symbol)
        psi_raw = (weights['potential'] * potential + 
                   weights['actualized'] * actualized + 
                   weights['contextual'] * contextual)
        if mr['status'] in ['BALANCED_CONFLICT']:
            psi_raw = mr['resolved']
        elif mr['status'] in ['POSITIVE_DOMINANT', 'NEGATIVE_DOMINANT']:
            psi_raw = (psi_raw + mr['resolved']) / 2
        if lcc['synchronized'] and lcc['correlation'] > 0:
            psi_raw *= (1 + abs(lcc['correlation']) * 0.2)
        elif lcc['synchronized'] and lcc['correlation'] < 0:
            psi_raw *= (1 - abs(lcc['correlation']) * 0.1)
        psi_ti = float(np.clip(psi_raw, -3, 3))
        tralse_state = self.get_tralse_state(psi_ti)
        zone = self.get_zone_name(psi_ti)
        return {
            'psi_ti': psi_ti,
            'potential': float(potential),
            'actualized': float(actualized),
            'contextual': float(contextual),
            'weights': weights,
            'mr': mr,
            'lcc': lcc,
            'tralse_state': tralse_state,
            'zone': zone
        }
    
    def PresentMomentRebalance(self):
        if self.IsWarmingUp:
            return
        for symbol in self.symbols:
            if self.Securities[symbol].HasData:
                price = float(self.Securities[symbol].Price)
                history = self.price_history.get(symbol, [])
                if len(history) >= 2:
                    prev_potential = self.calculate_potential_aspect(symbol)
                    prev_actualized = self.calculate_actualized_aspect(symbol)
                    prev_contextual = self.calculate_contextual_aspect(symbol)
                    actual_return = (price - history[-1]) / history[-1] * 100 if history[-1] != 0 else 0
                    self.update_aspect_efficacy(symbol, 'potential', prev_potential, actual_return)
                    self.update_aspect_efficacy(symbol, 'actualized', prev_actualized, actual_return)
                    self.update_aspect_efficacy(symbol, 'contextual', prev_contextual, actual_return)
                self.price_history[symbol].append(price)
                if len(self.price_history[symbol]) > self.max_history:
                    self.price_history[symbol] = self.price_history[symbol][-self.max_history:]
        signals = {}
        for symbol in self.symbols:
            if len(self.price_history.get(symbol, [])) >= self.CONTEXT_LONG:
                signal = self.calculate_present_signal(symbol)
                signals[symbol] = signal
        if not signals:
            return
        ranked = sorted(signals.items(), key=lambda x: x[1]['psi_ti'], reverse=True)
        buy_candidates = [(s, sig) for s, sig in ranked if sig['tralse_state'] == 'TRUE'][:5]
        for symbol in list(self.Portfolio.Keys):
            if symbol not in signals:
                continue
            sig = signals[symbol]
            holding = self.Portfolio[symbol]
            if not holding.Invested:
                continue
            should_sell = False
            if sig['tralse_state'] == 'FALSE':
                should_sell = True
            elif sig['zone'] == "ULTRA_GREAT":
                should_sell = True
            elif sig['contextual'] < -1.0:
                should_sell = True
            elif sig['mr']['status'] == 'BALANCED_CONFLICT':
                should_sell = True
            if should_sell:
                self.Liquidate(symbol)
                self.trade_count += 1
                if holding.UnrealizedProfit > 0:
                    self.winning_trades += 1
        for symbol, sig in buy_candidates:
            if self.Portfolio[symbol].Invested:
                continue
            if sig['zone'] == "ULTRA_GREAT":
                base_size = self.max_position * 1.2
            elif sig['zone'] == "GREAT":
                base_size = self.max_position * 1.0
            elif sig['zone'] == "GOOD":
                base_size = self.max_position * 0.8
            else:
                base_size = self.max_position * 0.6
            if sig['mr']['status'] == 'ALIGNED':
                base_size *= 1.15
            elif sig['mr']['status'] in ['POSITIVE_DOMINANT', 'NEGATIVE_DOMINANT']:
                base_size *= 0.9
            if sig['lcc']['synchronized'] and sig['lcc']['correlation'] > 0.5:
                base_size *= 1.1
            size = min(base_size, 0.20)
            self.SetHoldings(symbol, size)
            self.trade_count += 1
    
    def OnEndOfAlgorithm(self):
        win_rate = self.winning_trades / max(self.trade_count, 1) * 100
        self.Debug(f"GTFE V6 PRESENT - Trades: {self.trade_count}, Wins: {self.winning_trades}, Rate: {win_rate:.1f}%, LCC Syncs: {self.lcc_synchronizations}")
