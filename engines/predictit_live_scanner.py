"""
PredictIt Live Market Scanner with TI Framework Analysis
=========================================================
Pulls real-time market data from PredictIt's free API and applies
Tralse classification, EAR analysis, and Kelly criterion sizing.

API: https://www.predictit.org/api/marketdata/all/
Rate limit: 1 request per minute
Cost: FREE, no API key required
"""

import requests
import math
import time
import json
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Tuple

TI_TRUTH = math.cos(math.pi / 8)
TI_EXISTENCE = math.cos(math.pi / 8) ** 2
TI_GILE = math.cos(math.pi / 5) ** 2
TI_LCC = (math.sqrt(2) + 1) / 4
TI_HYPERCONNECTION = math.sqrt(2) - 1

PREDICTIT_API_URL = "https://www.predictit.org/api/marketdata/all/"
PROFIT_FEE = 0.10
WITHDRAWAL_FEE = 0.05


class PredictItScanner:
    def __init__(self):
        self.last_fetch_time = 0
        self.cached_markets = None
        self.cache_ttl = 60

    def fetch_markets(self, force: bool = False) -> Optional[dict]:
        now = time.time()
        if not force and self.cached_markets and (now - self.last_fetch_time) < self.cache_ttl:
            return self.cached_markets

        try:
            resp = requests.get(PREDICTIT_API_URL, timeout=15, headers={
                'User-Agent': 'TI-Framework-Research/1.0'
            })
            resp.raise_for_status()
            data = resp.json()
            self.cached_markets = data
            self.last_fetch_time = now
            return data
        except Exception as e:
            print(f"PredictIt API error: {e}")
            return self.cached_markets

    def get_all_contracts(self) -> List[dict]:
        data = self.fetch_markets()
        if not data or 'markets' not in data:
            return []

        contracts = []
        for market in data['markets']:
            market_name = market.get('name', '')
            market_id = market.get('id', 0)
            market_url = market.get('url', '')

            for contract in market.get('contracts', []):
                best_buy_yes = contract.get('bestBuyYesCost')
                best_buy_no = contract.get('bestBuyNoCost')
                best_sell_yes = contract.get('bestSellYesCost')
                best_sell_no = contract.get('bestSellNoCost')
                last_trade = contract.get('lastTradePrice')
                last_close = contract.get('lastClosePrice')

                yes_price = best_buy_yes or last_trade or last_close or 0.5
                no_price = best_buy_no if best_buy_no is not None else (1.0 - yes_price)

                raw_sum = yes_price + no_price
                if raw_sum > 0:
                    implied_yes = yes_price / raw_sum
                    implied_no = no_price / raw_sum
                else:
                    implied_yes = 0.5
                    implied_no = 0.5

                contracts.append({
                    'market_id': market_id,
                    'market_name': market_name,
                    'market_url': market_url,
                    'contract_id': contract.get('id', 0),
                    'contract_name': contract.get('name', ''),
                    'yes_price': yes_price,
                    'no_price': no_price,
                    'implied_yes_prob': implied_yes,
                    'implied_no_prob': implied_no,
                    'best_buy_yes': best_buy_yes,
                    'best_buy_no': best_buy_no,
                    'best_sell_yes': best_sell_yes,
                    'best_sell_no': best_sell_no,
                    'last_trade': last_trade,
                    'last_close': last_close,
                    'volume': contract.get('volume', 0) or 0,
                    'open_interest': contract.get('openInterest', 0) or 0,
                    'date_end': contract.get('dateEnd', ''),
                    'status': contract.get('status', ''),
                    'spread': abs(1.0 - yes_price - no_price),
                })
        return contracts

    def analyze_contract(self, contract: dict, our_probability: Optional[float] = None) -> dict:
        yes_price = contract['yes_price']
        no_price = contract['no_price']
        implied_yes = contract.get('implied_yes_prob', yes_price)

        if our_probability is None:
            market_implied_prob = implied_yes
            edge_score = 0.0
            position = 'OBSERVE'
        else:
            market_implied_prob = implied_yes
            yes_edge = our_probability - yes_price
            no_edge = (1.0 - our_probability) - no_price

            if yes_edge > no_edge and yes_edge > 0:
                edge_score = yes_edge
                position = 'BUY YES'
            elif no_edge > yes_edge and no_edge > 0:
                edge_score = no_edge
                position = 'BUY NO'
            else:
                edge_score = 0.0
                position = 'NO EDGE'

        prob_for_ev = our_probability if our_probability is not None else implied_yes

        tralse = self._tralse_classify_price(yes_price, contract.get('spread', 0))

        ev_yes = self._expected_value_full(prob_for_ev, yes_price)
        ev_no = self._expected_value_full(1.0 - prob_for_ev, no_price)

        best_ev = max(ev_yes, ev_no)
        best_side = 'YES' if ev_yes >= ev_no else 'NO'

        return {
            **contract,
            'market_implied_prob': market_implied_prob,
            'our_probability': our_probability,
            'edge': edge_score,
            'position': position,
            'tralse_state': tralse['state'],
            'tralse_action': tralse['action'],
            'tralse_confidence': tralse['confidence'],
            'ev_yes': ev_yes,
            'ev_no': ev_no,
            'best_ev': best_ev,
            'best_side': best_side,
            'net_return_yes': self._net_return(yes_price) if 0 < yes_price < 1.0 else 0,
            'net_return_no': self._net_return(no_price) if 0 < no_price < 1.0 else 0,
        }

    def _tralse_classify_price(self, yes_price: float, spread: float) -> dict:
        distance_from_certainty = min(yes_price, 1.0 - yes_price)

        if distance_from_certainty < (1.0 - TI_TRUTH):
            if spread < 0.05:
                return {'state': 'TRUE', 'action': 'HIGH CONVICTION', 'confidence': 1.0 - distance_from_certainty}
            else:
                return {'state': 'TRALSE', 'action': 'WIDE SPREAD', 'confidence': 0.5}
        elif distance_from_certainty < (1.0 - TI_EXISTENCE):
            return {'state': 'TRUE', 'action': 'LEAN', 'confidence': TI_EXISTENCE - distance_from_certainty}
        elif distance_from_certainty < TI_HYPERCONNECTION:
            return {'state': 'TRALSE', 'action': 'UNCERTAIN', 'confidence': 0.3}
        else:
            return {'state': 'TRALSE', 'action': 'COIN FLIP', 'confidence': 0.0}

    def _expected_value_full(self, prob: float, cost: float) -> float:
        if cost <= 0 or cost >= 1.0:
            return 0.0
        gross_win = 1.0 - cost
        after_profit_fee = gross_win * (1 - PROFIT_FEE)
        total_if_win = cost + after_profit_fee
        payout_if_win = total_if_win * (1 - WITHDRAWAL_FEE)
        net_if_win = payout_if_win - cost

        total_if_lose = 0.0
        payout_if_lose = 0.0
        net_if_lose = -cost

        ev = (prob * net_if_win) + ((1 - prob) * net_if_lose)
        return ev

    def _net_return(self, cost: float) -> float:
        if cost <= 0 or cost >= 1.0:
            return 0.0
        gross_profit = 1.0 - cost
        after_profit_fee = gross_profit * (1 - PROFIT_FEE)
        total = cost + after_profit_fee
        after_withdrawal = total * (1 - WITHDRAWAL_FEE)
        net = after_withdrawal - cost
        return net / cost

    def kelly_size(self, prob: float, cost: float, bankroll: float, fraction: float = 0.25) -> float:
        if cost <= 0 or cost >= 1.0 or prob <= 0 or prob >= 1.0:
            return 0.0
        gross_win = 1.0 - cost
        after_profit_fee = gross_win * (1 - PROFIT_FEE)
        total_if_win = cost + after_profit_fee
        payout_if_win = total_if_win * (1 - WITHDRAWAL_FEE)
        net_win = payout_if_win - cost
        net_odds = net_win / cost
        if net_odds <= 0:
            return 0.0
        kelly = (prob * net_odds - (1 - prob)) / net_odds
        kelly = max(0, kelly)
        bet = bankroll * kelly * fraction
        bet = min(bet, bankroll * 0.10)
        return round(bet, 2)

    def scan_opportunities(self, bankroll: float = 500.0, min_volume: int = 0) -> List[dict]:
        contracts = self.get_all_contracts()
        if not contracts:
            return []

        analyzed = []
        for c in contracts:
            if c['status'] != 'Open':
                continue
            if c['volume'] < min_volume:
                continue

            result = self.analyze_contract(c)
            result['kelly_yes'] = self.kelly_size(
                result['market_implied_prob'], result['yes_price'], bankroll
            )
            result['kelly_no'] = self.kelly_size(
                1.0 - result['market_implied_prob'], result['no_price'], bankroll
            )
            analyzed.append(result)

        return analyzed

    def find_mispriced(self, contracts: List[dict], threshold: float = 0.15) -> List[dict]:
        mispriced = []
        for c in contracts:
            yes_p = c.get('yes_price', 0)
            no_p = c.get('no_price', 0)

            spread = abs(1.0 - yes_p - no_p)
            if spread > threshold:
                c['spread_inefficiency'] = spread
                mispriced.append(c)

            if yes_p < 0.05 or yes_p > 0.95:
                if c.get('volume', 0) > 100:
                    c['extreme_price'] = True
                    if c not in mispriced:
                        mispriced.append(c)

        return sorted(mispriced, key=lambda x: x.get('spread_inefficiency', 0), reverse=True)

    def categorize_markets(self, contracts: List[dict]) -> dict:
        categories = {
            'presidential': [],
            'congressional': [],
            'policy': [],
            'other': [],
        }

        for c in contracts:
            name_lower = c.get('market_name', '').lower()
            if any(k in name_lower for k in ['president', 'presidential', 'white house', 'nominee']):
                categories['presidential'].append(c)
            elif any(k in name_lower for k in ['senate', 'house', 'congress', 'representative', 'governor']):
                categories['congressional'].append(c)
            elif any(k in name_lower for k in ['policy', 'bill', 'legislation', 'executive order', 'fed', 'rate']):
                categories['policy'].append(c)
            else:
                categories['other'].append(c)

        return categories

    def get_summary_stats(self, contracts: List[dict]) -> dict:
        if not contracts:
            return {'total': 0}

        volumes = [c.get('volume', 0) for c in contracts]
        prices = [c.get('yes_price', 0) for c in contracts]
        evs = [c.get('best_ev', 0) for c in contracts if c.get('best_ev')]

        return {
            'total': len(contracts),
            'total_volume': sum(volumes),
            'avg_volume': sum(volumes) / len(volumes) if volumes else 0,
            'max_volume': max(volumes) if volumes else 0,
            'avg_yes_price': sum(prices) / len(prices) if prices else 0,
            'positive_ev_count': sum(1 for e in evs if e > 0),
            'avg_ev': sum(evs) / len(evs) if evs else 0,
            'markets_scanned': len(set(c.get('market_id') for c in contracts)),
        }
