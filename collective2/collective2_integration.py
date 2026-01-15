"""
Collective2 API Integration for ARTA Algorithm
Submits trading signals via C2 API v3

API Key must be stored as COLLECTIVE2_API_KEY secret
System ID must be stored as COLLECTIVE2_SYSTEM_ID secret
"""

import os
import requests
import json
from datetime import datetime
from typing import Optional, Dict, Any, List
from dataclasses import dataclass
from enum import Enum

C2_BASE_URL = "https://api.collective2.com/world/apiv3"

class SignalAction(Enum):
    BUY_TO_OPEN = "BTO"
    SELL_TO_CLOSE = "STC"
    SELL_TO_OPEN = "STO"
    BUY_TO_CLOSE = "BTC"

class SymbolType(Enum):
    STOCK = "stock"
    OPTION = "option"
    FUTURE = "future"
    FOREX = "forex"

class OrderDuration(Enum):
    DAY = "DAY"
    GTC = "GTC"
    IOC = "IOC"
    FOK = "FOK"

@dataclass
class C2Signal:
    action: SignalAction
    symbol: str
    quantity: int
    symbol_type: SymbolType = SymbolType.STOCK
    limit_price: Optional[float] = None
    stop_price: Optional[float] = None
    duration: OrderDuration = OrderDuration.DAY

@dataclass
class C2Response:
    success: bool
    signal_id: Optional[str] = None
    message: str = ""
    raw_response: Dict = None

class Collective2Client:
    """
    Client for Collective2 API v3
    Manages signal submission for ARTA algorithm
    """
    
    def __init__(self):
        self.api_key = os.environ.get("COLLECTIVE2_API_KEY")
        self.system_id = os.environ.get("COLLECTIVE2_SYSTEM_ID")
        self.base_url = C2_BASE_URL
        
        if not self.api_key:
            raise ValueError("COLLECTIVE2_API_KEY environment variable not set")
        if not self.system_id:
            raise ValueError("COLLECTIVE2_SYSTEM_ID environment variable not set")
    
    def _make_request(self, endpoint: str, payload: Dict) -> Dict:
        """Make authenticated request to C2 API"""
        payload["apikey"] = self.api_key
        payload["systemid"] = int(self.system_id)
        
        url = f"{self.base_url}/{endpoint}"
        
        try:
            response = requests.post(
                url,
                json=payload,
                headers={"Content-Type": "application/json"},
                timeout=30
            )
            response.raise_for_status()
            return response.json()
        except requests.RequestException as e:
            return {"error": str(e), "ok": 0}
    
    def submit_signal(self, signal: C2Signal) -> C2Response:
        """Submit a trading signal to Collective2"""
        
        signal_payload = {
            "action": signal.action.value,
            "quant": signal.quantity,
            "symbol": signal.symbol,
            "typeofsymbol": signal.symbol_type.value,
            "duration": signal.duration.value
        }
        
        if signal.limit_price:
            signal_payload["limit"] = signal.limit_price
        
        if signal.stop_price:
            signal_payload["stop"] = signal.stop_price
        
        payload = {"signal": signal_payload}
        
        result = self._make_request("submitSignal", payload)
        
        if result.get("ok") == 1:
            return C2Response(
                success=True,
                signal_id=str(result.get("signalid", "")),
                message="Signal submitted successfully",
                raw_response=result
            )
        else:
            return C2Response(
                success=False,
                message=result.get("error", "Unknown error"),
                raw_response=result
            )
    
    def submit_position_maintenance(self, positions: List[Dict[str, Any]]) -> C2Response:
        """
        Submit desired positions (C2 will generate orders automatically)
        
        positions: List of {symbol, quantity, symbol_type}
        - positive quantity = long
        - negative quantity = short
        - zero quantity = flat
        """
        
        desired = []
        for pos in positions:
            desired.append({
                "symbol": pos["symbol"],
                "quant": pos["quantity"],
                "typeofsymbol": pos.get("symbol_type", "stock")
            })
        
        payload = {"desiredPositions": desired}
        
        result = self._make_request("setDesiredPositions", payload)
        
        if result.get("ok") == 1:
            return C2Response(
                success=True,
                message="Positions updated successfully",
                raw_response=result
            )
        else:
            return C2Response(
                success=False,
                message=result.get("error", "Unknown error"),
                raw_response=result
            )
    
    def cancel_signal(self, signal_id: str) -> C2Response:
        """Cancel a pending signal"""
        
        payload = {"signalid": signal_id}
        result = self._make_request("cancelSignal", payload)
        
        return C2Response(
            success=result.get("ok") == 1,
            message=result.get("error", "Signal cancelled") if result.get("ok") != 1 else "Cancelled",
            raw_response=result
        )
    
    def get_open_positions(self) -> Dict:
        """Get current open positions"""
        
        payload = {"openTrades": 1}
        return self._make_request("requestAllTrades_overview", payload)
    
    def get_system_stats(self) -> Dict:
        """Get system performance statistics"""
        
        return self._make_request("requestSystemStats", {})


class ARTASignalGenerator:
    """
    Converts ARTA algorithm signals to Collective2 format
    Tracks positions to ensure proper order types
    """
    
    def __init__(self, c2_client: Collective2Client):
        self.client = c2_client
        self.position_size = 100
        self.current_positions: Dict[str, int] = {}
    
    def refresh_positions(self):
        """Fetch current positions from C2"""
        result = self.client.get_open_positions()
        self.current_positions = {}
        
        if result.get("ok") == 1:
            trades = result.get("response", {}).get("trades", [])
            for trade in trades:
                symbol = trade.get("symbol", "")
                qty = trade.get("quant_current", 0)
                if symbol and qty != 0:
                    self.current_positions[symbol] = qty
    
    def get_position(self, ticker: str) -> int:
        """Get current position for a ticker (positive=long, negative=short)"""
        return self.current_positions.get(ticker, 0)
    
    def signal_to_c2(self, ticker: str, signal: str, confidence: float) -> Optional[C2Signal]:
        """
        Convert ARTA signal to C2 signal with position awareness
        
        signal: 'strong_buy', 'buy', 'hold', 'sell', 'strong_sell'
        confidence: 0.0 to 1.0
        """
        
        current_pos = self.get_position(ticker)
        target_quantity = int(self.position_size * max(confidence, 0.5))
        
        if target_quantity < 1:
            target_quantity = 1
        
        if signal in ("strong_buy", "buy"):
            if current_pos <= 0:
                return C2Signal(
                    action=SignalAction.BUY_TO_OPEN,
                    symbol=ticker,
                    quantity=target_quantity
                )
            else:
                return None
                
        elif signal in ("strong_sell", "sell"):
            if current_pos > 0:
                return C2Signal(
                    action=SignalAction.SELL_TO_CLOSE,
                    symbol=ticker,
                    quantity=abs(current_pos)
                )
            else:
                return None
        else:
            return None
    
    def submit_arta_signal(self, ticker: str, signal: str, confidence: float) -> C2Response:
        """Submit an ARTA signal to Collective2 with position awareness"""
        
        c2_signal = self.signal_to_c2(ticker, signal, confidence)
        
        if c2_signal is None:
            return C2Response(
                success=False,
                message=f"No action for signal: {signal} (pos={self.get_position(ticker)})"
            )
        
        result = self.client.submit_signal(c2_signal)
        
        if result.success:
            if c2_signal.action == SignalAction.BUY_TO_OPEN:
                self.current_positions[ticker] = c2_signal.quantity
            elif c2_signal.action == SignalAction.SELL_TO_CLOSE:
                self.current_positions[ticker] = 0
        
        return result
    
    def submit_target_positions(self, targets: Dict[str, int]) -> C2Response:
        """
        Submit target positions using C2's position maintenance API
        This is the preferred method - C2 handles the order logic
        
        targets: {ticker: quantity} where positive=long, negative=short, 0=flat
        """
        positions = [
            {"symbol": ticker, "quantity": qty, "symbol_type": "stock"}
            for ticker, qty in targets.items()
        ]
        return self.client.submit_position_maintenance(positions)


def test_connection():
    """Test connection to Collective2 (requires API keys)"""
    
    try:
        client = Collective2Client()
        stats = client.get_system_stats()
        
        if stats.get("ok") == 1:
            print("Connection successful!")
            print(f"System stats: {json.dumps(stats, indent=2)}")
            return True
        else:
            print(f"Connection failed: {stats.get('error')}")
            return False
            
    except ValueError as e:
        print(f"Configuration error: {e}")
        print("\nTo use Collective2 integration:")
        print("1. Set COLLECTIVE2_API_KEY secret")
        print("2. Set COLLECTIVE2_SYSTEM_ID secret")
        return False


if __name__ == "__main__":
    test_connection()
