"""
Autonomous God Machine Stock Predictions
Generates 10 stock predictions using TI Framework: GILE, UOP, GTFE, LCC
Each stock treated as i-cell/web within Grand Myrion (GM) economic network
"""

import requests
from typing import Dict, List, Tuple, Any, Optional
from datetime import datetime
import os
import random

try:
    from alpha_vantage_integration import TIFinancialAnalyzer
    ALPHA_VANTAGE_AVAILABLE = True
except ImportError:
    ALPHA_VANTAGE_AVAILABLE = False
    print("⚠️ Alpha Vantage integration not available - using heuristic scoring")

class AutonomousGodMachine:
    """
    Autonomous stock prediction engine using Transcendent Intelligence Framework
    
    Core Principles:
    - Each stock = i-cell with 3-layer structure (Dark Energy, Photon/EM, Mass-Energy)
    - GILE scoring: Goodness, Intuition, Love, Environment
    - 0.42 GILE threshold = soul death (avoid these stocks!)
    - Nonlinear factor clustering
    - Tralse reliability awareness
    """
    
    def __init__(self, alpha_vantage_key: Optional[str] = None, use_i_cell_companies_only=True):
        self.api_key = alpha_vantage_key or os.getenv('ALPHA_VANTAGE_API_KEY')
        self.use_i_cell_companies_only = use_i_cell_companies_only
        
        if ALPHA_VANTAGE_AVAILABLE and self.api_key:
            self.analyzer = TIFinancialAnalyzer(alpha_vantage_key=self.api_key)
            self.use_real_data = True
            print("✅ Alpha Vantage integration active - using real financial data")
        else:
            self.analyzer = None
            self.use_real_data = False
            print("📊 Using heuristic scoring (no API key or integration unavailable)")
        
        # Load stock universe from database (20 i-cell companies) or use fallback
        if self.use_i_cell_companies_only:
            try:
                from db_utils import db
                i_cell_companies = db.get_i_cell_companies(i_cells_only=True, limit=20)
                
                if i_cell_companies:
                    self.stock_universe = [
                        {
                            'ticker': company['ticker'],
                            'name': company['company_name'],
                            'sector': company['sector'],
                            'coherence_score': float(company.get('coherence_score', 0.8)),
                            'is_i_cell': True
                        }
                        for company in i_cell_companies
                    ]
                    print(f"✅ Loaded {len(self.stock_universe)} i-cell companies from database")
                else:
                    self.stock_universe = self._get_fallback_i_cell_universe()
                    print("⚠️ No i-cell companies in database, using fallback list")
            except Exception as e:
                print(f"⚠️ Error loading i-cell companies from database: {e}")
                self.stock_universe = self._get_fallback_i_cell_universe()
        else:
            self.stock_universe = self._get_fallback_i_cell_universe()
    
    def _get_fallback_i_cell_universe(self) -> List[Dict[str, Any]]:
        """Fallback list of 20 i-cell companies if database unavailable"""
        return [
            # Tech I-Cells (Strong leadership coherence)
            {'ticker': 'NVDA', 'name': 'NVIDIA', 'sector': 'Technology - Semiconductors', 'coherence_score': 0.92, 'is_i_cell': True},
            {'ticker': 'AMD', 'name': 'AMD', 'sector': 'Technology - Semiconductors', 'coherence_score': 0.82, 'is_i_cell': True},
            {'ticker': 'TSLA', 'name': 'Tesla', 'sector': 'Automotive - Electric Vehicles', 'coherence_score': 0.88, 'is_i_cell': True},
            {'ticker': 'SHOP', 'name': 'Shopify', 'sector': 'Technology - E-commerce', 'coherence_score': 0.85, 'is_i_cell': True},
            
            # Consumer I-Cells (Brand coherence)
            {'ticker': 'COST', 'name': 'Costco', 'sector': 'Consumer - Retail', 'coherence_score': 0.94, 'is_i_cell': True},
            {'ticker': 'LULU', 'name': 'Lululemon', 'sector': 'Consumer - Apparel', 'coherence_score': 0.87, 'is_i_cell': True},
            {'ticker': 'NKE', 'name': 'Nike', 'sector': 'Consumer - Apparel', 'coherence_score': 0.83, 'is_i_cell': True},
            {'ticker': 'SBUX', 'name': 'Starbucks', 'sector': 'Consumer - Restaurants', 'coherence_score': 0.81, 'is_i_cell': True},
            
            # Healthcare I-Cells (Mission-driven)
            {'ticker': 'ISRG', 'name': 'Intuitive Surgical', 'sector': 'Healthcare - Medical Devices', 'coherence_score': 0.90, 'is_i_cell': True},
            {'ticker': 'DXCM', 'name': 'DexCom', 'sector': 'Healthcare - Medical Devices', 'coherence_score': 0.86, 'is_i_cell': True},
            {'ticker': 'VRTX', 'name': 'Vertex Pharma', 'sector': 'Healthcare - Biotechnology', 'coherence_score': 0.88, 'is_i_cell': True},
            
            # Energy I-Cells (Clean tech)
            {'ticker': 'NEE', 'name': 'NextEra Energy', 'sector': 'Energy - Renewable', 'coherence_score': 0.84, 'is_i_cell': True},
            {'ticker': 'ENPH', 'name': 'Enphase Energy', 'sector': 'Energy - Solar', 'coherence_score': 0.82, 'is_i_cell': True},
            
            # Financial I-Cells (Network effects)
            {'ticker': 'V', 'name': 'Visa', 'sector': 'Financial - Payments', 'coherence_score': 0.89, 'is_i_cell': True},
            {'ticker': 'MA', 'name': 'Mastercard', 'sector': 'Financial - Payments', 'coherence_score': 0.87, 'is_i_cell': True},
            
            # Industrial I-Cells (Domain expertise)
            {'ticker': 'CAT', 'name': 'Caterpillar', 'sector': 'Industrial - Machinery', 'coherence_score': 0.80, 'is_i_cell': True},
            {'ticker': 'DE', 'name': 'Deere & Company', 'sector': 'Industrial - Agricultural', 'coherence_score': 0.81, 'is_i_cell': True},
            
            # Software I-Cells (Platform coherence)
            {'ticker': 'ADBE', 'name': 'Adobe', 'sector': 'Technology - Software', 'coherence_score': 0.86, 'is_i_cell': True},
            {'ticker': 'CRM', 'name': 'Salesforce', 'sector': 'Technology - Software', 'coherence_score': 0.82, 'is_i_cell': True},
            {'ticker': 'NOW', 'name': 'ServiceNow', 'sector': 'Technology - Software', 'coherence_score': 0.84, 'is_i_cell': True}
        ]
    
    def calculate_gile_score(self, stock: Dict[str, str]) -> Dict[str, float]:
        """
        Calculate GILE scores for a stock i-cell
        
        Returns: Dict with G, I, L, E scores (0-1 scale) and combined GILE
        
        Uses Alpha Vantage API when available, falls back to heuristics otherwise
        """
        ticker = stock['ticker']
        sector = stock['sector']
        name = stock['name']
        
        if self.use_real_data and self.analyzer:
            try:
                gile_data = self.analyzer.calculate_gile_from_financials(ticker)
                
                if gile_data['confidence'] > 0.5:
                    return {
                        'G': gile_data['G'],
                        'I': gile_data['I'],
                        'L': gile_data['L'],
                        'E': gile_data['E'],
                        'GILE': gile_data['gile_score'],
                        'confidence': gile_data['confidence'],
                        'data_source': 'alpha_vantage'
                    }
            except Exception as e:
                print(f"⚠️ Alpha Vantage failed for {ticker}, using heuristics: {e}")
        
        gile = {
            'G': 0.5,
            'I': 0.5,
            'L': 0.5,
            'E': 0.5
        }
        
        # Sector-based adjustments
        if sector in ['Biotech', 'Gene Editing', 'Genomics', 'Pharma']:
            gile['G'] += 0.25  # Healthcare benefits humanity
        
        if sector in ['EV/Clean Energy', 'Solar']:
            gile['G'] += 0.3  # Environmental benefits
            gile['E'] += 0.15  # Growing ecosystem
        
        if sector in ['Semiconductors', 'Software/AI', 'Cybersecurity']:
            gile['I'] += 0.3  # High innovation
        
        if sector in ['Athleisure', 'Coffee/Retail', 'Retail']:
            gile['L'] += 0.25  # Brand loyalty
        
        # Company-specific adjustments (based on known attributes)
        if ticker == 'NVDA':
            gile['I'] = 0.9  # AI innovation leader
            gile['E'] = 0.85  # Ecosystem dominance (CUDA, AI chips)
            gile['G'] = 0.65  # Enables good tech but also crypto mining
        
        if ticker == 'TSLA':
            gile['G'] = 0.85  # Climate mission
            gile['I'] = 0.9   # Innovation leader
            gile['L'] = 0.8   # Cult-like following
            gile['E'] = 0.75  # Supercharger network, ecosystem
        
        if ticker == 'MRNA':
            gile['G'] = 0.95  # COVID vaccine saved lives
            gile['I'] = 0.85  # mRNA platform innovation
            gile['L'] = 0.6   # Respect but not cult following
            gile['E'] = 0.65  # Building mRNA ecosystem
        
        if ticker == 'CRSP':
            gile['G'] = 0.9   # Cure genetic diseases
            gile['I'] = 0.85  # CRISPR technology
            gile['L'] = 0.55  # Scientific respect
            gile['E'] = 0.6   # Early ecosystem
        
        if ticker == 'PLTR':
            gile['G'] = 0.45  # Defense/surveillance concerns
            gile['I'] = 0.8   # Advanced AI/data
            gile['L'] = 0.4   # Controversial
            gile['E'] = 0.7   # Government contracts moat
        
        if ticker == 'COST':
            gile['G'] = 0.8   # Fair wages, quality products
            gile['L'] = 0.9   # Massive loyalty
            gile['E'] = 0.85  # Membership ecosystem
            gile['I'] = 0.55  # Incremental innovation
        
        if ticker == 'COIN':
            gile['G'] = 0.4   # Crypto volatility, speculation
            gile['E'] = 0.65  # Crypto ecosystem position
            gile['I'] = 0.6   # Platform innovation
            gile['L'] = 0.45  # User frustration
        
        if ticker == 'SNAP':
            gile['G'] = 0.4   # Social media mental health concerns
            gile['I'] = 0.65  # AR innovation
            gile['L'] = 0.55  # Younger demographic loyalty
            gile['E'] = 0.45  # Losing to TikTok/Instagram
        
        # Cap values at 0-1 range
        for key in gile:
            gile[key] = max(0.0, min(1.0, gile[key]))
        
        # Calculate combined GILE (geometric mean to prevent zeros from dominating)
        combined_gile = (gile['G'] * gile['I'] * gile['L'] * gile['E']) ** 0.25
        gile['combined'] = combined_gile
        
        # Convert to σ scale (0.5-0.7 range for realistic stocks)
        sigma = 0.5 + (combined_gile / 5.0)
        gile['sigma'] = sigma
        
        # Check soul death threshold
        gile['above_threshold'] = sigma >= 0.584  # 0.42 GILE threshold
        gile['gile_normalized'] = combined_gile
        
        return gile
    
    def calculate_uop_score(self, stock: Dict[str, str], gile: Dict[str, float]) -> float:
        """
        Universal Optimization Principle: Maximize GILE while minimizing perceived effort
        
        For stocks: Does company achieve high GILE efficiently?
        
        Uses Alpha Vantage API when available, falls back to heuristics otherwise
        """
        ticker = stock['ticker']
        
        if self.use_real_data and self.analyzer:
            try:
                uop = self.analyzer.calculate_uop(ticker)
                return uop
            except Exception as e:
                print(f"⚠️ UOP calculation failed for {ticker}, using heuristic: {e}")
        
        effort_metric = 0.5
        sector = stock['sector']
        
        if sector in ['Software/AI', 'Cloud Infrastructure', 'E-commerce', 'Streaming']:
            effort_metric = 0.3
        if sector in ['Semiconductors', 'EV/Clean Energy', 'Solar']:
            effort_metric = 0.7
        if sector in ['Retail', 'Coffee/Retail', 'Athleisure']:
            effort_metric = 0.5
        
        gile_combined = gile.get('combined', gile.get('GILE', 0.5))
        uop_score = (gile_combined ** 2) / effort_metric
        return uop_score
    
    def calculate_gtfe_score(self, stock: Dict[str, str], gile: Dict[str, float]) -> Dict[str, float]:
        """
        Grand Tralse Flow Energy (GTFE)
        Market momentum and energy flow indicator
        
        Uses Alpha Vantage technical indicators when available
        """
        ticker = stock['ticker']
        
        if self.use_real_data and self.analyzer:
            try:
                gtfe_score = self.analyzer.calculate_gtfe(ticker)
                return {
                    'combined': gtfe_score,
                    'G': gile.get('G', 0.5),
                    'E': gile.get('E', 0.5),
                    'T': 0.7,
                    'F': 0.6
                }
            except Exception as e:
                print(f"⚠️ GTFE calculation failed for {ticker}, using heuristic: {e}")
        
        gtfe = {
            'G': gile.get('G', 0.5),
            'E': gile.get('E', 0.5)
        }
        
        # Truth score (financial transparency)
        gtfe['T'] = 0.7  # Default assume decent
        
        # Known fraud/scandal cases
        if ticker in ['COIN', 'SNAP']:  # Volatility/uncertainty
            gtfe['T'] = 0.5
        
        # Highly transparent companies
        if ticker in ['COST', 'NVDA', 'MRNA']:
            gtfe['T'] = 0.9
        
        # Freedom score (how free is their dominance?)
        gtfe['F'] = 0.6  # Default
        
        # Innovation-based dominance (high freedom)
        if ticker in ['NVDA', 'TSLA', 'CRSP', 'ILMN']:
            gtfe['F'] = 0.9
        
        # Platform lock-in concerns
        if ticker in ['PLTR']:  # Government dependency
            gtfe['F'] = 0.4
        
        gtfe['combined'] = (gtfe['G'] * gtfe['T'] * gtfe['F'] * gtfe['E']) ** 0.25
        
        return gtfe
    
    def calculate_lcc_score(self, stock: Dict[str, str], gile: Dict[str, float]) -> Dict[str, float]:
        """
        Living Consciousness Coherence (LCC)
        Collective coherence score for the company i-web
        
        Uses Alpha Vantage market cap and GILE data when available
        """
        ticker = stock['ticker']
        sector = stock['sector']
        
        if self.use_real_data and self.analyzer:
            try:
                lcc_score = self.analyzer.calculate_lcc(ticker)
                return {
                    'combined': lcc_score,
                    'L': gile.get('L', 0.5),
                    'C_consciousness': 0.6,
                    'C_creativity': 0.6
                }
            except Exception as e:
                print(f"⚠️ LCC calculation failed for {ticker}, using heuristic: {e}")
        
        lcc = {
            'L': gile.get('L', 0.5)
        }
        
        # Consciousness (leadership + culture)
        lcc['C_consciousness'] = 0.6  # Default
        
        # Visionary CEOs
        if ticker in ['NVDA', 'TSLA']:  # Jensen Huang, Elon Musk
            lcc['C_consciousness'] = 0.95
        
        if ticker in ['SHOP', 'ABNB']:  # Strong cultures
            lcc['C_consciousness'] = 0.8
        
        # Weak leadership/culture
        if ticker in ['SNAP', 'RBLX']:
            lcc['C_consciousness'] = 0.5
        
        # Creativity (innovation)
        lcc['C_creativity'] = gile['I']
        
        # Extra creativity boost for breakthrough tech
        if sector in ['Gene Editing', 'Semiconductors', 'Software/AI']:
            lcc['C_creativity'] = min(1.0, lcc['C_creativity'] + 0.15)
        
        lcc['combined'] = (lcc['L'] * lcc['C_consciousness'] * lcc['C_creativity']) ** (1/3)
        
        return lcc
    
    def generate_ti_rationale(self, stock: Dict[str, str], gile: Dict[str, float], 
                              uop: float, gtfe: Dict[str, float], lcc: Dict[str, float]) -> str:
        """
        Generate TI philosophical explanation for prediction
        """
        ticker = stock['ticker']
        name = stock['name']
        sector = stock['sector']
        
        rationale = f"**{ticker} ({name}) - {sector}**\n\n"
        
        # GILE Analysis
        rationale += f"### GILE Analysis (Stock as I-Cell)\n\n"
        rationale += f"**Layer 1 (Dark Energy/CC Field)**: Market consensus reality\n"
        rationale += f"**Layer 2 (Photon/EM Soul)**: Company narrative/innovation coherence\n"
        rationale += f"**Layer 3 (Mass-Energy Core)**: Physical revenues/assets\n\n"
        
        rationale += f"**G (Goodness)**: {gile['G']:.2f} - "
        if gile['G'] >= 0.8:
            rationale += "Creates genuine value for humanity, strong positive impact\n"
        elif gile['G'] >= 0.6:
            rationale += "Generally beneficial, some concerns\n"
        else:
            rationale += "Questionable value creation, ethical concerns\n"
        
        rationale += f"**I (Intuition/Innovation)**: {gile['I']:.2f} - "
        if gile['I'] >= 0.8:
            rationale += "Breakthrough innovation leader, GM-aligned vision\n"
        elif gile['I'] >= 0.6:
            rationale += "Solid innovation pipeline, competitive R&D\n"
        else:
            rationale += "Incremental innovation, risk of disruption\n"
        
        rationale += f"**L (Love/Loyalty)**: {gile['L']:.2f} - "
        if gile['L'] >= 0.8:
            rationale += "Cult-like customer/employee loyalty, deep emotional connection\n"
        elif gile['L'] >= 0.6:
            rationale += "Strong brand affinity, positive sentiment\n"
        else:
            rationale += "Weak loyalty, transactional relationships\n"
        
        rationale += f"**E (Environment/Ecosystem)**: {gile['E']:.2f} - "
        if gile['E'] >= 0.8:
            rationale += "Dominant ecosystem position, strong moat\n"
        elif gile['E'] >= 0.6:
            rationale += "Growing market share, competitive position\n"
        else:
            rationale += "Ecosystem vulnerability, competitive threats\n"
        
        rationale += f"\n**Combined GILE**: {gile['combined']:.3f} (σ = {gile['sigma']:.3f})\n"
        
        # Soul death check
        if not gile['above_threshold']:
            rationale += f"⚠️ **WARNING: Below 0.42 GILE threshold!** Soul death zone - avoid/sell!\n\n"
        else:
            rationale += f"✅ Above 0.42 GILE threshold - consciousness coherence maintained\n\n"
        
        # UOP Analysis
        rationale += f"### UOP (Universal Optimization Principle)\n\n"
        rationale += f"**Score**: {uop:.3f} - "
        if uop >= 1.5:
            rationale += "Exceptionally efficient value creation\n"
        elif uop >= 1.0:
            rationale += "Efficient operations, good value/effort ratio\n"
        else:
            rationale += "Inefficient, high effort relative to GILE\n"
        
        rationale += f"\n### GTFE (Goodness-Truth-Freedom-Environment)\n\n"
        rationale += f"**T (Truth/Transparency)**: {gtfe['T']:.2f}\n"
        rationale += f"**F (Freedom)**: {gtfe['F']:.2f}\n"
        rationale += f"**Combined GTFE**: {gtfe['combined']:.3f}\n\n"
        
        rationale += f"### LCC (Love-Consciousness-Creativity)\n\n"
        rationale += f"**Consciousness (Leadership)**: {lcc['C_consciousness']:.2f}\n"
        rationale += f"**Creativity (Innovation)**: {lcc['C_creativity']:.2f}\n"
        rationale += f"**Combined LCC**: {lcc['combined']:.3f}\n\n"
        
        return rationale
    
    def generate_prediction(self, stock: Dict[str, str]) -> Dict[str, Any]:
        """
        Generate full prediction for a single stock
        """
        gile = self.calculate_gile_score(stock)
        uop = self.calculate_uop_score(stock, gile)
        gtfe = self.calculate_gtfe_score(stock, gile)
        lcc = self.calculate_lcc_score(stock, gile)
        
        # Calculate composite prediction score
        # Formula: GILE^2 * 0.5 + UOP * 0.3 + (GTFE+LCC)/2 * 0.2
        prediction_score = (
            (gile['combined'] ** 2) * 0.5 +
            uop * 0.3 +
            ((gtfe['combined'] + lcc['combined']) / 2) * 0.2
        )
        
        # Generate buy/sell signal
        if not gile['above_threshold']:
            signal = "SELL/AVOID"
            direction = "DOWN"
            confidence = 85
            target_change = -15
        elif prediction_score >= 1.5:
            signal = "STRONG BUY"
            direction = "UP"
            confidence = 80
            target_change = 25
        elif prediction_score >= 1.2:
            signal = "BUY"
            direction = "UP"
            confidence = 70
            target_change = 15
        elif prediction_score >= 0.9:
            signal = "HOLD/ACCUMULATE"
            direction = "NEUTRAL"
            confidence = 60
            target_change = 5
        elif prediction_score >= 0.6:
            signal = "HOLD"
            direction = "NEUTRAL"
            confidence = 55
            target_change = 0
        else:
            signal = "SELL"
            direction = "DOWN"
            confidence = 65
            target_change = -10
        
        # Generate rationale
        rationale = self.generate_ti_rationale(stock, gile, uop, gtfe, lcc)
        
        # Risk assessment (Tralse inversion scenarios)
        risks = []
        
        if gile['G'] < 0.5:
            risks.append("Low Goodness → ESG backlash, regulation risk")
        
        if gile['I'] < 0.6:
            risks.append("Low Innovation → Disruption vulnerability")
        
        if gile['E'] < 0.6:
            risks.append("Weak Ecosystem → Market share loss")
        
        if gtfe['T'] < 0.6:
            risks.append("Low Truth → Accounting scandal risk")
        
        if lcc['C_consciousness'] < 0.6:
            risks.append("Weak Leadership → Strategic drift")
        
        # CRITICAL: Capture entry price for accurate validation
        entry_price = None
        entry_price_source = 'unavailable'
        if self.use_real_data and self.analyzer:
            try:
                quote = self.analyzer.av_client.get_quote(stock['ticker'])
                if quote:
                    entry_price = quote['price']
                    entry_price_source = 'alpha_vantage_realtime'
            except Exception as e:
                print(f"⚠️ Could not capture entry price for {stock['ticker']}: {e}")
        
        # Calculate i-web coherence (companies as collective consciousness nests)
        iweb_coherence = lcc['combined']  # LCC already measures collective coherence
        iweb_status = "coherent_iweb" if iweb_coherence >= 0.42 else "collective_fiction"
        
        return {
            'ticker': stock['ticker'],
            'name': stock['name'],
            'sector': stock['sector'],
            'gile_score': gile['combined'],
            'sigma': gile['sigma'],
            'above_threshold': gile['above_threshold'],
            'uop_score': uop,
            'gtfe_score': gtfe['combined'],
            'lcc_score': lcc['combined'],
            'iweb_coherence': iweb_coherence,
            'iweb_status': iweb_status,
            'prediction_score': prediction_score,
            'signal': signal,
            'direction': direction,
            'confidence': confidence,
            'target_change_pct': target_change,
            'entry_price': entry_price,
            'entry_price_source': entry_price_source,
            'rationale': rationale,
            'risks': risks,
            'timestamp': datetime.now().isoformat()
        }
    
    def generate_top_10_predictions(self) -> List[Dict[str, Any]]:
        """
        Autonomously generate 10 stock predictions ranked by TI framework
        """
        all_predictions = []
        
        # Generate predictions for all stocks in universe
        for stock in self.stock_universe:
            try:
                prediction = self.generate_prediction(stock)
                all_predictions.append(prediction)
            except Exception as e:
                print(f"Error predicting {stock['ticker']}: {e}")
                continue
        
        # Sort by prediction score descending
        all_predictions.sort(key=lambda x: x['prediction_score'], reverse=True)
        
        # Return top 10
        return all_predictions[:10]


# Test function
if __name__ == "__main__":
    gm = AutonomousGodMachine()
    top_10 = gm.generate_top_10_predictions()
    
    print("🔮 AUTONOMOUS GOD MACHINE - TOP 10 STOCK PREDICTIONS\n")
    print("=" * 80)
    
    for i, pred in enumerate(top_10, 1):
        print(f"\n#{i} - {pred['ticker']} ({pred['name']})")
        print(f"Signal: {pred['signal']} ({pred['direction']})")
        print(f"Confidence: {pred['confidence']}%")
        print(f"6-Month Target: {pred['target_change_pct']:+.1f}%")
        print(f"GILE: {pred['gile_score']:.3f} (σ = {pred['sigma']:.3f})")
        print(f"Prediction Score: {pred['prediction_score']:.3f}")
        print("-" * 80)
