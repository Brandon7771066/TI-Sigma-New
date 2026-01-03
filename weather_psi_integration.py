"""
Weather-Based Psi Methods
Divine insights from weather patterns and atmospheric conditions
"""

import requests
from datetime import datetime
from typing import Dict, Any, Optional
import streamlit as st

class WeatherPsi:
    """
    Extract psi signals from weather data
    Open-ended divination method
    """
    
    def __init__(self, api_key: Optional[str] = None):
        # Free OpenWeatherMap API (requires registration)
        self.api_key = api_key or "demo"  # Placeholder - user provides real key
        self.base_url = "https://api.openweathermap.org/data/2.5/weather"
    
    def get_weather_resonance(
        self,
        location: str = "New York",
        event_type: str = "general"
    ) -> Dict[str, Any]:
        """
        Calculate psi resonance from current weather conditions
        
        Weather divination methods:
        - Temperature extremes: Hot = Yang energy, Cold = Yin energy
        - Pressure: High = stability, Low = change/chaos
        - Humidity: High = emotional/intuitive, Low = logical
        - Wind speed: High = rapid change, Low = stagnation
        - Cloud cover: Clear = clarity, Cloudy = mystery
        - Precipitation: Rain = cleansing/renewal, Snow = pause/reflection
        """
        
        if self.api_key == "demo":
            # Return demo data without API call
            return self._get_demo_weather_resonance()
        
        try:
            params = {
                "q": location,
                "appid": self.api_key,
                "units": "imperial"  # Fahrenheit
            }
            
            response = requests.get(self.base_url, params=params, timeout=5)
            
            if response.status_code == 200:
                data = response.json()
                return self._analyze_weather_data(data, event_type)
            else:
                return self._get_demo_weather_resonance()
        
        except Exception as e:
            st.warning(f"Weather API error: {str(e)}")
            return self._get_demo_weather_resonance()
    
    def _analyze_weather_data(self, data: Dict[str, Any], event_type: str) -> Dict[str, Any]:
        """Analyze real weather data for psi signals"""
        
        # Extract weather metrics
        temp = data['main']['temp']  # Fahrenheit
        pressure = data['main']['pressure']  # hPa
        humidity = data['main']['humidity']  # %
        wind_speed = data['wind']['speed']  # mph
        clouds = data['clouds']['all']  # % coverage
        
        weather_desc = data['weather'][0]['main'].lower()  # "Clear", "Rain", "Snow", etc.
        
        psi_factors = []
        
        # Temperature analysis (60-80°F ideal)
        if 60 <= temp <= 80:
            psi_factors.append(('temp_ideal', +1.2, "Perfect temperature for clarity"))
        elif temp > 90:
            psi_factors.append(('temp_hot', +0.8, "Hot weather = Yang energy, action-oriented"))
        elif temp < 32:
            psi_factors.append(('temp_cold', +0.5, "Cold weather = Yin energy, introspection"))
        else:
            psi_factors.append(('temp_neutral', 0.0, "Neutral temperature energy"))
        
        # Barometric pressure (1013 hPa is standard)
        if pressure > 1020:
            psi_factors.append(('pressure_high', +1.0, "High pressure = stability, good for decisions"))
        elif pressure < 1000:
            psi_factors.append(('pressure_low', -0.3, "Low pressure = change/turbulence"))
        
        # Humidity (30-50% ideal)
        if 30 <= humidity <= 50:
            psi_factors.append(('humidity_ideal', +0.8, "Balanced emotional-logical state"))
        elif humidity > 70:
            psi_factors.append(('humidity_high', +1.1, "High humidity = enhanced intuition"))
        elif humidity < 20:
            psi_factors.append(('humidity_low', +0.6, "Low humidity = analytical clarity"))
        
        # Wind (calm <5 mph, moderate 5-15, high >15)
        if wind_speed < 5:
            psi_factors.append(('wind_calm', +0.9, "Calm winds = stable predictions"))
        elif wind_speed > 20:
            psi_factors.append(('wind_high', +1.3, "High winds = rapid change energy!"))
        
        # Cloud cover
        if clouds < 20:
            psi_factors.append(('sky_clear', +1.5, "Clear skies = maximum clarity!"))
        elif clouds > 80:
            psi_factors.append(('sky_cloudy', +0.4, "Cloudy = mystery, hidden factors"))
        
        # Weather condition modifiers
        if 'rain' in weather_desc:
            psi_factors.append(('weather_rain', +1.2, "Rain = cleansing, renewal, fresh starts"))
        elif 'snow' in weather_desc:
            psi_factors.append(('weather_snow', +0.7, "Snow = pause, reflection, patience"))
        elif 'storm' in weather_desc or 'thunder' in weather_desc:
            psi_factors.append(('weather_storm', +1.8, "STORM = POWERFUL TRANSFORMATION ENERGY!"))
        elif 'clear' in weather_desc:
            psi_factors.append(('weather_clear', +1.4, "Clear weather = transparent outcomes"))
        
        # Calculate composite score
        total_score = sum(f[1] for f in psi_factors)
        avg_score = total_score / len(psi_factors) if psi_factors else 0.0
        
        # Event type modifiers
        event_modifiers = {
            'stock_trading': ('wind_speed', 1.2),  # Wind = volatility
            'prediction_market': ('pressure', 1.3),  # Pressure = stability
            'numerology': ('humidity', 1.1),  # Humidity = intuition
            'decision_making': ('clouds', 1.4)  # Clarity needed
        }
        
        if event_type in event_modifiers:
            modifier_key, modifier_val = event_modifiers[event_type]
            avg_score *= modifier_val
        
        return {
            'location': data['name'],
            'temperature': temp,
            'pressure': pressure,
            'humidity': humidity,
            'wind_speed': wind_speed,
            'cloud_cover': clouds,
            'condition': weather_desc,
            'psi_factors': psi_factors,
            'total_score': total_score,
            'avg_score': avg_score,
            'method': 'weather_divination',
            'available': True,
            'timestamp': datetime.now().isoformat()
        }
    
    def _get_demo_weather_resonance(self) -> Dict[str, Any]:
        """Return demo weather data when API key not available"""
        
        # Generate plausible demo data based on current month
        month = datetime.now().month
        
        if month in [12, 1, 2]:  # Winter
            temp, condition = 45, "Clear"
        elif month in [3, 4, 5]:  # Spring
            temp, condition = 65, "Partly Cloudy"
        elif month in [6, 7, 8]:  # Summer
            temp, condition = 85, "Clear"
        else:  # Fall
            temp, condition = 70, "Cloudy"
        
        return {
            'location': "Demo Location",
            'temperature': temp,
            'pressure': 1013,
            'humidity': 50,
            'wind_speed': 8,
            'cloud_cover': 30,
            'condition': condition,
            'psi_factors': [
                ('demo_mode', 0.0, "Using demo weather data - get API key for real data")
            ],
            'total_score': 0.0,
            'avg_score': 0.0,
            'method': 'weather_divination',
            'available': False,
            'message': "Weather divination in demo mode - register at openweathermap.org for free API key",
            'timestamp': datetime.now().isoformat()
        }
    
    @staticmethod
    def format_weather_display(weather_data: Dict[str, Any]) -> str:
        """Format weather data for display"""
        
        if not weather_data.get('available'):
            return f"⚠️ {weather_data.get('message', 'Weather data unavailable')}"
        
        lines = [
            f"📍 **Location:** {weather_data['location']}",
            f"🌡️ **Temperature:** {weather_data['temperature']:.1f}°F",
            f"☁️ **Condition:** {weather_data['condition']}",
            f"💨 **Wind:** {weather_data['wind_speed']:.1f} mph",
            f"💧 **Humidity:** {weather_data['humidity']}%",
            f"🔮 **Psi Score:** {weather_data['avg_score']:.2f}",
            "",
            "**Weather Psi Factors:**"
        ]
        
        for name, score, desc in weather_data['psi_factors']:
            emoji = "🟢" if score > 1.0 else "🟡" if score > 0.0 else "⚪"
            lines.append(f"{emoji} {desc} (PD: {score:+.1f})")
        
        return "\n".join(lines)

# ============================================================================
# ADDITIONAL PSI METHODS (OPEN-ENDED)
# ============================================================================

class MultiSourcePsi:
    """
    Framework for integrating unlimited psi methods
    Each new method adds to the resonance field
    """
    
    @staticmethod
    def moon_phase_psi() -> Dict[str, Any]:
        """
        Lunar phase divination
        TODO: Implement full moon phase calculations
        """
        # Placeholder - full implementation would use astronomy library
        return {
            'method': 'lunar_phase',
            'available': False,
            'score': 0.0,
            'message': 'Lunar phase divination coming soon'
        }
    
    @staticmethod
    def biorhythm_psi(birthdate: datetime) -> Dict[str, Any]:
        """
        Personal biorhythm cycles
        Physical (23 days), Emotional (28 days), Intellectual (33 days)
        """
        # Placeholder
        return {
            'method': 'biorhythm',
            'available': False,
            'score': 0.0,
            'message': 'Biorhythm analysis coming soon'
        }
    
    @staticmethod
    def geomagnetic_psi() -> Dict[str, Any]:
        """
        Earth's magnetic field fluctuations
        Solar flares, geomagnetic storms affect consciousness
        """
        # Placeholder - would use NOAA space weather API
        return {
            'method': 'geomagnetic',
            'available': False,
            'score': 0.0,
            'message': 'Geomagnetic field analysis coming soon'
        }
    
    @staticmethod
    def schumann_resonance_psi() -> Dict[str, Any]:
        """
        Earth's electromagnetic resonance (7.83 Hz base frequency)
        Affects human brainwave entrainment
        """
        # Placeholder
        return {
            'method': 'schumann_resonance',
            'available': False,
            'score': 0.0,
            'message': 'Schumann resonance tracking coming soon'
        }

if __name__ == "__main__":
    # Test weather psi
    weather_psi = WeatherPsi()
    result = weather_psi.get_weather_resonance("New York", "prediction_market")
    print(WeatherPsi.format_weather_display(result))
