import os
import requests
from typing import Dict, Any, Optional
from tenacity import retry, stop_after_attempt, wait_exponential


class MagAIIntegration:
    def __init__(self, email: str = None, password: str = None):
        """
        Initialize MagAI integration.
        Credentials can be provided directly or through environment variables.
        """
        self.email = email or os.environ.get("MAGAI_EMAIL")
        self.password = password or os.environ.get("MAGAI_PASSWORD")
        self.base_url = "https://api.magai.co"
        self.session_token = None
    
    @retry(
        stop=stop_after_attempt(3),
        wait=wait_exponential(multiplier=1, min=2, max=10),
        reraise=True
    )
    def authenticate(self) -> bool:
        """Authenticate with MagAI and obtain session token."""
        try:
            login_url = f"{self.base_url}/auth/login"
            payload = {
                "email": self.email,
                "password": self.password
            }
            
            response = requests.post(login_url, json=payload)
            
            if response.status_code == 200:
                data = response.json()
                self.session_token = data.get("token") or data.get("access_token")
                return True
            else:
                return False
        except Exception as e:
            return False
    
    def analyze_with_multiple_models(self, prompt: str, models: list = None) -> Dict[str, Any]:
        """
        Analyze text using multiple AI models available in MagAI.
        Returns a dictionary with results from different models.
        """
        if not self.session_token:
            authenticated = self.authenticate()
            if not authenticated:
                return {
                    "error": "Failed to authenticate with MagAI",
                    "available": False
                }
        
        if models is None:
            models = ["gpt-4", "claude-3", "gemini-pro"]
        
        results = {}
        
        for model in models:
            try:
                result = self._query_model(prompt, model)
                results[model] = result
            except Exception as e:
                results[model] = {"error": str(e)}
        
        return {
            "available": True,
            "results": results
        }
    
    def _query_model(self, prompt: str, model: str) -> str:
        """Query a specific model in MagAI."""
        if not self.session_token:
            raise Exception("Not authenticated")
        
        headers = {
            "Authorization": f"Bearer {self.session_token}",
            "Content-Type": "application/json"
        }
        
        payload = {
            "model": model,
            "prompt": prompt,
            "max_tokens": 4000
        }
        
        response = requests.post(
            f"{self.base_url}/chat/completions",
            headers=headers,
            json=payload,
            timeout=60
        )
        
        if response.status_code == 200:
            data = response.json()
            return data.get("response", data.get("content", "No response"))
        else:
            raise Exception(f"API error: {response.status_code}")
    
    def get_available_models(self) -> list:
        """Get list of available AI models in MagAI."""
        if not self.session_token:
            self.authenticate()
        
        try:
            headers = {"Authorization": f"Bearer {self.session_token}"}
            response = requests.get(f"{self.base_url}/models", headers=headers)
            
            if response.status_code == 200:
                return response.json().get("models", [])
            else:
                return ["gpt-4", "claude-3", "gemini-pro", "llama-3"]
        except:
            return ["gpt-4", "claude-3", "gemini-pro", "llama-3"]
