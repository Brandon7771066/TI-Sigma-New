import os
from typing import Dict, Any, List
from concurrent.futures import ThreadPoolExecutor, as_completed
from tenacity import retry, stop_after_attempt, wait_exponential, retry_if_exception
from openai import OpenAI
from anthropic import Anthropic
import requests

def is_rate_limit_error(exception: BaseException) -> bool:
    """Check if the exception is a rate limit or quota violation error."""
    error_msg = str(exception)
    return (
        "429" in error_msg
        or "RATELIMIT_EXCEEDED" in error_msg
        or "quota" in error_msg.lower()
        or "rate limit" in error_msg.lower()
        or (hasattr(exception, "status_code") and exception.status_code == 429)
    )


class OpenAIIntegration:
    def __init__(self):
        # the newest OpenAI model is "gpt-5" which was released August 7, 2025.
        # do not change this unless explicitly requested by the user
        AI_INTEGRATIONS_OPENAI_API_KEY = os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY")
        AI_INTEGRATIONS_OPENAI_BASE_URL = os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL")
        
        self.client = OpenAI(
            api_key=AI_INTEGRATIONS_OPENAI_API_KEY,
            base_url=AI_INTEGRATIONS_OPENAI_BASE_URL
        )
    
    @retry(
        stop=stop_after_attempt(7),
        wait=wait_exponential(multiplier=1, min=2, max=128),
        retry=retry_if_exception(is_rate_limit_error),
        reraise=True
    )
    def analyze(self, prompt: str, system_prompt: str = None) -> str:
        """Analyze text using GPT-5."""
        messages = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})
        
        # the newest OpenAI model is "gpt-5" which was released August 7, 2025.
        # do not change this unless explicitly requested by the user
        response = self.client.chat.completions.create(
            model="gpt-5",
            messages=messages,
            max_completion_tokens=8192
        )
        return response.choices[0].message.content or ""


class AnthropicIntegration:
    def __init__(self):
        AI_INTEGRATIONS_ANTHROPIC_API_KEY = os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY")
        AI_INTEGRATIONS_ANTHROPIC_BASE_URL = os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL")
        
        self.client = Anthropic(
            api_key=AI_INTEGRATIONS_ANTHROPIC_API_KEY,
            base_url=AI_INTEGRATIONS_ANTHROPIC_BASE_URL
        )
    
    @retry(
        stop=stop_after_attempt(7),
        wait=wait_exponential(multiplier=1, min=2, max=128),
        retry=retry_if_exception(is_rate_limit_error),
        reraise=True
    )
    def analyze(self, prompt: str, system_prompt: str = None) -> str:
        """Analyze text using Claude Opus."""
        kwargs = {
            "model": "claude-opus-4-1",
            "max_tokens": 8192,
            "messages": [{"role": "user", "content": prompt}]
        }
        
        if system_prompt:
            kwargs["system"] = system_prompt
        
        message = self.client.messages.create(**kwargs)
        return message.content[0].text if message.content[0].type == "text" else ""


class PerplexityIntegration:
    def __init__(self):
        self.api_key = os.environ.get("PERPLEXITY_API_KEY")
        self.base_url = "https://api.perplexity.ai/chat/completions"
    
    @retry(
        stop=stop_after_attempt(7),
        wait=wait_exponential(multiplier=1, min=2, max=128),
        retry=retry_if_exception(is_rate_limit_error),
        reraise=True
    )
    def analyze(self, prompt: str, system_prompt: str = None) -> Dict[str, Any]:
        """Analyze text using Perplexity with citations."""
        messages = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})
        
        payload = {
            "model": "llama-3.1-sonar-large-128k-online",
            "messages": messages,
            "max_tokens": 8192,
            "temperature": 0.2,
            "top_p": 0.9,
            "return_images": False,
            "return_related_questions": True,
            "stream": False
        }
        
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json"
        }
        
        response = requests.post(self.base_url, json=payload, headers=headers)
        response.raise_for_status()
        
        result = response.json()
        return {
            "content": result["choices"][0]["message"]["content"],
            "citations": result.get("citations", [])
        }
