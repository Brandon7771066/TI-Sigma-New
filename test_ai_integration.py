"""
Quick test to verify AI integrations are working
"""

import os
from openai import OpenAI
from anthropic import Anthropic

# Test OpenAI GPT-5
print("Testing OpenAI GPT-5 via Replit AI Integrations...")
try:
    openai_client = OpenAI(
        api_key=os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY"),
        base_url=os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL")
    )
    
    response = openai_client.chat.completions.create(
        model="gpt-5",
        messages=[{"role": "user", "content": "Say 'GPT-5 works!' in exactly 3 words."}],
        max_completion_tokens=20
    )
    
    print(f"✅ GPT-5 Response: {response.choices[0].message.content}")
except Exception as e:
    print(f"❌ GPT-5 Error: {e}")

# Test Anthropic Claude Opus 4.1
print("\nTesting Claude Opus 4.1 via Replit AI Integrations...")
try:
    anthropic_client = Anthropic(
        api_key=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY"),
        base_url=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL")
    )
    
    message = anthropic_client.messages.create(
        model="claude-opus-4-1",
        max_tokens=20,
        messages=[{"role": "user", "content": "Say 'Claude works!' in exactly 3 words."}]
    )
    
    print(f"✅ Claude Response: {message.content[0].text}")
except Exception as e:
    print(f"❌ Claude Error: {e}")

print("\n✨ Test complete!")
