"""
Overnight Research Agent - Multi-Agent Research Adapter
Implements PlatformAdapter for AutoGen-powered overnight research
Routes through MasterCoordinator for budget enforcement and logging
"""

try:
    import autogen
    AUTOGEN_AVAILABLE = True
except ImportError:
    print("⚠️ AutoGen not imported yet - restart workflow")
    AUTOGEN_AVAILABLE = False
    autogen = None

from datetime import datetime
import json
from db_utils import db
import os
from multi_platform_orchestrator import PlatformAdapter, PlatformCapability, MasterCoordinator
from typing import Dict, Any

# Configure LLM - Use gpt-4o-mini for cost efficiency
llm_config = {
    "config_list": [
        {
            "model": "gpt-4o-mini",
            "api_key": os.getenv("OPENAI_API_KEY", "")
        }
    ],
    "temperature": 0.7,
    "timeout": 120
}


class OvernightResearchAdapter(PlatformAdapter):
    """
    Platform adapter for overnight research using AutoGen multi-agent workflows
    Exposes equation extraction, integration analysis, and paper generation
    """
    
    def __init__(self):
        super().__init__(
            "OvernightResearch", 
            PlatformCapability.MULTI_AGENT_CHAT,
            budget_limit_per_task=3.0
        )
        self.available = AUTOGEN_AVAILABLE
        
        if AUTOGEN_AVAILABLE:
            # Create specialized agents
            self.theory_agent = autogen.AssistantAgent(
                name="TheoryExpert",
                system_message="""You are a theoretical physicist and neuroscientist expert in:
                - Temporal Wave Architecture (TWA)
                - Holistic Existence Matrix (HEM)  
                - Myrion Resolution (MR)
                - Quantum-classical consciousness models
                - i-cell ontology
                
                Your job: Extract equations, explain theoretical foundations.
                Format equations in LaTeX.""",
                llm_config=llm_config
            )
            
            self.integration_agent = autogen.AssistantAgent(
                name="IntegrationSpecialist",
                system_message="""You cross-reference concepts across papers and find connections.
                You understand: TWA, HEM, MR, i-cells, GILE framework, TI-UOP, quantum biology.""",
                llm_config=llm_config
            )
            
            self.writing_agent = autogen.AssistantAgent(
                name="ResearchWriter",
                system_message="""You write publication-ready research papers.
                Output: LaTeX-formatted research papers for Nature, Science, PNAS.""",
                llm_config=llm_config
            )
            
            self.user_proxy = autogen.UserProxyAgent(
                name="Coordinator",
                human_input_mode="NEVER",
                max_consecutive_auto_reply=5,
                code_execution_config={"use_docker": False}
            )
    
    def estimate_cost(self, task: Dict[str, Any]) -> float:
        """Estimate cost for multi-agent research task"""
        # Multi-agent with 3-5 rounds typically uses ~4000-6000 tokens
        return 0.008
    
    def execute_task(self, task: Dict[str, Any], budget_remaining: float) -> Dict[str, Any]:
        """Execute overnight research task with budget enforcement"""
        
        if not self.available:
            return {"status": "unavailable", "message": "AutoGen not installed", "platform": self.name}
        
        estimated = self.estimate_cost(task)
        if estimated > budget_remaining:
            return {
                "status": "budget_exceeded",
                "message": f"Estimated ${estimated:.3f} exceeds remaining ${budget_remaining:.3f}",
                "platform": self.name
            }
        
        task_description = task.get("description", "")
        max_rounds = task.get("max_rounds", 3)
        
        try:
            # Determine which agents to use based on task
            agents = [self.user_proxy, self.theory_agent]
            
            if "integration" in task_description.lower():
                agents.append(self.integration_agent)
            if "paper" in task_description.lower() or "outline" in task_description.lower():
                agents.append(self.writing_agent)
            
            # Create group chat
            group_chat = autogen.GroupChat(
                agents=agents,
                messages=[],
                max_round=max_rounds
            )
            
            manager = autogen.GroupChatManager(
                groupchat=group_chat,
                llm_config=llm_config
            )
            
            # Execute chat
            self.user_proxy.initiate_chat(manager, message=task_description)
            
            # Extract conversation transcript
            messages = group_chat.messages if hasattr(group_chat, 'messages') else []
            
            if messages:
                conversation = "\n\n".join([
                    f"[{msg.get('role', msg.get('name', 'unknown'))}]: {msg.get('content', '')}"
                    for msg in messages
                ])
            else:
                conversation = "Multi-agent task completed (no message history captured)"
            
            # Estimate actual cost (rough approximation)
            estimated_tokens = len(conversation) * 0.75  # Rough token estimate
            pricing = {"input": 0.150 / 1_000_000, "output": 0.600 / 1_000_000}
            actual_cost = (estimated_tokens * 0.4 * pricing["input"]) + (estimated_tokens * 0.6 * pricing["output"])
            
            self.tasks_completed += 1
            self.total_cost += actual_cost
            
            # Persist output to database
            asset_id = db.add_asset(
                asset_type="research_finding",
                source_app=f"Orchestrator-{self.name}",
                title=task.get("title", task_description[:50]),
                content={
                    "task": task.get("title", ""),
                    "prompt": task_description,
                    "conversation": conversation,
                    "agents_used": [a.name for a in agents],
                    "rounds": len(messages),
                    "tokens_estimated": int(estimated_tokens),
                    "cost": actual_cost
                },
                tags=["orchestrator", "overnight_research", "autogen", "multi_agent"]
            )
            
            return {
                "status": "success",
                "result": conversation,
                "tokens_used": int(estimated_tokens),
                "cost": actual_cost,
                "platform": self.name,
                "asset_id": asset_id
            }
            
        except Exception as e:
            return {
                "status": "error",
                "error": str(e),
                "platform": self.name
            }
    
    def get_capability(self) -> PlatformCapability:
        return self.capability


# ============================================================================
# USAGE: Use overnight_research_launcher.py to run overnight research sessions
# ============================================================================
#
# The OvernightResearchAdapter above is registered with MasterCoordinator
# for proper budget enforcement and routing.
#
# To run overnight research:
#   python overnight_research_launcher.py
#
# Or programmatically:
#   from overnight_research_launcher import run_overnight_research_session
#   report = run_overnight_research_session(budget_limit=10.0)
#
# ============================================================================


if __name__ == "__main__":
    print("⚠️  This file contains the OvernightResearchAdapter class.")
    print("⚠️  To run overnight research sessions, use:")
    print()
    print("    python overnight_research_launcher.py")
    print()
    print("   Or import and use:")
    print("    from overnight_research_launcher import run_overnight_research_session")
    print("    report = run_overnight_research_session(budget_limit=10.0)")
    print()
    print("=" * 70)


# Legacy code below this line has been removed.
# OvernightResearchSystem class with duplicate AutoGen agents has been replaced
# with OvernightResearchAdapter (above) that integrates with MasterCoordinator.
