"""
Overnight Research Launcher
Simple launcher that registers OvernightResearchAdapter with MasterCoordinator
"""

from datetime import datetime
from overnight_research_agent import OvernightResearchAdapter
from multi_platform_orchestrator import MasterCoordinator, PlatformCapability
from db_utils import db


def run_overnight_research_session(budget_limit: float = 10.0):
    """
    Launch overnight research session using MasterCoordinator
    All tasks route through coordinator for budget enforcement
    """
    
    print("🌙 " + "="*70)
    print("   OVERNIGHT RESEARCH SESSION")
    print(f"   Budget: ${budget_limit}")
    print("="*70)
    
    # Create coordinator
    coordinator = MasterCoordinator(budget_limit=budget_limit)
    
    # Register overnight research adapter
    overnight_adapter = OvernightResearchAdapter()
    coordinator.register_platform(overnight_adapter)
    
    # Define overnight research tasks
    overnight_tasks = [
        {
            "title": "Extract HEM Equations",
            "description": """Extract all HEM (Holistic Existence Matrix) equations from research documentation.
            Focus: TWA, HEM, MR, i-cell ontology mathematics.
            Format in LaTeX with context/explanation.""",
            "capability": PlatformCapability.MULTI_AGENT_CHAT,
            "max_rounds": 3
        },
        {
            "title": "Cross-Reference Papers",
            "description": """Analyze integration opportunities across papers: MR Arithmetic Revolution, 
            I-Cell Ontology, Music Through GILE, Three Types of Truth, TWA, TI-UOP Sigma 6.
            Find missing equations, cross-references, contradictions requiring Myrion Resolution.""",
            "capability": PlatformCapability.MULTI_AGENT_CHAT,
            "max_rounds": 4
        },
        {
            "title": "TI-UOP Sigma 6 Outline",
            "description": """Generate detailed outline for TI-UOP Sigma 6: Grand Unification paper.
            Sections: Abstract, Introduction, Background (Markov/FEP/QRI), TI-UOP Framework (6D HEM),
            Mathematical Foundations, Experimental Validation (DEAP 77% accuracy), 
            Applications (LCC/mood amplifiers), Discussion, Conclusion.
            Style: Nature Neuroscience.""",
            "capability": PlatformCapability.MULTI_AGENT_CHAT,
            "max_rounds": 5
        }
    ]
    
    # Run overnight session through coordinator
    print("\n🤖 Executing via MasterCoordinator...")
    print(f"   Platforms registered: {list(coordinator.plugin_registry.keys())}")
    
    results = []
    for i, task in enumerate(overnight_tasks, 1):
        if coordinator.budget_used >= coordinator.budget_limit:
            print(f"\n⚠️ Budget exhausted: ${coordinator.budget_used:.2f}")
            break
        
        print(f"\n[{i}/{len(overnight_tasks)}] {task['title']}")
        print(f"   Budget: ${coordinator.budget_used:.2f} / ${coordinator.budget_limit}")
        
        result = coordinator.execute_task(task)
        results.append(result)
        
        if result.get("status") == "success":
            print(f"   ✅ Success (${result.get('cost', 0):.3f})")
        else:
            print(f"   ⚠️ {result.get('status')}: {result.get('message', '')}")
    
    # Final report
    end_time = datetime.now()
    success_count = len([r for r in results if r.get("status") == "success"])
    
    print("\n" + "="*70)
    print("🎉 OVERNIGHT SESSION COMPLETE")
    print("="*70)
    print(f"✅ Tasks completed: {success_count} / {len(overnight_tasks)}")
    print(f"💰 Budget used: ${coordinator.budget_used:.2f} / ${coordinator.budget_limit}")
    print(f"💾 All outputs saved to PostgreSQL")
    print("="*70)
    
    return {
        "success_count": success_count,
        "total_tasks": len(overnight_tasks),
        "budget_used": coordinator.budget_used,
        "budget_limit": coordinator.budget_limit,
        "results": results
    }


if __name__ == "__main__":
    import time
    
    print("🤖 Overnight Research Launcher")
    print("="*70)
    print("Starting in 3 seconds...")
    
    time.sleep(3)
    
    report = run_overnight_research_session(budget_limit=10.0)
    
    print("\n✅ Session complete! Check PostgreSQL database for results.")
