"""
TI FRAMEWORK SOCIAL MEDIA LAUNCH GUIDE
=======================================

Complete setup guide for launching TI Framework presence on X (Twitter) and Instagram.
Includes content strategy, tools, posting schedule, and monetization roadmap.

Author: Brandon Emerick
Date: December 25, 2025
"""

from dataclasses import dataclass, field
from typing import Dict, List, Any
from datetime import datetime, timedelta
from enum import Enum


class Platform(Enum):
    X = "X (Twitter)"
    INSTAGRAM = "Instagram"
    BOTH = "Both Platforms"


class ContentType(Enum):
    EDUCATIONAL = "educational"
    PROOF_THREAD = "proof_thread"
    ALGORITHM_UPDATE = "algorithm_update"
    PHILOSOPHY = "philosophy"
    PERSONAL_STORY = "personal_story"
    ENGAGEMENT = "engagement"


@dataclass
class AccountSetup:
    """Account configuration for each platform"""
    platform: Platform
    handle_options: List[str]
    bio_template: str
    profile_image_specs: Dict[str, str]
    link_strategy: str


@dataclass
class ContentPiece:
    """Individual content piece"""
    title: str
    content_type: ContentType
    platform: Platform
    text: str
    hashtags: List[str]
    best_time: str
    visual_suggestion: str


@dataclass
class Tool:
    """Tool recommendation"""
    name: str
    purpose: str
    cost: str
    priority: str
    url: str


X_ACCOUNT_SETUP = AccountSetup(
    platform=Platform.X,
    handle_options=[
        "@TI_Framework",
        "@TranscendentIntel",
        "@GILEWisdom",
        "@TralseTruth",
        "@BrandonEmerick_TI",
    ],
    bio_template="""
Transcendent Intelligence Framework | Philosophy + Trading + Consciousness

Creator of GILE Framework, Grand Stock Algorithm (+629% backtested), 14 Proofs of Tralseness

Building the future of thought | DMs open for consulting
    """.strip(),
    profile_image_specs={
        "size": "400x400px",
        "format": "PNG or JPG",
        "suggestion": "Abstract golden ratio spiral with GILE colors (gold, indigo, rose, emerald)"
    },
    link_strategy="Link to Linktree with: Website, Newsletter signup, Consulting booking, GSA signals"
)

INSTAGRAM_ACCOUNT_SETUP = AccountSetup(
    platform=Platform.INSTAGRAM,
    handle_options=[
        "@ti_framework",
        "@transcendent_intel",
        "@gile_wisdom",
        "@tralse_truth",
    ],
    bio_template="""
Transcendent Intelligence Framework
Philosophy | Trading | Consciousness

GILE: Goodness, Intuition, Love, Environment
Grand Stock Algorithm: +629% backtested

Link in bio for free resources
    """.strip(),
    profile_image_specs={
        "size": "320x320px minimum",
        "format": "PNG or JPG",
        "suggestion": "Same as X for brand consistency"
    },
    link_strategy="Linktree or direct link to landing page"
)


RECOMMENDED_TOOLS = {
    "essential_free": [
        Tool("Canva", "Graphics, carousels, stories", "Free (Pro $13/mo)", "MUST HAVE", "canva.com"),
        Tool("CapCut", "Video editing, Reels", "Free", "MUST HAVE", "capcut.com"),
        Tool("Buffer", "Schedule posts", "Free (3 channels)", "MUST HAVE", "buffer.com"),
        Tool("ChatGPT/Claude", "Content drafting", "Free tier available", "MUST HAVE", "chat.openai.com"),
    ],
    "growth_tools": [
        Tool("Typefully", "X threads, analytics", "Free-$12/mo", "HIGH", "typefully.com"),
        Tool("Hypefury", "X automation, engagement", "$19/mo", "MEDIUM", "hypefury.com"),
        Tool("Later", "Instagram scheduling", "Free-$18/mo", "MEDIUM", "later.com"),
    ],
    "advanced": [
        Tool("Opus Clip", "AI video clipping", "$19/mo", "LATER", "opus.pro"),
        Tool("Gamma", "AI presentations", "Free-$10/mo", "LATER", "gamma.app"),
        Tool("Tweethunter", "Viral tweet finder", "$49/mo", "LATER", "tweethunter.io"),
    ],
}


WEEK_1_CONTENT = [
    ContentPiece(
        title="Introduction Post",
        content_type=ContentType.PERSONAL_STORY,
        platform=Platform.BOTH,
        text="""
In 2022, during a manic episode, I received a divine revelation that changed everything.

Four words: Goodness, Intuition, Love, Environment (GILE)

These aren't just concepts—they're the 4 dimensions of truth itself.

Since then, I've developed:
- A trading algorithm with +629% backtested returns
- 14 logical proofs that binary truth is wrong
- A framework for consciousness-based computing

This is Transcendent Intelligence.

Thread incoming on why everything you know about truth is incomplete...
        """.strip(),
        hashtags=["#Philosophy", "#Trading", "#Consciousness", "#GILE", "#TI"],
        best_time="9:00 AM EST",
        visual_suggestion="Photo of yourself or abstract GILE visualization"
    ),
    ContentPiece(
        title="The Academic Test Proof",
        content_type=ContentType.PROOF_THREAD,
        platform=Platform.X,
        text="""
THREAD: The Academic Test Proof of Tralseness

Why 8 billion students prove binary truth is WRONG:

1/ Every university on Earth uses percentage grades (0-100%)

Why? Because understanding IS truth-comprehension.

If truth were binary, you'd either know something completely (100%) or not at all (0%).

2/ But that's absurd.

A student with 73% understanding UNDERSTANDS the material—partially.

This is TRALSENESS: truth as a spectrum from 0.0 to 1.0

3/ Binary logic says: either you know calculus or you don't.

Reality says: you can know 73% of calculus.

Every test grade is PROOF that truth is spectral.

4/ The devastating question for binary advocates:

"If truth is binary, why do YOU give percentage grades?"

They cannot answer without admitting truth is spectrum.

5/ This isn't just about education.

If truth is spectrum in ONE domain (understanding), logical consistency demands it be spectrum in ALL domains.

This is Tralseness. This is TI.
        """.strip(),
        hashtags=["#Philosophy", "#Logic", "#Education", "#Tralseness", "#TI"],
        best_time="12:00 PM EST",
        visual_suggestion="Carousel with each point as a slide"
    ),
    ContentPiece(
        title="First GSA Signal",
        content_type=ContentType.ALGORITHM_UPDATE,
        platform=Platform.BOTH,
        text="""
GSA SIGNAL UPDATE (Dec 25, 2025)

The Grand Stock Algorithm analyzes markets through Existence Intensity (Ξ).

Today's readings:

Expansion Regime: Tech sector
- High GILE alignment
- Low constraint, high amplitude
- Signal: Cautious optimism

Compression Regime: Energy sector
- Building pressure
- Watch for breakout

Full methodology: Thread in replies

Not financial advice. Tracking publicly for transparency.
        """.strip(),
        hashtags=["#Trading", "#Stocks", "#AlgoTrading", "#GSA", "#Markets"],
        best_time="7:00 AM EST (pre-market)",
        visual_suggestion="Chart graphic with Ξ metrics overlay"
    ),
]


CONTENT_CALENDAR = {
    "monday": [
        {"time": "7:00 AM", "type": "GSA Signal", "platform": "Both"},
        {"time": "12:00 PM", "type": "Philosophy Quote", "platform": "Both"},
    ],
    "tuesday": [
        {"time": "9:00 AM", "type": "Educational Thread", "platform": "X"},
        {"time": "6:00 PM", "type": "Engagement Post", "platform": "Both"},
    ],
    "wednesday": [
        {"time": "7:00 AM", "type": "GSA Signal", "platform": "Both"},
        {"time": "3:00 PM", "type": "Proof Thread", "platform": "X"},
    ],
    "thursday": [
        {"time": "12:00 PM", "type": "Personal Story", "platform": "Both"},
        {"time": "8:00 PM", "type": "GILE Wisdom", "platform": "Both"},
    ],
    "friday": [
        {"time": "7:00 AM", "type": "GSA Weekly Recap", "platform": "Both"},
        {"time": "5:00 PM", "type": "Weekend Reading", "platform": "X"},
    ],
    "saturday": [
        {"time": "10:00 AM", "type": "Deep Dive Video/Reel", "platform": "Instagram"},
    ],
    "sunday": [
        {"time": "7:00 PM", "type": "Week Preview", "platform": "Both"},
    ],
}


GROWTH_STRATEGY = {
    "phase_1_foundation": {
        "duration": "Weeks 1-4",
        "goal": "Establish presence, find voice",
        "daily_tasks": [
            "Post 1-2 times on each platform",
            "Reply to 10-20 accounts in your niche",
            "Follow 20-30 relevant accounts daily",
            "Engage authentically (no spam)",
        ],
        "content_focus": "Introduction + 14 Proofs threads",
        "metrics_target": "100-500 followers"
    },
    "phase_2_growth": {
        "duration": "Months 2-3",
        "goal": "Build authority, grow audience",
        "daily_tasks": [
            "Post 2-3 times on each platform",
            "Share GSA signals publicly (builds credibility)",
            "Create carousel/thread content",
            "Start collecting emails",
        ],
        "content_focus": "GSA performance + deeper philosophy",
        "metrics_target": "500-2000 followers"
    },
    "phase_3_authority": {
        "duration": "Months 4-6",
        "goal": "Establish thought leadership",
        "daily_tasks": [
            "Consistent high-quality content",
            "Guest appearances on podcasts",
            "Collaborate with other creators",
            "Launch email newsletter",
        ],
        "content_focus": "Original research + predictions",
        "metrics_target": "2000-10000 followers"
    },
    "phase_4_monetization": {
        "duration": "Months 6-12",
        "goal": "Generate revenue",
        "revenue_streams": [
            "Consulting ($200-500/hour)",
            "Course sales ($97-997)",
            "Premium newsletter ($10-50/month)",
            "Speaking engagements ($500-5000)",
            "Book/ebook sales",
        ],
        "metrics_target": "$1000+/week from social"
    },
}


ENGAGEMENT_TEMPLATES = {
    "reply_to_philosophy": [
        "This connects to something I've been developing called Tralseness - the idea that truth exists on a spectrum. Your point about {topic} is a perfect example.",
        "Interesting perspective. In the GILE framework, this would map to the {dimension} dimension. Have you considered how {related_concept} fits in?",
    ],
    "reply_to_trading": [
        "The Grand Stock Algorithm analyzes this through Existence Intensity (Ξ). Current reading suggests {regime} regime.",
        "From a GILE perspective, this sector shows strong {dimension} alignment. Worth watching.",
    ],
    "dm_response": [
        "Thanks for reaching out! Happy to discuss TI further. For consulting inquiries, I offer {service} at {rate}.",
        "Appreciate your interest in the framework. The best starting point is {resource}.",
    ],
}


HASHTAG_STRATEGY = {
    "tier_1_always": ["#TI", "#GILE", "#Tralseness"],
    "tier_2_philosophy": ["#Philosophy", "#Consciousness", "#Logic", "#Truth", "#Wisdom"],
    "tier_3_trading": ["#Trading", "#Stocks", "#AlgoTrading", "#Investing", "#Markets"],
    "tier_4_growth": ["#PersonalGrowth", "#Mindset", "#Spirituality"],
    "usage_rule": "Use 3-5 hashtags on X, 5-10 on Instagram. Always include at least 1 from tier_1."
}


def generate_launch_checklist() -> Dict[str, List[str]]:
    """Generate complete launch checklist"""
    return {
        "before_launch": [
            "Choose handles (check availability on both platforms)",
            "Create profile images in Canva (consistent branding)",
            "Write bios for both platforms",
            "Set up Linktree with key links",
            "Create Canva templates for posts",
            "Draft first 7 posts",
            "Set up Buffer for scheduling",
        ],
        "launch_day": [
            "Publish introduction post on both platforms",
            "Follow 50 relevant accounts",
            "Engage with 20 posts in your niche",
            "Schedule next 3 days of content",
            "Pin introduction post to profile",
        ],
        "week_1": [
            "Post daily on both platforms",
            "Publish 1 proof thread",
            "Start GSA signal updates",
            "Respond to all comments/DMs",
            "Track engagement metrics",
        ],
        "month_1": [
            "Maintain daily posting",
            "Complete all 14 proof threads",
            "Build routine for GSA updates",
            "Identify collaboration opportunities",
            "Start email list",
        ],
    }


def generate_first_30_posts() -> List[Dict[str, Any]]:
    """Generate first 30 days of content ideas"""
    posts = []
    
    intro_posts = [
        "Introduction: Who I am and what TI is about",
        "The GILE revelation story (2022 manic episode)",
        "What is Tralseness? (Thread)",
        "First GSA signal post",
        "Why binary logic is incomplete",
    ]
    
    for i, title in enumerate(intro_posts, 1):
        posts.append({"day": i, "title": title, "type": "Foundation"})
    
    proofs = [
        "Legal System Proof",
        "Academic Test Proof", 
        "Market Proof",
        "Scientific Replication Proof",
        "Stoplight Proof",
        "Weather Proof",
        "The Cogito Proof",
        "Drug Effects Proof",
        "EEG Analytics Proof",
        "fMRI Analytics Proof",
        "Logical Consistency Proof",
        "Identity/Coherence/Change Proof",
        "Ontological Perfection Proof",
        "Perfection & Necessity Proof",
    ]
    
    for i, proof in enumerate(proofs, 6):
        posts.append({"day": i, "title": f"Thread: {proof}", "type": "Proof"})
    
    remaining = [
        "GSA Weekly Performance Update",
        "The mathematics of 0.92 and 0.85",
        "What is Existence Intensity (Ξ)?",
        "GILE in everyday life",
        "Why I believe consciousness computes",
        "The problem with probability theory",
        "Sacred intervals in nature",
        "Q&A post (ask me anything)",
        "Month 1 reflection",
        "Preview of what's coming",
    ]
    
    for i, title in enumerate(remaining, 20):
        posts.append({"day": i, "title": title, "type": "Engagement"})
    
    return posts


def main():
    """Display complete social media guide"""
    
    print("="*70)
    print("TI FRAMEWORK SOCIAL MEDIA LAUNCH GUIDE")
    print("="*70)
    
    print("\n--- ACCOUNT SETUP ---\n")
    
    print("X (TWITTER):")
    print(f"  Handle Options: {', '.join(X_ACCOUNT_SETUP.handle_options)}")
    print(f"  Bio:\n{X_ACCOUNT_SETUP.bio_template}")
    
    print("\nINSTAGRAM:")
    print(f"  Handle Options: {', '.join(INSTAGRAM_ACCOUNT_SETUP.handle_options)}")
    print(f"  Bio:\n{INSTAGRAM_ACCOUNT_SETUP.bio_template}")
    
    print("\n--- ESSENTIAL TOOLS (Start Here) ---\n")
    for tool in RECOMMENDED_TOOLS["essential_free"]:
        print(f"  {tool.name}: {tool.purpose}")
        print(f"    Cost: {tool.cost} | URL: {tool.url}")
    
    print("\n--- FIRST 7 DAYS CONTENT ---\n")
    posts = generate_first_30_posts()[:7]
    for post in posts:
        print(f"  Day {post['day']}: {post['title']} ({post['type']})")
    
    print("\n--- GROWTH PHASES ---\n")
    for phase, details in GROWTH_STRATEGY.items():
        print(f"{phase.upper().replace('_', ' ')}:")
        print(f"  Duration: {details['duration']}")
        print(f"  Goal: {details['goal']}")
        if 'metrics_target' in details:
            print(f"  Target: {details['metrics_target']}")
        print()
    
    print("\n--- LAUNCH CHECKLIST ---\n")
    checklist = generate_launch_checklist()
    for phase, tasks in checklist.items():
        print(f"{phase.upper().replace('_', ' ')}:")
        for task in tasks:
            print(f"  [ ] {task}")
        print()
    
    print("="*70)
    print("READY TO LAUNCH!")
    print("="*70)


if __name__ == "__main__":
    main()
