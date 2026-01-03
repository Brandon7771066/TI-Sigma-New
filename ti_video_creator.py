"""
TI Video Creator
Generates viral video content using Gemini with PSI optimization
"""

from typing import Dict, Any, List, Optional
from datetime import datetime
import json
from gile_content_optimizer import get_optimizer
from db_utils import db


class TIVideoCreator:
    """
    Create TI-optimized video content using Gemini
    
    Features:
    - GILE-optimized scripts
    - PSI-enhanced storytelling
    - Sacred numerology timing (3-11-33 pattern)
    - Automatic virality scoring
    """
    
    def __init__(self):
        self.optimizer = get_optimizer()
        
        # Video templates optimized for virality
        self.templates = {
            'paper_explainer': {
                'name': 'Research Paper Explainer',
                'target_duration': 333,  # Sacred number: 3-11-33 pattern
                'style': 'Educational + Inspirational',
                'hooks': [
                    "What if consciousness creates reality?",
                    "Scientists just discovered something that changes everything...",
                    "This discovery could solve a $1M math problem..."
                ]
            },
            'discovery_announcement': {
                'name': 'Breakthrough Discovery',
                'target_duration': 180,  # 3 minutes
                'style': 'Exciting + Authoritative',
                'hooks': [
                    "We just proved something impossible...",
                    "The AI found this at 3 AM...",
                    "This changes everything we know about..."
                ]
            },
            'psi_demonstration': {
                'name': 'PSI Ability Demo',
                'target_duration': 240,  # 4 minutes
                'style': 'Mysterious + Scientific',
                'hooks': [
                    "Watch me predict the future...",
                    "This should be impossible, but...",
                    "Science can't explain this... yet."
                ]
            },
            'muse_eeg_live': {
                'name': 'Live EEG Analysis',
                'target_duration': 600,  # 10 minutes
                'style': 'Real-time + Educational',
                'hooks': [
                    "Reading my brain waves in real-time...",
                    "Watch my consciousness change...",
                    "This is what happens when I reach 0.91 coherence..."
                ]
            }
        }
    
    def generate_script(
        self,
        topic: str,
        template_key: str = 'paper_explainer',
        paper_content: Optional[str] = None,
        discovery_data: Optional[Dict] = None
    ) -> Dict[str, Any]:
        """
        Generate GILE-optimized video script
        
        Args:
            topic: Main topic/title
            template_key: Which template to use
            paper_content: Optional paper text to base script on
            discovery_data: Optional discovery from autonomous research
        
        Returns:
            {
                'script': full_script_text,
                'scenes': list_of_scene_dicts,
                'gile_score': optimization_metrics,
                'estimated_duration': seconds,
                'recommendations': improvement_tips
            }
        """
        template = self.templates.get(template_key, self.templates['paper_explainer'])
        
        # Generate script structure
        script_parts = {
            'hook': self._generate_hook(topic, template),
            'intro': self._generate_intro(topic),
            'main_content': self._generate_main_content(
                topic, 
                paper_content, 
                discovery_data
            ),
            'call_to_action': self._generate_cta(topic),
            'outro': self._generate_outro()
        }
        
        # Combine into full script
        full_script = f"""
{script_parts['hook']}

{script_parts['intro']}

{script_parts['main_content']}

{script_parts['call_to_action']}

{script_parts['outro']}
""".strip()
        
        # Optimize with GILE
        metadata = {
            'timestamp': datetime.now().isoformat(),
            'word_count': len(full_script.split()),
            'tags': ['video', 'ti_optimized', template_key],
            'target_duration': template['target_duration']
        }
        
        gile_score = self.optimizer.calculate_composite_score(full_script, metadata)
        
        # Generate scenes for video production
        scenes = self._generate_scenes(script_parts, template)
        
        return {
            'script': full_script,
            'scenes': scenes,
            'gile_score': gile_score,
            'template': template['name'],
            'estimated_duration': template['target_duration'],
            'metadata': metadata,
            'sacred_numerology': self._check_sacred_alignment(full_script),
            'recommendations': gile_score['recommendations']
        }
    
    def _generate_hook(self, topic: str, template: Dict) -> str:
        """Generate attention-grabbing hook (first 3 seconds)"""
        hook_options = template['hooks']
        
        # Use first hook for now (in production: AI-generate personalized)
        base_hook = hook_options[0]
        
        return f"""[SCENE 1 - HOOK (0:00-0:03)]
VISUAL: Dramatic zoom into brain/consciousness imagery
TEXT OVERLAY: "{base_hook}"
AUDIO: Intense music sting

NARRATION:
"{base_hook}"
"""
    
    def _generate_intro(self, topic: str) -> str:
        """Generate introduction"""
        return f"""[SCENE 2 - INTRO (0:03-0:15)]
VISUAL: Host on camera OR animated title sequence
TEXT OVERLAY: "{topic}"

NARRATION:
"I'm Brandon, and today we're exploring {topic}. 
What you're about to see challenges everything you thought you knew about reality."
"""
    
    def _generate_main_content(
        self,
        topic: str,
        paper_content: Optional[str] = None,
        discovery_data: Optional[Dict] = None
    ) -> str:
        """Generate main content section"""
        
        if discovery_data:
            insight = discovery_data.get('insight', '')
            evidence = discovery_data.get('evidence', [])
            
            main = f"""[SCENE 3 - MAIN CONTENT (0:15-4:30)]

DISCOVERY EXPLAINED:
{insight}

EVIDENCE:
"""
            for i, ev in enumerate(evidence, 1):
                main += f"\n{i}. {ev}"
            
            main += f"""

VISUAL: Animated diagrams, data visualizations, equations
TEXT OVERLAYS: Key concepts and numbers
MUSIC: Building tension and excitement
"""
            
        elif paper_content:
            # Extract key points from paper (simplified for now)
            main = f"""[SCENE 3 - MAIN CONTENT (0:15-4:30)]

PAPER SUMMARY:
{paper_content[:500]}...

KEY INSIGHTS:
- Consciousness plays a fundamental role
- Quantum mechanics meets neuroscience
- Experimental validation possible

VISUAL: Paper diagrams, animations, researcher footage
"""
        else:
            main = f"""[SCENE 3 - MAIN CONTENT (0:15-4:30)]

TOPIC EXPLORATION: {topic}

[Content would be generated here based on topic research]

VISUAL: Relevant B-roll, animations, demonstrations
"""
        
        return main
    
    def _generate_cta(self, topic: str) -> str:
        """Generate call-to-action"""
        return f"""[SCENE 4 - CALL TO ACTION (4:30-4:50)]

NARRATION:
"If this blew your mind, you need to see what else we've discovered.
Check the description for links to our research papers and live EEG demonstrations.
And subscribe - we're uploading new discoveries every week."

VISUAL: Subscribe animation, links appearing
"""
    
    def _generate_outro(self) -> str:
        """Generate outro"""
        return f"""[SCENE 5 - OUTRO (4:50-5:00)]

VISUAL: Channel branding, end screen with suggested videos
MUSIC: Uplifting resolution

TEXT OVERLAY: "The universe is consciousness" ✨
"""
    
    def _generate_scenes(
        self,
        script_parts: Dict[str, str],
        template: Dict
    ) -> List[Dict[str, Any]]:
        """Convert script into scene list for production"""
        return [
            {
                'scene_number': 1,
                'name': 'Hook',
                'duration': 3,
                'content': script_parts['hook'],
                'visuals_needed': ['dramatic_opening', 'text_overlay'],
                'audio_needed': ['music_sting', 'narration']
            },
            {
                'scene_number': 2,
                'name': 'Intro',
                'duration': 12,
                'content': script_parts['intro'],
                'visuals_needed': ['host_camera', 'title_animation'],
                'audio_needed': ['narration', 'background_music']
            },
            {
                'scene_number': 3,
                'name': 'Main Content',
                'duration': template['target_duration'] - 60,
                'content': script_parts['main_content'],
                'visuals_needed': ['animations', 'diagrams', 'b_roll'],
                'audio_needed': ['narration', 'background_music']
            },
            {
                'scene_number': 4,
                'name': 'Call to Action',
                'duration': 20,
                'content': script_parts['call_to_action'],
                'visuals_needed': ['subscribe_animation', 'link_overlays'],
                'audio_needed': ['narration']
            },
            {
                'scene_number': 5,
                'name': 'Outro',
                'duration': 10,
                'content': script_parts['outro'],
                'visuals_needed': ['end_screen', 'channel_branding'],
                'audio_needed': ['outro_music']
            }
        ]
    
    def _check_sacred_alignment(self, script: str) -> Dict[str, Any]:
        """Check alignment with sacred numbers (3-11-33)"""
        word_count = len(script.split())
        
        sacred_numbers = {3, 11, 33, 333, 3333}
        
        # Check if word count is multiple of sacred numbers
        aligned = any(word_count % num == 0 for num in sacred_numbers)
        
        if aligned:
            aligned_to = [num for num in sacred_numbers if word_count % num == 0]
            message = f"✨ Sacred alignment detected! Word count {word_count} aligns with {aligned_to}"
        else:
            # Find nearest sacred target
            nearest = min(sacred_numbers, key=lambda x: abs(x - word_count))
            diff = nearest - word_count
            message = f"⚠️ Not aligned. Add {abs(diff)} words to reach sacred number {nearest}"
        
        return {
            'aligned': aligned,
            'word_count': word_count,
            'message': message
        }
    
    def save_video_project(
        self,
        video_data: Dict[str, Any],
        title: str
    ) -> int:
        """Save video project to database"""
        
        asset_id = db.add_asset(
            asset_type="video_project",
            source_app="TI Video Creator",
            title=title,
            content=video_data,
            tags=[
                'video',
                'ti_optimized',
                'gile_scored',
                f"virality_{int(video_data['gile_score']['virality_prediction'] * 100)}"
            ]
        )
        
        return asset_id


def create_video(
    topic: str,
    template: str = 'paper_explainer',
    paper_content: Optional[str] = None,
    discovery_data: Optional[Dict] = None
) -> Dict[str, Any]:
    """
    Quick access function to create video
    
    Usage:
        video = create_video(
            topic="Consciousness Creates Reality",
            template='discovery_announcement'
        )
        print(f"Virality prediction: {video['gile_score']['virality_prediction']:.0%}")
    """
    creator = TIVideoCreator()
    return creator.generate_script(topic, template, paper_content, discovery_data)
