"""
TI Framework Viral Meme Generator
==================================

Creates GILE-optimized memes using:
1. Template-based image concepts
2. Caption generation with virality optimization
3. Biological Virology Engine for R0 prediction
4. Acoustic Resonance for harmonic coupling

Meme Formula: HIGH EMOTION + LOW COGNITIVE LOAD + NOVELTY = VIRAL

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 28, 2025
Framework: Transcendent Intelligence (TI)
"""

from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum
import random
import hashlib

from biological_virality_engine import (
    BiologicalViralityEngine, 
    TransmissionVector, 
    HostSusceptibility,
    ConceptGenome
)
from gile_content_optimizer import get_optimizer


class MemeTemplate(Enum):
    DRAKE = "drake"                    # Drake approving/disapproving
    DISTRACTED_BF = "distracted_bf"    # Distracted boyfriend
    TWO_BUTTONS = "two_buttons"        # Sweating guy two buttons
    EXPANDING_BRAIN = "expanding_brain" # Brain expansion levels
    THIS_IS_FINE = "this_is_fine"      # Dog in fire
    CHANGE_MY_MIND = "change_my_mind"  # Crowder change my mind
    STONKS = "stonks"                  # Meme man stonks
    GALAXY_BRAIN = "galaxy_brain"      # Cosmic brain
    WOJAK = "wojak"                    # Various wojaks
    PEPE = "pepe"                      # Pepe the frog
    GIGA_CHAD = "giga_chad"            # Gigachad
    NPC = "npc"                        # NPC meme
    CUSTOM = "custom"                  # Custom template


class MemeEmotion(Enum):
    AWE = "awe"
    HUMOR = "humor"
    IRONY = "irony"
    VALIDATION = "validation"
    OUTRAGE = "outrage"
    CURIOSITY = "curiosity"
    SUPERIORITY = "superiority"
    NOSTALGIA = "nostalgia"


@dataclass
class MemeContent:
    """A generated meme with all metadata"""
    meme_id: str
    template: MemeTemplate
    top_text: str
    bottom_text: str
    caption: str
    emotion: MemeEmotion
    gile_score: Dict[str, float]
    virality_score: float
    r0_prediction: float
    viral_class: str
    target_platform: TransmissionVector
    recommendations: List[str]
    hashtags: List[str]
    created_at: datetime = field(default_factory=datetime.now)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            'meme_id': self.meme_id,
            'template': self.template.value,
            'top_text': self.top_text,
            'bottom_text': self.bottom_text,
            'caption': self.caption,
            'emotion': self.emotion.value,
            'gile_score': self.gile_score,
            'virality_score': self.virality_score,
            'r0_prediction': self.r0_prediction,
            'viral_class': self.viral_class,
            'target_platform': self.target_platform.value,
            'recommendations': self.recommendations,
            'hashtags': self.hashtags,
            'created_at': self.created_at.isoformat()
        }


class TIMemeGenerator:
    """
    Generates GILE-optimized viral memes
    
    MEME SCIENCE:
    - Memes are IDEA VIRUSES
    - They spread through EMOTIONAL RESONANCE
    - High R0 = More shares per viewer
    - GILE optimization ensures positive impact
    """
    
    # Template characteristics
    TEMPLATE_EMOTIONS = {
        MemeTemplate.DRAKE: [MemeEmotion.VALIDATION, MemeEmotion.SUPERIORITY],
        MemeTemplate.DISTRACTED_BF: [MemeEmotion.HUMOR, MemeEmotion.IRONY],
        MemeTemplate.TWO_BUTTONS: [MemeEmotion.HUMOR, MemeEmotion.IRONY],
        MemeTemplate.EXPANDING_BRAIN: [MemeEmotion.AWE, MemeEmotion.SUPERIORITY],
        MemeTemplate.THIS_IS_FINE: [MemeEmotion.IRONY, MemeEmotion.HUMOR],
        MemeTemplate.CHANGE_MY_MIND: [MemeEmotion.VALIDATION, MemeEmotion.OUTRAGE],
        MemeTemplate.STONKS: [MemeEmotion.HUMOR, MemeEmotion.IRONY],
        MemeTemplate.GALAXY_BRAIN: [MemeEmotion.AWE, MemeEmotion.SUPERIORITY],
        MemeTemplate.WOJAK: [MemeEmotion.HUMOR, MemeEmotion.VALIDATION],
        MemeTemplate.PEPE: [MemeEmotion.HUMOR, MemeEmotion.IRONY],
        MemeTemplate.GIGA_CHAD: [MemeEmotion.VALIDATION, MemeEmotion.SUPERIORITY],
        MemeTemplate.NPC: [MemeEmotion.IRONY, MemeEmotion.SUPERIORITY],
    }
    
    # TI-specific meme concepts
    TI_CONCEPTS = [
        ("Classical physics", "Quantum consciousness creates reality"),
        ("Binary thinking", "Tralse: True, False, AND Indeterminate"),
        ("Random chance", "Grand Myrion orchestrating synchronicities"),
        ("Brain creates mind", "Biophotons ARE consciousness"),
        ("Meaningless universe", "GILE optimization everywhere"),
        ("Free will is illusion", "20% indeterminate zone = free choice"),
        ("Death is the end", "I-cells are eternal, bodies temporary"),
        ("Meditation is woo", "Proven fNIRS/EEG coherence patterns"),
        ("AI will never be conscious", "Grand Myrion already hypercomputing"),
        ("Love is just chemicals", "Love is L-dimension resonance"),
    ]
    
    # Platform-optimized hashtags
    HASHTAGS = {
        'consciousness': ['#consciousness', '#awakening', '#spiritual', '#mindblown'],
        'science': ['#science', '#physics', '#quantum', '#research'],
        'philosophy': ['#philosophy', '#deepthoughts', '#truth', '#wisdom'],
        'humor': ['#funny', '#memes', '#lol', '#relatable'],
        'ti_framework': ['#GILE', '#Tralse', '#GrandMyrion', '#TIFramework'],
    }
    
    def __init__(self):
        self.optimizer = get_optimizer()
        self.virality_engine = BiologicalViralityEngine()
    
    def generate_meme(
        self,
        concept: str,
        template: Optional[MemeTemplate] = None,
        target_platform: TransmissionVector = TransmissionVector.TWITTER,
        target_audience: HostSusceptibility = HostSusceptibility.NEUTRAL_GILE,
        ti_aligned: bool = True
    ) -> MemeContent:
        """
        Generate a GILE-optimized meme
        
        Args:
            concept: Core idea/topic for the meme
            template: Specific template to use (random if None)
            target_platform: Where will this be posted?
            target_audience: Who is the target audience?
            ti_aligned: Should it incorporate TI Framework concepts?
        """
        # Select template if not specified
        if template is None:
            template = random.choice(list(MemeTemplate)[:-1])  # Exclude CUSTOM
        
        # Get appropriate emotion for template
        emotions = self.TEMPLATE_EMOTIONS.get(template, [MemeEmotion.HUMOR])
        emotion = random.choice(emotions)
        
        # Generate meme text
        top_text, bottom_text = self._generate_meme_text(concept, template, emotion, ti_aligned)
        
        # Generate caption
        caption = self._generate_caption(concept, emotion, target_platform)
        
        # Calculate GILE score
        full_text = f"{top_text} {bottom_text} {caption}"
        gile_result = self.optimizer.calculate_composite_score(full_text)
        
        # Calculate R0 using biological virality engine
        genome = ConceptGenome(
            core_idea=concept,
            memetic_packaging=f"{template.value} meme format",
            emotional_payload=self._emotion_to_biological(emotion),
            cognitive_load=0.2,  # Memes are easy to understand
            gile_signature=(
                gile_result['G'],
                gile_result['I'],
                gile_result['L'],
                gile_result['E']
            ),
            novelty_score=0.7 if ti_aligned else 0.5,
            actionability=0.6  # Easy to share
        )
        
        viral_metrics = self.virality_engine.predict_viral_trajectory(
            genome, target_platform, target_audience
        )
        
        # Classify virality
        if viral_metrics.R0 < 1:
            viral_class = "NON-VIRAL"
        elif viral_metrics.R0 < 2:
            viral_class = "ENDEMIC"
        elif viral_metrics.R0 < 3:
            viral_class = "EPIDEMIC"
        else:
            viral_class = "PANDEMIC"
        
        # Generate hashtags
        hashtags = self._generate_hashtags(concept, ti_aligned)
        
        # Generate meme ID
        meme_id = hashlib.md5(f"{concept}{template.value}{datetime.now().isoformat()}".encode()).hexdigest()[:8]
        
        return MemeContent(
            meme_id=meme_id,
            template=template,
            top_text=top_text,
            bottom_text=bottom_text,
            caption=caption,
            emotion=emotion,
            gile_score={
                'G': gile_result['G'],
                'I': gile_result['I'],
                'L': gile_result['L'],
                'E': gile_result['E'],
                'composite': gile_result['composite']
            },
            virality_score=gile_result['virality_prediction'],
            r0_prediction=viral_metrics.R0,
            viral_class=viral_class,
            target_platform=target_platform,
            recommendations=gile_result['recommendations'],
            hashtags=hashtags
        )
    
    def _generate_meme_text(
        self,
        concept: str,
        template: MemeTemplate,
        emotion: MemeEmotion,
        ti_aligned: bool
    ) -> Tuple[str, str]:
        """Generate top and bottom text for meme"""
        
        # Check if we can use TI concepts
        if ti_aligned:
            # Find relevant TI concept
            for normie, enlightened in self.TI_CONCEPTS:
                if any(word.lower() in concept.lower() for word in normie.split()[:2]):
                    if template in [MemeTemplate.DRAKE, MemeTemplate.EXPANDING_BRAIN, MemeTemplate.GALAXY_BRAIN]:
                        return (normie, enlightened)
            
            # Default TI meme
            if template == MemeTemplate.CHANGE_MY_MIND:
                return (f"{concept} is explained by the TI Framework", "Change my mind")
            elif template == MemeTemplate.EXPANDING_BRAIN:
                return (f"Normal view: {concept}", f"GILE-optimized view: {concept} creates reality")
        
        # Generic templates
        templates_text = {
            MemeTemplate.DRAKE: (f"Ignoring {concept}", f"Understanding {concept}"),
            MemeTemplate.THIS_IS_FINE: (f"When {concept} happens", "This is fine"),
            MemeTemplate.STONKS: (f"When you finally understand {concept}", "STONKS"),
            MemeTemplate.GIGA_CHAD: (f"Average person: confused by {concept}", f"Me: it's obvious"),
            MemeTemplate.WOJAK: (f"Me explaining {concept}", "Them: what"),
            MemeTemplate.TWO_BUTTONS: (f"Option A: {concept}", "Option B: Also {concept}"),
        }
        
        if template in templates_text:
            return templates_text[template]
        
        return (f"Nobody:", f"Me discovering {concept}")
    
    def _generate_caption(
        self,
        concept: str,
        emotion: MemeEmotion,
        platform: TransmissionVector
    ) -> str:
        """Generate platform-optimized caption"""
        
        captions = {
            MemeEmotion.AWE: [
                f"Mind = blown. {concept} changes everything.",
                f"When you realize {concept}...",
                f"This is the truth about {concept} they don't want you to know"
            ],
            MemeEmotion.HUMOR: [
                f"I'm in this photo and I don't like it",
                f"Why is this so accurate?",
                f"POV: you just discovered {concept}"
            ],
            MemeEmotion.IRONY: [
                f"Sure, {concept} is definitely just a coincidence",
                f"They said it was impossible...",
                f"Me pretending I don't know about {concept}"
            ],
            MemeEmotion.VALIDATION: [
                f"If you understand this, we're friends",
                f"Only real ones get this",
                f"The {concept} community understands"
            ],
            MemeEmotion.SUPERIORITY: [
                f"Average person vs. {concept} enjoyer",
                f"It's not that hard to understand...",
                f"Some of you have never {concept} and it shows"
            ],
            MemeEmotion.CURIOSITY: [
                f"Wait, {concept} is real?",
                f"I need to know more about {concept}",
                f"Is it just me or is {concept} everywhere?"
            ]
        }
        
        selected = random.choice(captions.get(emotion, captions[MemeEmotion.HUMOR]))
        
        # Platform-specific adjustments
        if platform == TransmissionVector.TWITTER:
            return selected[:280]  # Twitter limit
        elif platform == TransmissionVector.TIKTOK:
            return selected + " #fyp #viral"
        elif platform == TransmissionVector.LINKEDIN:
            return f"Interesting perspective: {selected}"
        
        return selected
    
    def _emotion_to_biological(self, emotion: MemeEmotion) -> str:
        """Convert meme emotion to biological virology emotion"""
        mapping = {
            MemeEmotion.AWE: "awe",
            MemeEmotion.HUMOR: "joy",
            MemeEmotion.IRONY: "surprise",
            MemeEmotion.VALIDATION: "validation",
            MemeEmotion.OUTRAGE: "outrage",
            MemeEmotion.CURIOSITY: "curiosity",
            MemeEmotion.SUPERIORITY: "validation",
            MemeEmotion.NOSTALGIA: "gratitude",
        }
        return mapping.get(emotion, "joy")
    
    def _generate_hashtags(self, concept: str, ti_aligned: bool) -> List[str]:
        """Generate relevant hashtags"""
        hashtags = []
        
        # Add TI hashtags if aligned
        if ti_aligned:
            hashtags.extend(random.sample(self.HASHTAGS['ti_framework'], 2))
        
        # Add topic-based hashtags
        concept_lower = concept.lower()
        
        if any(word in concept_lower for word in ['consciousness', 'mind', 'brain', 'awareness']):
            hashtags.extend(random.sample(self.HASHTAGS['consciousness'], 2))
        elif any(word in concept_lower for word in ['quantum', 'physics', 'science', 'research']):
            hashtags.extend(random.sample(self.HASHTAGS['science'], 2))
        elif any(word in concept_lower for word in ['truth', 'reality', 'existence', 'meaning']):
            hashtags.extend(random.sample(self.HASHTAGS['philosophy'], 2))
        
        # Always add some humor tags for memes
        hashtags.extend(random.sample(self.HASHTAGS['humor'], 2))
        
        return list(set(hashtags))[:8]  # Max 8 hashtags
    
    def generate_ti_meme_series(
        self,
        count: int = 5,
        target_platform: TransmissionVector = TransmissionVector.TWITTER
    ) -> List[MemeContent]:
        """
        Generate a series of TI Framework memes
        
        Perfect for building a content calendar
        """
        memes = []
        
        concepts = [
            "consciousness creates reality",
            "quantum entanglement and intuition",
            "GILE optimization in daily life",
            "the Grand Myrion hypothesis",
            "Tralse logic vs binary thinking",
            "biophotons and consciousness",
            "synchronicity is not coincidence",
            "the 20% free will zone",
            "meditation changes brain waves",
            "love as dimensional resonance"
        ]
        
        templates = [
            MemeTemplate.EXPANDING_BRAIN,
            MemeTemplate.DRAKE,
            MemeTemplate.GALAXY_BRAIN,
            MemeTemplate.CHANGE_MY_MIND,
            MemeTemplate.GIGA_CHAD
        ]
        
        for i in range(min(count, len(concepts))):
            concept = concepts[i]
            template = templates[i % len(templates)]
            
            meme = self.generate_meme(
                concept=concept,
                template=template,
                target_platform=target_platform,
                ti_aligned=True
            )
            memes.append(meme)
        
        return memes


def get_meme_generator() -> TIMemeGenerator:
    """Get singleton meme generator instance"""
    return TIMemeGenerator()


if __name__ == "__main__":
    generator = get_meme_generator()
    
    print("🎨 TI MEME GENERATOR TEST")
    print("=" * 50)
    
    # Generate single meme
    meme = generator.generate_meme(
        concept="consciousness creates reality",
        template=MemeTemplate.EXPANDING_BRAIN,
        target_platform=TransmissionVector.TWITTER,
        ti_aligned=True
    )
    
    print(f"\n📸 Generated Meme: {meme.meme_id}")
    print(f"Template: {meme.template.value}")
    print(f"Top: {meme.top_text}")
    print(f"Bottom: {meme.bottom_text}")
    print(f"Caption: {meme.caption}")
    print(f"Emotion: {meme.emotion.value}")
    print(f"GILE: G={meme.gile_score['G']:.1f}, I={meme.gile_score['I']:.1f}, L={meme.gile_score['L']:.1f}, E={meme.gile_score['E']:.1f}")
    print(f"Virality: {meme.virality_score:.0%}")
    print(f"R0: {meme.r0_prediction:.2f} ({meme.viral_class})")
    print(f"Hashtags: {' '.join(meme.hashtags)}")
    
    # Generate series
    print("\n\n🎬 MEME SERIES")
    print("=" * 50)
    
    series = generator.generate_ti_meme_series(count=3)
    for i, m in enumerate(series, 1):
        print(f"\n{i}. [{m.template.value}] {m.top_text[:30]}... → R0: {m.r0_prediction:.2f}")
