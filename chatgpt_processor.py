"""
ChatGPT History Processor - Simplified Version
Parses and categorizes ChatGPT conversation exports directly in memory.
"""

import json
from datetime import datetime
from typing import List, Dict
from collections import defaultdict

class ChatGPTProcessor:
    """Process and categorize ChatGPT conversation exports."""
    
    # Concept categorization keywords
    CONCEPT_KEYWORDS = {
        'TWA_tralse_algebra': [
            'tralse', 'wave algebra', 'TWA', 'quadruplet', 'codex', 
            'tralse wave', 'tralse-false', 'tralse function'
        ],
        'icells_ontology': [
            'i-cell', 'icell', 'informational cell', 'i-cell characteristics',
            'shell', 'sprout', 'bless', 'signature', 'heartbeat'
        ],
        'myrion_resolution': [
            'myrion', 'resolution', 'contradiction', 'permissibility distribution',
            'PD', 'rho parameter', 'synergy', 'myrion spiral'
        ],
        'CCC_consciousness': [
            'CCC', 'central cosmic consciousness', 'blessing', 'actualization',
            'divine', 'prophecy', 'spacetime before big bang'
        ],
        'quantum_mechanisms': [
            'quantum', 'entanglement', 'Bell', 'CHSH', 'superposition',
            'wave function', 'quantum coherence', 'quantum biology'
        ],
        'mathematical_proofs': [
            'proof', 'theorem', 'mathematical', 'equation', 'formula',
            'logarithm', 'optimization', 'margin of error', 'RNG', 'Psi'
        ],
        'sigma_evolution': [
            'sigma', 'sigma 5', 'sigma 6', 'ti-uop', 'TI-UOP',
            'singularity', 'framework evolution'
        ],
        'patents_applications': [
            'patent', 'application', 'commercial', 'product', 
            'implementation', 'practical use', 'business model'
        ],
        'verisyn_coherence': [
            'verisyn', 'coherence', 'cosmic unification', 'harmony',
            'resonance gain', 'phase lock', 'harmonic'
        ],
        'resonance_mechanisms': [
            'resonate', 'resonance', 'genome', 'simulation', 'fuse',
            'split', 'rebase', 'operator'
        ],
        'biophotons_EM': [
            'biophoton', 'electromagnetic', 'EM field', 'photon',
            'light emission', 'field topology', 'Hapbee', 'ulRFE'
        ],
        'GILE_framework': [
            'GILE', 'goodness', 'intuition', 'love', 'environment',
            'four dimensions', 'divine framework'
        ],
        'clinical_applications': [
            'medication', 'prozac', 'sertraline', 'treatment',
            'therapy', 'clinical', 'patient', 'LCC protocol'
        ],
        'markov_FEP': [
            'markov blanket', 'free energy principle', 'FEP', 'friston',
            'active inference', 'predictive processing'
        ],
        'QRI_integration': [
            'QRI', 'boundary problem', 'symmetry theory', 'valence',
            'Gómez-Emilsson', 'andrés', 'consciousness topology'
        ]
    }
    
    def process_conversations(self, conversations_data: List[Dict]) -> Dict:
        """
        Process ChatGPT conversations directly from parsed JSON.
        
        Args:
            conversations_data: List of conversation dictionaries from conversations.json
            
        Returns:
            Dict with categorization results, indexes, and statistics
        """
        results = {
            'total_conversations': len(conversations_data),
            'by_concept': defaultdict(set),  # Use sets to avoid duplicates
            'by_date': defaultdict(set),
            'date_range': {'start': None, 'end': None},
            'master_index': '',
            'timeline': ''
        }
        
        # Track detailed conversation info for generating outputs
        conversation_details = []
        
        for conv in conversations_data:
            # Extract metadata
            conv_id = conv.get('id', 'unknown')
            title = conv.get('title', 'Untitled')
            create_time = conv.get('create_time')
            messages = conv.get('mapping', {})
            
            # Get date
            if create_time:
                dt = datetime.fromtimestamp(create_time)
                date_key = dt.strftime('%Y-%m')
                
                # Track date range
                if not results['date_range']['start'] or dt < datetime.fromisoformat(results['date_range']['start'] or '9999-12-31'):
                    results['date_range']['start'] = dt.isoformat()
                if not results['date_range']['end'] or dt > datetime.fromisoformat(results['date_range']['end'] or '0001-01-01'):
                    results['date_range']['end'] = dt.isoformat()
            else:
                date_key = 'unknown'
                dt = None
            
            # Extract full text for categorization
            full_text = self._extract_conversation_text(messages)
            
            # Categorize by concept
            concepts = self._categorize_conversation(title, full_text)
            
            # Store conversation details
            conv_detail = {
                'id': conv_id,
                'title': title,
                'date': dt.isoformat() if dt else None,
                'date_key': date_key,
                'create_time': create_time,
                'concepts': concepts,
                'message_count': len(messages),
                'preview': full_text[:500] if full_text else ""
            }
            conversation_details.append(conv_detail)
            
            # Add to concept categories
            for concept in concepts:
                results['by_concept'][concept].add(conv_id)
            
            # Add to date categories
            results['by_date'][date_key].add(conv_id)
        
        # Convert sets to lists for JSON serialization
        results['by_concept'] = {k: list(v) for k, v in results['by_concept'].items()}
        results['by_date'] = {k: list(v) for k, v in results['by_date'].items()}
        
        # Generate master index and timeline
        results['master_index'] = self._generate_master_index(
            results, conversation_details
        )
        results['timeline'] = self._generate_timeline(
            results['by_date'], conversation_details
        )
        
        return results
    
    def _extract_conversation_text(self, messages: Dict) -> str:
        """Extract all text from conversation messages."""
        text_parts = []
        
        for msg_id, msg_data in messages.items():
            message = msg_data.get('message', {})
            if message:
                content = message.get('content', {})
                if content:
                    parts = content.get('parts', [])
                    for part in parts:
                        if isinstance(part, str):
                            text_parts.append(part)
        
        return "\n".join(text_parts)
    
    def _categorize_conversation(self, title: str, text: str) -> List[str]:
        """Categorize conversation based on keywords in title and text."""
        concepts = []
        
        # Combine title and text for matching (convert to lowercase)
        full_content = (title + " " + text).lower()
        
        # Check each concept's keywords
        for concept, keywords in self.CONCEPT_KEYWORDS.items():
            for keyword in keywords:
                if keyword.lower() in full_content:
                    concepts.append(concept)
                    break  # Found match for this concept, move to next
        
        # If no concepts matched, categorize as 'other'
        if not concepts:
            concepts.append('other')
        
        return concepts
    
    def _generate_master_index(self, results: Dict, conversation_details: List[Dict]) -> str:
        """Generate master index markdown."""
        
        index_md = "# ChatGPT History - Master Index\n\n"
        index_md += f"**Processing Date:** {datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n"
        index_md += f"**Total Conversations:** {results['total_conversations']}\n\n"
        
        if results['date_range']['start']:
            index_md += f"**Date Range:** {results['date_range']['start'][:10]} to {results['date_range']['end'][:10]}\n\n"
        
        index_md += "---\n\n## Categorization by Concept\n\n"
        
        # Sort concepts by conversation count
        sorted_concepts = sorted(
            results['by_concept'].items(),
            key=lambda x: len(x[1]),
            reverse=True
        )
        
        for concept, conv_ids in sorted_concepts:
            index_md += f"### {concept.replace('_', ' ').title()}\n"
            index_md += f"- **Conversations:** {len(conv_ids)}\n\n"
            
            # Add sample conversation titles
            sample_convs = [c for c in conversation_details if c['id'] in conv_ids[:5]]
            if sample_convs:
                index_md += "**Key Conversations:**\n"
                for conv in sample_convs[:5]:
                    index_md += f"- {conv['title']}\n"
                index_md += "\n"
        
        index_md += "---\n\n## Timeline by Date\n\n"
        
        sorted_dates = sorted(results['by_date'].keys(), reverse=True)
        for date in sorted_dates:
            count = len(results['by_date'][date])
            index_md += f"- **{date}:** {count} conversations\n"
        
        return index_md
    
    def _generate_timeline(self, by_date: Dict, conversation_details: List[Dict]) -> str:
        """Generate chronological timeline of insights."""
        
        timeline_md = "# Timeline of Insights\n\n"
        timeline_md += "## Chronological Development of TI-UOP Framework\n\n"
        
        # Sort dates chronologically
        sorted_dates = sorted(by_date.keys())
        
        for date in sorted_dates:
            conv_ids = by_date[date]
            conversations = [c for c in conversation_details if c['id'] in conv_ids]
            
            timeline_md += f"## {date}\n\n"
            timeline_md += f"**{len(conversations)} conversations**\n\n"
            
            # Group by concept
            concept_groups = defaultdict(list)
            for conv in conversations:
                for concept in conv.get('concepts', []):
                    concept_groups[concept].append(conv['title'])
            
            for concept, titles in sorted(concept_groups.items()):
                timeline_md += f"### {concept.replace('_', ' ').title()}\n"
                for title in titles:
                    timeline_md += f"- {title}\n"
                timeline_md += "\n"
            
            timeline_md += "---\n\n"
        
        return timeline_md
