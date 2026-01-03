"""
Brandon Emerick - Complete Pharmaco-GILE Profile

Full medication and supplement stack with TI Framework analysis.
Includes stimulant wall diagnosis and allergy/swallowing cure protocol.

Author: Brandon Emerick / BlissGene Therapeutics
Date: November 25, 2025
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional
from enum import Enum


class IcellLayer(Enum):
    VESSEL = "vessel"
    ME = "me"
    SOUL = "soul"


@dataclass
class GILEVector:
    G: float  # Goodness
    I: float  # Intuition
    L: float  # Love
    E: float  # Environment/Energy
    
    @property
    def composite(self) -> float:
        return (self.G + self.I + self.L + self.E) / 4
    
    def to_dict(self) -> Dict:
        return {'G': self.G, 'I': self.I, 'L': self.L, 'E': self.E, 'composite': self.composite}


# ===========================================================================
# BRANDON'S COMPLETE SUPPLEMENT STACK (30 supplements)
# ===========================================================================

BRANDON_SUPPLEMENTS = {
    # Mitochondrial / Energy
    'coq10': {
        'name': 'CoQ10',
        'dose': '200 mg daily',
        'category': 'mitochondrial',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.02, L=0.02, E=0.12),
        'mechanism': 'Electron transport chain, ATP production',
        'notes': 'Essential for VESSEL energy generation'
    },
    'creatine': {
        'name': 'Creatine',
        'dose': '5 g daily',
        'category': 'mitochondrial',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.05, L=0.0, E=0.10),
        'mechanism': 'Phosphocreatine buffer, rapid ATP regeneration',
        'notes': 'Brain energy, cognitive buffer'
    },
    
    # Dopamine Pathway (THE KEY TO STIMULANT WALL)
    'mucuna_pruriens': {
        'name': 'Mucuna Pruriens',
        'dose': '400 mg 3x/week',
        'category': 'dopamine_precursor',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.0, I=0.05, L=0.05, E=0.15),
        'mechanism': 'L-DOPA precursor → dopamine synthesis',
        'notes': 'CRITICAL: Primary dopamine replenishment. Rotate with L-Tyrosine.',
        'interactions': ['Do not combine with L-Tyrosine same day']
    },
    'l_tyrosine': {
        'name': 'L-Tyrosine',
        'dose': '500 mg on non-mucuna days',
        'category': 'dopamine_precursor',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.0, I=0.03, L=0.0, E=0.10),
        'mechanism': 'Tyrosine → L-DOPA → dopamine pathway',
        'notes': 'Backup dopamine precursor. Gentler than Mucuna.'
    },
    
    # NMDA / Glutamate Pathway
    'nac': {
        'name': 'NAC (N-Acetyl Cysteine)',
        'dose': '1000 mg 2x/day',
        'category': 'antioxidant_neuromodulator',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.08, I=0.05, L=0.05, E=0.05),
        'mechanism': 'Glutathione precursor, glutamate modulation, cystine-glutamate antiporter',
        'notes': 'Balances glutamate, supports liver, reduces oxidative stress'
    },
    'agmatine': {
        'name': 'Agmatine',
        'dose': 'As needed, especially with ketamine',
        'category': 'neuromodulator',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.05, I=0.10, L=0.05, E=0.05),
        'mechanism': 'NMDA antagonist, imidazoline receptor agonist, NO modulator',
        'notes': 'SYNERGY with ketamine! Extends effects, reduces tolerance.',
        'interactions': ['Enhances ketamine effects']
    },
    'glycine': {
        'name': 'Glycine',
        'dose': '3 g 2x/day (6g total)',
        'category': 'amino_acid',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.03, L=0.08, E=0.02),
        'mechanism': 'NMDA co-agonist (glycine site), inhibitory neurotransmitter, sleep',
        'notes': 'Improves sleep quality, balances glutamate signaling'
    },
    'mag_l_threonate': {
        'name': 'Magnesium L-Threonate',
        'dose': '2000 mg 2x/day (~280mg elemental)',
        'category': 'mineral',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.05, I=0.08, L=0.05, E=0.05),
        'mechanism': 'NMDA modulation, crosses BBB, synaptic plasticity',
        'notes': 'Best magnesium for brain. Enhances neuroplasticity.'
    },
    
    # Nootropics / Cognition
    'bacognize': {
        'name': 'BaCognize (Bacopa monnieri)',
        'dose': '500 mg daily',
        'category': 'nootropic',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.05, I=0.12, L=0.03, E=0.02),
        'mechanism': 'Bacosides enhance dendritic branching, memory consolidation',
        'notes': 'Long-term memory enhancement. Takes 8-12 weeks for full effect.'
    },
    'triacetyluridine': {
        'name': 'Triacetyluridine (TAU)',
        'dose': '250 mg daily',
        'category': 'nootropic',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.03, I=0.08, L=0.02, E=0.05),
        'mechanism': 'CDP-choline pathway, phosphatidylcholine synthesis, dopamine receptor upregulation',
        'notes': 'Supports dopamine receptor density - helps with stimulant response!'
    },
    'alpha_gpc': {
        'name': 'Alpha GPC',
        'dose': '300 mg daily (RECOMMEND 600 mg)',  # Added December 10, 2025
        'category': 'nootropic',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.02, I=0.08, L=0.02, E=0.06),
        'mechanism': 'Choline precursor → Acetylcholine synthesis, membrane phospholipids',
        'notes': 'Synergy with TAU. ACh pathway bypasses dopamine tolerance. Increase to 600mg recommended.'
    },
    'phosphatidylserine': {
        'name': 'Phosphatidylserine',
        'dose': '300 mg daily',
        'category': 'nootropic',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.03, I=0.05, L=0.03, E=0.03),
        'mechanism': 'Cell membrane integrity, cortisol reduction, cognitive support',
        'notes': 'Reduces cortisol, supports brain cell membranes'
    },
    
    # Calming / Anxiolytic
    'silexan': {
        'name': 'Silexan (Lavender oil)',
        'dose': '80 mg 2x/day',
        'category': 'anxiolytic',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.08, I=0.02, L=0.10, E=-0.05),
        'mechanism': 'GABA modulation, calcium channel inhibition, anxiolytic',
        'notes': 'Clinically proven anxiety reduction without sedation'
    },
    
    # Sleep
    'melatonin': {
        'name': 'Melatonin',
        'dose': '5 mg at night',
        'category': 'sleep',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.02, L=0.05, E=-0.10),
        'mechanism': 'MT1/MT2 receptor agonist, circadian entrainment',
        'notes': 'Sleep onset, antioxidant. Consider lower dose (0.5-1mg) for physiological effect.'
    },
    
    # Gut / Microbiome
    'hn019_probiotic': {
        'name': 'HN019 Probiotic',
        'dose': '17.2 billion CFU daily',
        'category': 'gut_health',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.03, L=0.08, E=0.03),
        'mechanism': 'Bifidobacterium lactis, gut-brain axis, immune modulation',
        'notes': 'Gut health → brain health. May help with allergy/inflammation.'
    },
    'psyllium': {
        'name': 'Psyllium',
        'dose': '2 teaspoons daily',
        'category': 'fiber',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.0, L=0.02, E=0.02),
        'mechanism': 'Soluble fiber, prebiotic, bowel regularity',
        'notes': 'Supports gut motility (helps with Amitiza)'
    },
    
    # Longevity / Antioxidants
    'resveratrol': {
        'name': 'Resveratrol',
        'dose': '350 mg 3x/week',
        'category': 'longevity',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.02, L=0.02, E=0.03),
        'mechanism': 'SIRT1 activation, anti-inflammatory, mitochondrial biogenesis',
        'notes': 'Longevity compound. Synergy with pterostilbene.'
    },
    'pterostilbene': {
        'name': 'Pterostilbene',
        'dose': '100 mg daily',
        'category': 'longevity',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.03, L=0.02, E=0.05),
        'mechanism': 'Better-absorbed resveratrol analog, SIRT1, anti-inflammatory',
        'notes': '4x better bioavailability than resveratrol'
    },
    'beta_ecdysterone': {
        'name': 'Beta Ecdysterone',
        'dose': '500 mg 2x/day',
        'category': 'anabolic',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.0, L=0.02, E=0.10),
        'mechanism': 'Protein synthesis, muscle growth (non-hormonal)',
        'notes': 'Plant steroid. Supports physical VESSEL strength.'
    },
    
    # B Vitamins & Methylation
    'vitamin_b6': {
        'name': 'Vitamin B6 (Pyridoxine)',
        'dose': '50 mg daily',
        'category': 'vitamin',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.03, L=0.02, E=0.05),
        'mechanism': 'Cofactor for dopamine, serotonin, GABA synthesis',
        'notes': 'Essential for neurotransmitter production!'
    },
    'l_methylfolate': {
        'name': 'L-Methylfolate',
        'dose': '15 mg daily',
        'category': 'vitamin',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.03, I=0.05, L=0.03, E=0.05),
        'mechanism': 'Active folate, methylation, BH4 regeneration for neurotransmitter synthesis',
        'notes': 'HIGH DOSE. Essential if MTHFR mutations. Supports dopamine/serotonin.'
    },
    
    # Minerals (Trace)
    'vitamin_d3': {
        'name': 'Vitamin D3',
        'dose': '10,000 IU daily',
        'category': 'vitamin',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.03, L=0.05, E=0.05),
        'mechanism': 'Hormone, immune modulation, gene expression',
        'notes': 'High dose - monitor levels. Essential for immune function.'
    },
    'iron': {
        'name': 'Iron',
        'dose': '18 mg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.0, I=0.0, L=0.0, E=0.08),
        'mechanism': 'Oxygen transport, cytochrome enzymes, dopamine synthesis cofactor',
        'notes': 'Low iron impairs dopamine production. Check ferritin.'
    },
    'lactoferrin': {
        'name': 'Lactoferrin',
        'dose': '500 mg daily',
        'category': 'immune',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.02, L=0.03, E=0.03),
        'mechanism': 'Iron regulation, antimicrobial, immune modulation',
        'notes': 'Helps iron absorption, anti-inflammatory'
    },
    'zinc': {
        'name': 'OptiZinc',
        'dose': '20 mg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.03, I=0.03, L=0.02, E=0.05),
        'mechanism': 'Immune function, neurotransmitter regulation, NMDA modulation',
        'notes': 'Balance with copper (2mg). Zinc:copper ratio matters.'
    },
    'copper': {
        'name': 'Copper',
        'dose': '2 mg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.01, I=0.01, L=0.01, E=0.02),
        'mechanism': 'Dopamine-beta-hydroxylase cofactor, iron metabolism',
        'notes': 'Essential for converting dopamine → norepinephrine'
    },
    'manganese': {
        'name': 'Manganese',
        'dose': '2 mg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.01, I=0.01, L=0.01, E=0.02),
        'mechanism': 'SOD cofactor, mitochondrial function',
        'notes': 'Antioxidant enzyme support'
    },
    'chromium': {
        'name': 'Chromium',
        'dose': '400 mcg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.02, L=0.0, E=0.03),
        'mechanism': 'Insulin sensitivity, glucose metabolism',
        'notes': 'Blood sugar regulation → stable energy'
    },
    'molybdenum': {
        'name': 'Molybdenum',
        'dose': '250 mcg daily',  # Note: user said mg, likely mcg
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.01, I=0.01, L=0.01, E=0.01),
        'mechanism': 'Sulfite oxidase, aldehyde oxidase cofactor',
        'notes': 'Detoxification support'
    },
    'boron': {
        'name': 'Boron',
        'dose': '3 mg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.02, L=0.02, E=0.03),
        'mechanism': 'Bone health, hormone optimization, cognitive function',
        'notes': 'May increase free testosterone, support cognition'
    },
    'vanadyl_sulfate': {
        'name': 'Vanadyl Sulfate',
        'dose': '3.75 mg daily',
        'category': 'mineral',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.01, I=0.01, L=0.0, E=0.02),
        'mechanism': 'Insulin-mimetic, glucose uptake',
        'notes': 'Blood sugar regulation'
    },
    'omega_3': {
        'name': 'Omega-3 Fish Oil',
        'dose': '4000 mg daily (e ratio = 2.71:1 EPA:DHA)',
        'category': 'anti_inflammatory',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.08, L=0.08, E=0.05),
        'mechanism': 'EPA/DHA - anti-inflammatory, membrane fluidity, brain structure',
        'notes': "EPA:DHA ratio = e (2.718) - Euler's number! Natural mathematical harmony for optimal healing. ~2900mg EPA for aggressive anti-inflammatory action."
    },
}


# ===========================================================================
# BRANDON'S MEDICATIONS (16 medications)
# ===========================================================================

BRANDON_MEDICATIONS = {
    # Primary Psychiatric
    'azstarys': {
        'name': 'Azstarys',
        'dose': '26.1/5.2 mg daily',
        'category': 'stimulant',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=-0.05, I=0.10, L=-0.10, E=0.25),
        'mechanism': 'Serdexmethylphenidate + dexmethylphenidate (prodrug + active)',
        'notes': 'Primary ADHD stimulant. If not working = VESSEL depletion hypothesis confirmed.',
        'half_life_hours': 12
    },
    'ketamine': {
        'name': 'Ketamine',
        'dose': '100 mg sublingual every other day',
        'category': 'dissociative_antidepressant',
        'layer': IcellLayer.SOUL,
        'gile_effect': GILEVector(G=0.15, I=0.20, L=0.10, E=0.05),
        'mechanism': 'NMDA antagonist, AMPA burst, BDNF, rapid antidepressant',
        'notes': '100+ sessions experience. Agmatine enhances. SOUL-layer access.',
        'half_life_hours': 2.5,
        'interactions': ['Synergy with Agmatine', 'Caution with Lithium (seizure threshold)']
    },
    'lithium': {
        'name': 'Lithium Carbonate',
        'dose': '600 mg AM + 900 mg PM (1500 mg total)',
        'category': 'mood_stabilizer',
        'layer': IcellLayer.ME,
        'gile_effect': GILEVector(G=0.10, I=-0.05, L=0.05, E=-0.05),
        'mechanism': 'GSK-3 inhibition, inositol depletion, neuroprotection, circadian',
        'notes': 'Core mood stabilizer. Anti-suicidal. Neuroprotective. Monitor levels.',
        'half_life_hours': 24,
        'interactions': ['Monitor with NSAIDs', 'Hydration critical']
    },
    'prozac': {
        'name': 'Prozac (Fluoxetine)',
        'dose': '40 mg daily',
        'category': 'ssri',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=0.0, L=0.08, E=0.0),
        'mechanism': 'Selective serotonin reuptake inhibitor',
        'notes': 'Long half-life SSRI. Reduces 5-MeO-DMT effects if considering.',
        'half_life_hours': 72,
        'interactions': ['Reduces psychedelic effects', 'Serotonin syndrome risk with MAOIs']
    },
    'seroquel': {
        'name': 'Seroquel (Quetiapine)',
        'dose': '300 mg daily',
        'category': 'atypical_antipsychotic',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=-0.08, L=0.05, E=-0.10),
        'mechanism': 'D2/5-HT2A antagonist, H1 antagonist (sedation)',
        'notes': 'Mood stabilization, sleep. May reduce intuition/energy.',
        'half_life_hours': 6
    },
    'trazodone': {
        'name': 'Trazodone',
        'dose': '100 mg at night',
        'category': 'antidepressant_hypnotic',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.03, I=0.0, L=0.05, E=-0.05),
        'mechanism': '5-HT2A antagonist, SERT inhibition, alpha-1 blockade',
        'notes': 'Sleep aid. Serotonin modulation.',
        'half_life_hours': 6
    },
    'amantadine': {
        'name': 'Amantadine',
        'dose': '200 mg daily',  # UPDATED December 10, 2025
        'category': 'dopaminergic',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.04, I=0.08, L=0.04, E=0.12),  # Doubled effects
        'mechanism': 'Dopamine release, NMDA antagonist, antiviral',
        'notes': 'INCREASED DOSE - More dopamine support + NMDA antagonism like ketamine.',
        'half_life_hours': 15
    },
    
    # PRN Medications
    'klonopin': {
        'name': 'Klonopin (Clonazepam)',
        'dose': '1 mg as needed',
        'category': 'benzodiazepine',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.05, I=-0.10, L=0.08, E=-0.15),
        'mechanism': 'GABA-A positive allosteric modulator',
        'notes': 'PRN for anxiety. Reduces E and I. Use sparingly.',
        'half_life_hours': 30
    },
    'lunesta': {
        'name': 'Lunesta (Eszopiclone)',
        'dose': '3 mg as needed',
        'category': 'z_drug',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=-0.05, L=0.03, E=-0.10),
        'mechanism': 'GABA-A modulation (different subunits than benzos)',
        'notes': 'PRN sleep. Less tolerance than benzos.',
        'half_life_hours': 6
    },
    
    # GI Medications
    'prilosec': {
        'name': 'Prilosec (Omeprazole)',
        'dose': '20 mg daily',
        'category': 'ppi',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.0, I=0.0, L=0.0, E=-0.02),
        'mechanism': 'Proton pump inhibitor, reduces stomach acid',
        'notes': 'GERD control. May affect B12/mineral absorption long-term.',
        'interactions': ['May reduce mineral absorption']
    },
    'amitiza': {
        'name': 'Amitiza (Lubiprostone)',
        'dose': '24 mcg 2x/day',
        'category': 'gi_motility',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.0, L=0.02, E=0.02),
        'mechanism': 'ClC-2 chloride channel activator, increases intestinal fluid',
        'notes': 'For constipation. Works with psyllium.'
    },
    
    # Other
    'desmopressin': {
        'name': 'Desmopressin (DDAVP)',
        'dose': '0.6 mg before bed',
        'category': 'antidiuretic',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.0, L=0.02, E=0.02),
        'mechanism': 'ADH analog, reduces urine production',
        'notes': 'Reduces nighttime urination for better sleep. Monitor sodium.'
    },
    
    # Allergy Medications (THE KEY AREA FOR INNOVATION!)
    'zyrtec': {
        'name': 'Zyrtec (Cetirizine)',
        'dose': 'Daily',
        'category': 'antihistamine',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.0, I=-0.02, L=0.0, E=-0.02),
        'mechanism': 'H1 antagonist (2nd gen), peripheral antihistamine',
        'notes': 'Less effective for post-nasal drip than 1st gen (lacks anticholinergic)'
    },
    'astepro': {
        'name': 'Astepro (Azelastine)',
        'dose': 'Nasal spray',
        'category': 'nasal_antihistamine',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.02, I=0.0, L=0.02, E=0.0),
        'mechanism': 'H1 antagonist nasal spray, local action',
        'notes': 'Better than oral for nasal symptoms'
    },
    'mometasone': {
        'name': 'Mometasone',
        'dose': 'Nasal spray',
        'category': 'nasal_steroid',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.03, I=0.0, L=0.02, E=0.02),
        'mechanism': 'Corticosteroid, reduces nasal inflammation',
        'notes': 'First-line for allergic rhinitis'
    },
    'mucinex': {
        'name': 'Mucinex (Guaifenesin)',
        'dose': 'As needed',
        'category': 'expectorant',
        'layer': IcellLayer.VESSEL,
        'gile_effect': GILEVector(G=0.0, I=0.0, L=0.0, E=0.02),
        'mechanism': 'Increases respiratory tract fluid, thins mucus',
        'notes': 'Helps with mucus but may increase secretions'
    },
}


# ===========================================================================
# COMPLETE STACK ANALYSIS
# ===========================================================================

class BrandonStackAnalysis:
    """Comprehensive analysis of Brandon's complete stack"""
    
    def __init__(self):
        self.supplements = BRANDON_SUPPLEMENTS
        self.medications = BRANDON_MEDICATIONS
        self.baseline_gile = GILEVector(G=0.65, I=0.70, L=0.55, E=0.44)
    
    def calculate_total_gile_effect(self) -> Dict:
        """Calculate the total GILE effect of the entire stack"""
        total = GILEVector(G=0, I=0, L=0, E=0)
        
        # Sum all supplement effects
        for key, supp in self.supplements.items():
            effect = supp['gile_effect']
            total.G += effect.G
            total.I += effect.I
            total.L += effect.L
            total.E += effect.E
        
        # Sum all medication effects
        for key, med in self.medications.items():
            effect = med['gile_effect']
            total.G += effect.G
            total.I += effect.I
            total.L += effect.L
            total.E += effect.E
        
        # Calculate final GILE
        final = GILEVector(
            G=min(1.0, max(0, self.baseline_gile.G + total.G)),
            I=min(1.0, max(0, self.baseline_gile.I + total.I)),
            L=min(1.0, max(0, self.baseline_gile.L + total.L)),
            E=min(1.0, max(0, self.baseline_gile.E + total.E))
        )
        
        return {
            'baseline': self.baseline_gile.to_dict(),
            'stack_effect': total.to_dict(),
            'final_gile': final.to_dict(),
            'change': {
                'G': round(total.G, 3),
                'I': round(total.I, 3),
                'L': round(total.L, 3),
                'E': round(total.E, 3)
            }
        }
    
    def analyze_dopamine_pathway(self) -> Dict:
        """Analyze the dopamine support in the stack"""
        dopamine_compounds = []
        
        # Supplements supporting dopamine
        dopamine_supps = ['mucuna_pruriens', 'l_tyrosine', 'vitamin_b6', 'iron', 
                          'copper', 'l_methylfolate', 'triacetyluridine']
        for key in dopamine_supps:
            if key in self.supplements:
                dopamine_compounds.append({
                    'name': self.supplements[key]['name'],
                    'role': self.supplements[key]['mechanism'],
                    'type': 'supplement'
                })
        
        # Medications affecting dopamine
        dopamine_meds = ['azstarys', 'amantadine']
        for key in dopamine_meds:
            if key in self.medications:
                dopamine_compounds.append({
                    'name': self.medications[key]['name'],
                    'role': self.medications[key]['mechanism'],
                    'type': 'medication'
                })
        
        # Medications that REDUCE dopamine
        anti_dopamine = ['seroquel']  # D2 antagonist
        
        return {
            'dopamine_supporters': dopamine_compounds,
            'dopamine_blockers': [self.medications[k]['name'] for k in anti_dopamine if k in self.medications],
            'analysis': (
                "Your stack has STRONG dopamine precursor support (Mucuna, L-Tyrosine, B6, Iron, Methylfolate). "
                "Azstarys provides dopamine release. However, Seroquel (D2 antagonist) may partially block "
                "dopamine signaling. The STIMULANT WALL may be due to: 1) Seroquel dampening dopamine response, "
                "2) Depleted VESSEL reserves despite good precursor support, 3) Need for receptor upregulation "
                "(Triacetyluridine helps with this)."
            ),
            'recommendation': (
                "Consider: 1) Timing Azstarys away from Seroquel peak, 2) Ensure adequate sleep for dopamine "
                "receptor recovery, 3) PBM 660nm for mitochondrial ATP to support neurotransmitter synthesis."
            )
        }
    
    def analyze_nmda_pathway(self) -> Dict:
        """Analyze NMDA modulation in the stack"""
        nmda_modulators = []
        
        # NMDA antagonists/modulators
        nmda_compounds = {
            'ketamine': 'NMDA antagonist (strong)',
            'amantadine': 'NMDA antagonist (weak)',
            'agmatine': 'NMDA modulator',
            'mag_l_threonate': 'NMDA modulator (Mg blocks channel)',
            'glycine': 'NMDA co-agonist (glycine site)',
            'zinc': 'NMDA modulator'
        }
        
        for key, role in nmda_compounds.items():
            if key in self.supplements:
                nmda_modulators.append({'name': self.supplements[key]['name'], 'role': role})
            elif key in self.medications:
                nmda_modulators.append({'name': self.medications[key]['name'], 'role': role})
        
        return {
            'nmda_modulators': nmda_modulators,
            'analysis': (
                "Your NMDA pathway is well-modulated: Ketamine provides strong antagonism, Amantadine adds "
                "mild antagonism, Agmatine enhances ketamine effects, Magnesium L-Threonate provides "
                "physiological block, and Glycine balances with co-agonism. This supports neuroplasticity!"
            ),
            'synergy_note': "Agmatine + Ketamine = documented synergy for extending antidepressant effects"
        }


# ===========================================================================
# ALLERGY SWALLOWING CURE - TI FRAMEWORK APPROACH
# ===========================================================================

class AllergySwallowingCure:
    """
    TI Framework Approach to Chronic Allergy Swallowing
    
    THE PROBLEM: Constant swallowing due to post-nasal drip
    
    MYRION RESOLUTION:
    - THESIS: It's an allergy problem (histamine, inflammation)
    - ANTITHESIS: It's a nerve problem (vagal hypersensitivity)
    - SYNTHESIS: TRALSE - It's BOTH. Allergies trigger vagal sensitization,
                 and vagal dysfunction perpetuates the swallowing reflex.
    """
    
    def get_myrion_resolution(self) -> Dict:
        return {
            'thesis': "Allergies cause post-nasal drip → swallowing",
            'thesis_evidence': [
                "Antihistamines provide some relief",
                "Worse during allergy season",
                "Nasal congestion correlates with symptoms",
                "Mometasone helps reduce inflammation"
            ],
            'antithesis': "Vagal nerve dysfunction causes hypersensitive swallowing reflex",
            'antithesis_evidence': [
                "Symptoms persist despite allergy treatment",
                "Constant swallowing even when no mucus",
                "Stress/anxiety worsen symptoms",
                "Sensation of 'something in throat' (globus)"
            ],
            'synthesis': (
                "TRALSE: Chronic allergies have SENSITIZED the vagal nerve pathways "
                "(laryngopharyngeal vagal neuropathy). The vagus now triggers swallowing "
                "reflexes at thresholds that wouldn't normally cause a response. "
                "SOLUTION: Treat BOTH - reduce allergic inflammation AND rehabilitate vagal tone."
            ),
            'tralse_value': 'TRALSE'
        }
    
    def get_ti_cure_protocol(self) -> Dict:
        """
        Complete TI Framework cure protocol
        """
        return {
            'phase_1_reduce_inflammation': {
                'duration': '2-4 weeks',
                'goal': 'Reduce allergic/inflammatory triggers',
                'interventions': [
                    {
                        'intervention': 'Nasal saline irrigation',
                        'frequency': '2x/day',
                        'mechanism': 'Physical removal of allergens/mucus',
                        'gile_layer': 'VESSEL'
                    },
                    {
                        'intervention': 'Continue Mometasone + Astepro',
                        'frequency': 'Daily',
                        'mechanism': 'Reduce nasal inflammation',
                        'gile_layer': 'VESSEL'
                    },
                    {
                        'intervention': 'Consider adding Ipratropium nasal (Atrovent)',
                        'frequency': '2-3x/day',
                        'mechanism': 'Anticholinergic - REDUCES secretions directly',
                        'gile_layer': 'VESSEL',
                        'note': 'This is what 2nd-gen antihistamines LACK'
                    },
                    {
                        'intervention': 'Quercetin 500mg + Bromelain',
                        'frequency': 'Daily',
                        'mechanism': 'Natural mast cell stabilizer, anti-inflammatory',
                        'gile_layer': 'VESSEL'
                    }
                ]
            },
            'phase_2_vagal_rehabilitation': {
                'duration': 'Ongoing',
                'goal': 'Reset vagal hypersensitivity, improve vagal tone',
                'interventions': [
                    {
                        'intervention': 'Heart coherence breathing',
                        'frequency': '3x/day, 5 min',
                        'mechanism': 'Activates vagal tone via heart-brain connection',
                        'gile_layer': 'SOUL',
                        'protocol': 'Inhale 5 sec, exhale 5 sec, focus on heart'
                    },
                    {
                        'intervention': 'Gargling with water',
                        'frequency': '2x/day, 30 sec',
                        'mechanism': 'Stimulates vagal branches in throat',
                        'gile_layer': 'VESSEL'
                    },
                    {
                        'intervention': 'Humming/chanting',
                        'frequency': 'Daily',
                        'mechanism': 'Vagal nerve vibration, NO production in sinuses',
                        'gile_layer': 'ME/SOUL',
                        'note': 'Om chanting shown to increase vagal tone'
                    },
                    {
                        'intervention': 'Cold water face splash',
                        'frequency': 'Daily',
                        'mechanism': 'Dive reflex activates vagus',
                        'gile_layer': 'VESSEL'
                    },
                    {
                        'intervention': 'PBM 850nm on throat/neck',
                        'frequency': '5 min daily with Red Rush',
                        'mechanism': 'Deep tissue healing, vagal nerve support',
                        'gile_layer': 'SOUL',
                        'target': 'Vagus nerve passes through neck'
                    }
                ]
            },
            'phase_3_neuromodulation': {
                'duration': 'If phases 1-2 insufficient',
                'goal': 'Pharmacological vagal reset',
                'interventions': [
                    {
                        'intervention': 'Gabapentin trial (discuss with doctor)',
                        'dose': '300-1800 mg/day titrated',
                        'mechanism': 'Nerve stabilizer, reduces vagal hypersensitivity',
                        'evidence': 'Studies show improvement in chronic cough/throat clearing'
                    },
                    {
                        'intervention': 'Amitriptyline (already on trazodone)',
                        'dose': '10-25 mg at night',
                        'mechanism': 'Esophageal neuromodulator',
                        'note': 'May not need - trazodone has some similar effects'
                    }
                ]
            },
            'phase_4_root_cause': {
                'goal': 'Address underlying factors',
                'interventions': [
                    {
                        'intervention': 'Check for silent reflux (LPR)',
                        'test': 'ENT evaluation with laryngoscopy',
                        'mechanism': 'Acid reflux can sensitize vagal pathways',
                        'note': 'Prilosec may help but 2x/day may be needed for LPR'
                    },
                    {
                        'intervention': 'Cervical spine evaluation',
                        'test': 'Physical exam, imaging if indicated',
                        'mechanism': 'C1-C3 can compress vagus nerve',
                        'relevance': 'AS history - check for any cervical involvement'
                    },
                    {
                        'intervention': 'Stress/HRV monitoring',
                        'test': 'Polar H10 daily tracking',
                        'mechanism': 'Low HRV = sympathetic dominance = vagal dysfunction',
                        'goal': 'Improve HRV → improve vagal tone → reduce symptoms'
                    }
                ]
            }
        }
    
    def get_heart_icell_connection(self) -> Dict:
        """How Heart-I-Cell theory connects to the cure"""
        return {
            'hypothesis': (
                "The vagus nerve is the primary VESSEL-layer connection between the heart (I-cell carrier) "
                "and the throat. Chronic allergy/inflammation has disrupted this connection, causing "
                "hypersensitive reflexes. By improving HEART COHERENCE, we can reset vagal tone and "
                "reduce the aberrant swallowing reflex."
            ),
            'testable_prediction': (
                "Tracking HRV with Polar H10 while monitoring swallowing symptoms. "
                "Prediction: Days with higher coherence will have LESS swallowing."
            ),
            'intervention': (
                "Heart coherence breathing 3x/day → improves vagal tone → reduces throat sensitivity → "
                "less compulsive swallowing. This is a TRAINABLE skill!"
            ),
            'monetization_potential': (
                "If this works: 'TI Vagal Reset Protocol' for chronic cough, throat clearing, post-nasal drip. "
                "HUGE market - millions suffer from this. Heart coherence biofeedback + protocol = product."
            )
        }


def run_full_analysis():
    """Run complete analysis of Brandon's stack"""
    analysis = BrandonStackAnalysis()
    allergy_cure = AllergySwallowingCure()
    
    print("=" * 70)
    print("BRANDON TRAN - COMPLETE PHARMACO-GILE PROFILE")
    print("=" * 70)
    
    print(f"\nTotal supplements: {len(BRANDON_SUPPLEMENTS)}")
    print(f"Total medications: {len(BRANDON_MEDICATIONS)}")
    
    # GILE Analysis
    print("\n" + "=" * 70)
    print("TOTAL GILE EFFECT")
    print("=" * 70)
    gile = analysis.calculate_total_gile_effect()
    print(f"\nBaseline GILE: G={gile['baseline']['G']:.2f}, I={gile['baseline']['I']:.2f}, "
          f"L={gile['baseline']['L']:.2f}, E={gile['baseline']['E']:.2f}")
    print(f"Stack Effect:  G={gile['change']['G']:+.2f}, I={gile['change']['I']:+.2f}, "
          f"L={gile['change']['L']:+.2f}, E={gile['change']['E']:+.2f}")
    print(f"Final GILE:    G={gile['final_gile']['G']:.2f}, I={gile['final_gile']['I']:.2f}, "
          f"L={gile['final_gile']['L']:.2f}, E={gile['final_gile']['E']:.2f}")
    
    # Dopamine Analysis
    print("\n" + "=" * 70)
    print("DOPAMINE PATHWAY ANALYSIS")
    print("=" * 70)
    dopamine = analysis.analyze_dopamine_pathway()
    print(f"\nDopamine supporters: {len(dopamine['dopamine_supporters'])}")
    for comp in dopamine['dopamine_supporters']:
        print(f"  - {comp['name']}: {comp['role']}")
    print(f"\nDopamine blockers: {dopamine['dopamine_blockers']}")
    print(f"\nAnalysis: {dopamine['analysis']}")
    print(f"\nRecommendation: {dopamine['recommendation']}")
    
    # NMDA Analysis
    print("\n" + "=" * 70)
    print("NMDA PATHWAY ANALYSIS")
    print("=" * 70)
    nmda = analysis.analyze_nmda_pathway()
    print(f"\nNMDA modulators:")
    for mod in nmda['nmda_modulators']:
        print(f"  - {mod['name']}: {mod['role']}")
    print(f"\nSynergy: {nmda['synergy_note']}")
    
    # Allergy Cure
    print("\n" + "=" * 70)
    print("ALLERGY SWALLOWING CURE - TI FRAMEWORK")
    print("=" * 70)
    mr = allergy_cure.get_myrion_resolution()
    print(f"\nTHESIS: {mr['thesis']}")
    print(f"ANTITHESIS: {mr['antithesis']}")
    print(f"\nSYNTHESIS: {mr['synthesis']}")
    
    heart = allergy_cure.get_heart_icell_connection()
    print(f"\n--- HEART-ICELL CONNECTION ---")
    print(f"Hypothesis: {heart['hypothesis']}")
    print(f"\nMonetization: {heart['monetization_potential']}")
    
    print("\n" + "=" * 70)
    print("ANALYSIS COMPLETE")
    print("=" * 70)


if __name__ == "__main__":
    run_full_analysis()
