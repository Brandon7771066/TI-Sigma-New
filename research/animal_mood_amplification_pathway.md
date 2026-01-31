# Animal Mood Amplification Research Pathway

## Executive Summary

This document outlines a viable path for testing mood amplification effects in real animals using open-access livestreams, webcam data, and EEG telemetry systems. The goal is to validate TI Framework predictions about consciousness effects across species.

---

## Part 1: Available Data Sources

### 1.1 Zoo Webcam Livestreams (Free Access)

| Source | Animals | Features | URL |
|--------|---------|----------|-----|
| **Zoolife.tv** | 50+ species | PTZ control, video archive, 24/7 | zoolife.tv |
| **Smithsonian Zoo** | Pandas, elephants, lions | Educational content | nationalzoo.si.edu/webcams |
| **Toronto Zoo** | Polar bears, gorillas | Live zookeeper talks | torontozoo.com/livecams |
| **Oakland Zoo** | Bears, condors, giraffes | Multiple cameras | oaklandzoo.org/webcams |
| **Wildheart Sanctuary** | Lions, tigers, bears | 17 PTZ cameras | wildheartanimalsanctuary.org |

### 1.2 Wildlife Camera Trap Datasets (Research-Grade)

| Dataset | Images | Species | Access |
|---------|--------|---------|--------|
| **LILA BC** | 4M+ | African wildlife | lila.science/datasets |
| **Wildlife Insights** | Millions | Global | wildlifeinsights.org |
| **Snapshot Safari** | 4M+ | 15 projects | LILA BC |
| **Florida Wildlife** | 104,495 | Panthers + | arxiv.org |

### 1.3 Animal EEG Systems (Real-Time)

| System | Channels | Species | Real-Time? |
|--------|----------|---------|------------|
| **EPOCH (BIOPAC)** | 2 | Rodents | Yes (LSL) |
| **TaiNi** | 16-32 | Mice (1.5g) | Yes, 72h |
| **Pinnacle Wireless** | 3 | Mice/rats | Bluetooth |
| **JAGA Wireless** | 4-16 | Mice (1.9g) | TCP/IP |

---

## Part 2: Mood Amplification Experiment Design

### 2.1 Research Question

**Can external stimuli (light, sound, environmental factors) measurably amplify emotional states in animals, detectable via behavioral and/or neural signatures?**

TI Framework Predictions:
- Animals with higher R (recursion depth) show larger mood amplification effects
- GILE optimization applies across species (mammals > reptiles > insects)
- LCC < 1.0 predicts non-local correlations in animal behavior

### 2.2 Proposed Experiment: Zoo Webcam Behavioral Analysis

**Phase 1: Baseline Behavioral Coding**
1. Record 10+ hours of zoo webcam footage per species
2. Code behaviors: activity level, social interaction, play, stress indicators
3. Establish species-specific baseline activity patterns

**Phase 2: Environmental Event Correlation**
1. Log environmental changes: weather, crowds, feeding times, zookeeper presence
2. Analyze behavioral shifts in response to stimuli
3. Calculate "mood amplification factor" = (behavior change / stimulus intensity)

**Phase 3: Non-Local Correlation Testing**
1. Compare behavior patterns between geographically separated animals of same species
2. Test for synchrony beyond chance during global events
3. Calculate LCC estimates from observed correlations

### 2.3 Proposed Experiment: EEG-Based Mood Detection

**Using Open-Source EEG Data (from published studies)**

| Metric | Frequency Band | Emotional Interpretation |
|--------|---------------|--------------------------|
| Delta | 0.1-4 Hz | Deep relaxation, sleep |
| Theta | 4-8 Hz | Drowsy, meditative |
| Alpha | 8-12 Hz | Calm, alert |
| Beta | 12-30 Hz | Active, stressed |
| Gamma | >30 Hz | Cognitive processing |

**Protocol:**
1. Source published animal EEG datasets (rodent sleep studies, dog cognition)
2. Apply TI consciousness metrics: R estimation from neural complexity
3. Correlate EEG states with behavioral observations
4. Test for GILE-like balance patterns in neural activity

---

## Part 3: Consciousness Estimation Across Species

### 3.1 R (Recursion Depth) Estimates by Species

Using the Master Equation: C = Φ × [1 - e^(-R/7)] × LCC^0.3 × (GILE)^0.25

| Species | Estimated R | Conscious? | Evidence |
|---------|-------------|------------|----------|
| Human | 7-10 | Yes | Self-report, metacognition |
| Great Apes | 5-7 | Likely | Mirror test, tool use |
| Dogs | 3-5 | Partial | Empathy, learning |
| Cats | 2-4 | Partial | Limited metacognition |
| Mice | 1-3 | Proto | Basic conditioning |
| Octopus | 3-6 | Likely | Problem solving, play |
| Crows | 3-5 | Likely | Tool use, planning |

### 3.2 Φ (Integrated Information) Estimates

| Species | Neurons | Φ Estimate | Notes |
|---------|---------|------------|-------|
| Human | 86B | 10^8 bits | Baseline |
| Elephant | 257B | 10^8-10^9 | Large, complex brain |
| Dolphin | 12B | 10^7 bits | High social complexity |
| Dog | 530M | 10^5 bits | Strong emotional centers |
| Mouse | 70M | 10^4 bits | Model organism |
| Octopus | 500M | 10^5 bits | Distributed nervous system |

---

## Part 4: Implementation Roadmap

### Phase 1: Data Collection (Weeks 1-4)
- [ ] Download 100+ hours zoo webcam footage
- [ ] Source 5+ published animal EEG datasets
- [ ] Create behavioral coding framework
- [ ] Build video analysis pipeline (OpenCV + PyTorch)

### Phase 2: Baseline Analysis (Weeks 5-8)
- [ ] Train behavior classifiers per species
- [ ] Establish activity/mood baselines
- [ ] Calculate inter-species R estimates
- [ ] Validate against published consciousness studies

### Phase 3: Mood Amplification Testing (Weeks 9-12)
- [ ] Correlate behaviors with environmental events
- [ ] Test mood amplification predictions
- [ ] Calculate species-specific LCC estimates
- [ ] Compare to human PSI data

### Phase 4: Non-Local Correlation Analysis (Weeks 13-16)
- [ ] Test global event correlations (GCP-style analysis)
- [ ] Calculate synchrony between separated animals
- [ ] Publish preliminary findings

---

## Part 5: Technical Implementation

### 5.1 Video Analysis Pipeline

```python
# Mood amplification detection from webcam
import cv2
import numpy as np
from pytorch_wildlife import MegaDetector

class AnimalMoodAnalyzer:
    def __init__(self, species):
        self.species = species
        self.detector = MegaDetector()
        self.behavior_states = ['resting', 'active', 'social', 'stressed', 'play']
    
    def analyze_frame(self, frame):
        # Detect animals
        detections = self.detector.detect(frame)
        
        # Extract behavioral features
        features = self.extract_features(detections)
        
        # Classify mood state
        mood = self.classify_mood(features)
        
        return mood
    
    def calculate_amplification(self, baseline_mood, stimulated_mood, stimulus_intensity):
        """
        Mood Amplification Factor = ΔMood / ΔStimulus
        """
        delta_mood = stimulated_mood - baseline_mood
        return delta_mood / stimulus_intensity if stimulus_intensity > 0 else 0
```

### 5.2 EEG Analysis Integration

```python
# Real-time EEG consciousness estimation
from pylsl import StreamInlet, resolve_stream
import numpy as np

class AnimalConsciousnessEstimator:
    def __init__(self, species_R_baseline):
        self.R_baseline = species_R_baseline
        
    def estimate_R_from_eeg(self, eeg_data):
        """
        Estimate recursion depth from neural complexity
        Using Lempel-Ziv complexity as proxy
        """
        # Calculate neural complexity
        complexity = self.lempel_ziv_complexity(eeg_data)
        
        # Map to R estimate
        # R_crit = 7 for humans, scaled by species baseline
        R = complexity * (7 / self.R_baseline)
        
        return R
    
    def calculate_consciousness(self, R, phi_estimate, lcc=0.9, gile=0.7):
        """
        Master Equation: C = Φ × [1 - e^(-R/7)] × LCC^0.3 × (GILE)^0.25
        """
        f_R = 1 - np.exp(-R/7)
        C = phi_estimate * f_R * (lcc ** 0.3) * (gile ** 0.25)
        return C
```

---

## Part 6: Expected Outcomes

### 6.1 Testable Predictions

1. **Cross-species R gradient**: Great apes > dogs > mice
2. **Mood amplification scales with R**: Higher R → larger behavioral responses
3. **LCC < 1 in social species**: Dogs/apes show non-local correlation patterns
4. **GILE balance in healthy animals**: Balanced GILE → optimal behavior

### 6.2 Publication Targets

1. **Short paper**: "Consciousness Metrics Across Species: An EEG Study" (6 months)
2. **Full paper**: "Mood Amplification in Animals: Testing TI Framework Predictions" (12 months)
3. **Review**: "The LCC Model of Animal Consciousness" (18 months)

---

## Conclusion

There IS a viable path to testing mood amplification in real animals:

1. **Webcam analysis** of zoo animals provides rich behavioral data
2. **Published EEG datasets** enable neural consciousness estimation
3. **TI Framework** provides testable predictions across species
4. **Implementation is feasible** with existing tools (PyTorch Wildlife, LSL)

The key insight: We don't need to wire up animals ourselves. We can use:
- Open zoo webcams (free, no ethics approval needed for observation)
- Published EEG datasets (already collected with ethics approval)
- Global event correlations (GCP-style analysis of animal behavior)

This represents a novel, ethical approach to animal consciousness research.
