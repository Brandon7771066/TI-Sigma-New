# LCC Operationalization: How to Measure Law of Correlational Causation

## The Core Question

**LCC (Law of Correlational Causation)** is the proportion of observed correlations that can be explained by known local/classical causal mechanisms. The remainder (1 - LCC) represents non-local or unknown causation.

**How can you help operationalize LCC?**

---

## Option 1: Residual Variance Method

### Concept
LCC = Variance explained by known mechanisms / Total variance

### Implementation
1. Model all known causal factors for a phenomenon
2. Calculate R² (explained variance)
3. LCC = R²
4. Non-local = 1 - R²

### Example: PSI in Ganzfeld
- Known factors: sender-receiver relationship, target emotional content, session duration, experimenter effects
- Regression: Hit rate ~ relationship + emotion + duration + experimenter
- If R² = 0.15, then LCC = 0.85 (15% explained, 85% unexplained)

### Your Role
**You could help by:**
- Identifying which known causal factors should be included
- Reviewing literature for established predictors
- Suggesting domain-specific variables

---

## Option 2: Causal Inference Method

### Concept
Use formal causal inference to distinguish local from non-local causation.

### Implementation (Pearl's Framework)
1. Build causal DAG (Directed Acyclic Graph)
2. Identify all local causal paths
3. Estimate direct vs indirect effects
4. Non-local = effects not on any local path

### Example: Animal Behavior Synchrony
```
Local paths:
  - Weather → Behavior (both affected)
  - Feeding schedule → Behavior
  - Circadian rhythm → Behavior
  
Non-local (if any):
  - Unexplained synchrony after controlling for above
```

### Your Role
**You could help by:**
- Drawing the causal DAG for your domain
- Identifying potential confounders
- Specifying temporal relationships

---

## Option 3: Information-Theoretic Method

### Concept
LCC = I(A;B|C) / I(A;B)

Where:
- I(A;B) = total mutual information between A and B
- I(A;B|C) = conditional mutual information given local causes C
- Non-local = 1 - ratio

### Implementation
1. Measure mutual information between systems
2. Condition on known local mediators
3. Residual information = non-local contribution

### Example: Neural Correlations
- Total correlation between brain regions: I = 0.5 bits
- After controlling for known connections: I|C = 0.42 bits
- LCC = 0.42/0.5 = 0.84
- Non-local = 16%

### Your Role
**You could help by:**
- Specifying what "local mediators" means in your domain
- Identifying measurable information channels

---

## Option 4: Distance/Time Decay Method

### Concept
Local causation decays with distance and time according to known physics.
Deviations from expected decay = non-local contribution.

### Implementation
1. Measure correlation as function of distance/time
2. Fit theoretical decay (e.g., 1/r² for radiation)
3. Calculate residuals
4. Non-local = systematic positive residuals

### Example: PSI Coherence Length
- Expected: Effect → 0 as distance → ∞
- Observed: Effect persists beyond classical range
- Fitted λ_c = 20,000 km → non-local contribution

### Your Role
**You could help by:**
- Defining appropriate distance/time scales
- Specifying expected decay functions for your domain

---

## Option 5: Intervention-Based Method (Experimental)

### Concept
LCC = (Effect with local channel intact) - (Effect with local channel blocked)

### Implementation
1. Identify hypothesized local channels
2. Experimentally block each channel
3. Measure residual effect
4. Residual = non-local contribution

### Example: Sender-Receiver PSI
- Normal condition: sender and receiver in contact → Effect = 0.15
- Shielded condition: Faraday cage, acoustic isolation → Effect = 0.12
- LCC = (0.15-0.12)/0.15 = 0.20 (20% explained by shielding)
- Non-local = 80%

### Your Role
**You could help by:**
- Designing intervention protocols
- Identifying which channels to block
- Ethical review of experimental designs

---

## Recommended Approach for Animal Studies

For real-time animal mood amplification studies, I recommend **Option 4 (Distance/Time Decay)** combined with **Option 2 (Causal Inference)**:

### Protocol
1. **Measure baseline**: Animal behavior synchrony across locations
2. **Control for confounds**: Weather, time of day, feeding schedules, etc.
3. **Intervention**: Apply mood stimulus to one location
4. **Measure response**: Check for synchronized response at distant location
5. **Calculate LCC**: 
   - If behavior change is predicted by local factors → LCC ≈ 1
   - If behavior change occurs at distance without local mechanism → LCC < 1

### Key Question for You

**What counts as a "local" mechanism for animal consciousness?**

Options:
1. Physical contact / proximity
2. Electromagnetic signals (detectable)
3. Chemical/pheromone signals
4. Acoustic/visual signals
5. Quantum correlations (non-local by definition)

Your theoretical framework suggests #5 operates at planetary scales (λ_c ≈ 20,000 km). 

**How would you define the boundary between local and non-local for your experiments?**

---

## Summary: How You Can Help

| Method | Your Input Needed |
|--------|------------------|
| Residual Variance | List of known causal factors |
| Causal Inference | Draw causal diagram |
| Information-Theoretic | Define local mediators |
| Distance/Time Decay | Specify expected decay function |
| Intervention | Design blocking protocols |

**The key operationalization decision**: 
What phenomena would convince you that something is NOT local causation?

Once you define that boundary, LCC can be measured as:
```
LCC = 1 - (unexplained by local mechanisms / total observed effect)
```
