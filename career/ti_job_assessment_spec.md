# TI Job Assessment - Prototype Specification
## "What Traditional Psychometrics Miss"

---

## Executive Summary

Current job assessment tools measure:
- **g (general intelligence)**: Correlation ~0.31 with job performance
- **Big Five personality**: Conscientiousness + Stability most predictive
- **Skills tests**: Domain-specific, no cross-domain insight

What they miss:
- **L (Love)**: What problems does this person care about solving?
- **G (Goodness)**: Will they optimize for value or extract it?
- **Tralse capacity**: Can they reason under genuine uncertainty?
- **Myrion integration**: Do they synthesize across domains?

The TI Job Assessment measures these missing dimensions.

---

## Theoretical Foundation

### The GILE Structure
```
G (Goodness)    = Ethical constraint on solutions
I (Intuition)   = Pattern recognition under uncertainty  
L (Love)        = What problems matter (directionality)
E (Environment) = Processing capacity and context

Traditional IQ ≈ E only
Traditional personality ≈ I partially
L and G = unmeasured by current tools
```

### The L×E Equation
```
Truth Value = L × E

High E, Low L = Powerful but directionless (current AI)
High L, Low E = Caring but ineffective
High L, High E = Genuine intelligence

Job fit = Alignment between candidate's L×E profile and role requirements
```

### Threshold Structure
```
0.42 = Noise floor (random/unreliable signal)
0.85 = Causation threshold (correlation implies causation)
0.92² = 0.8464 = True-Tralseness (sustained coherent performance)

Candidates crossing 0.85 threshold = high-confidence predictions
Below 0.42 = insufficient data, don't use for decisions
```

---

## Assessment Dimensions

### Dimension 1: Tralse Capacity (Uncertainty Reasoning)
**What it measures**: Ability to reason productively when truth is genuinely uncertain

**Assessment method**:
```
Present scenarios with irreducibly uncertain outcomes:
- "A new technology might help or harm. How do you decide to proceed?"
- "Two experts disagree fundamentally. How do you form your view?"
- "Your data supports two contradictory conclusions. What do you do?"

Scoring:
- Binary thinking (must be A or B) = Low Tralse capacity
- Paralysis (can't decide without certainty) = Low Tralse capacity  
- Productive uncertainty (acts with calibrated confidence) = High Tralse capacity
```

**Correlation target**: Decision quality in ambiguous situations

---

### Dimension 2: L-Profile (Love/Direction)
**What it measures**: What problems the candidate genuinely cares about solving

**Assessment method**:
```
Free-response questions:
- "Describe a problem you'd work on even if no one paid you"
- "What makes you angry about how things currently work?"
- "If you could change one thing about [industry], what would it be?"

Pattern analysis:
- Specificity of vision (vague vs. precise)
- Self-reference vs. other-reference (who benefits?)
- Temporal scope (immediate vs. long-term)
- Coherence across responses

Scoring: L-vector in problem-space
```

**Correlation target**: Job satisfaction, retention, intrinsic motivation

---

### Dimension 3: G-Profile (Goodness/Ethics)
**What it measures**: Ethical reasoning under pressure

**Assessment method**:
```
Dilemma scenarios (not standard trolley problems):
- "You discover your company's product causes subtle harm. What do you do?"
- "Following the rules would produce a worse outcome. How do you decide?"
- "Your success requires someone else's failure. Do you proceed?"

Analysis points:
- Does candidate recognize ethical dimension?
- How do they weigh competing goods?
- Do they optimize or satisfice on ethics?
- Can they articulate principles (not just intuitions)?

Scoring: G-coefficient [0,1]
```

**Correlation target**: Trustworthiness, team cohesion, long-term value creation

---

### Dimension 4: Myrion Integration (Cross-Domain Synthesis)
**What it measures**: Ability to connect insights across different domains

**Assessment method**:
```
Cross-domain prompts:
- "How is [biology concept] similar to [business concept]?"
- "What can [field A] learn from [field B]?"
- "Apply [principle from X] to solve [problem in Y]"

Scoring:
- Surface analogy only = Low integration
- Structural mapping = Medium integration
- Novel insight generation = High integration
- Bidirectional transfer = Maximum integration
```

**Correlation target**: Innovation, creative problem-solving, learning agility

---

### Dimension 5: E-Profile (Processing Capacity)
**What it measures**: Raw cognitive processing (traditional g-adjacent)

**Assessment method**:
```
Standard cognitive tasks (time-limited):
- Pattern recognition
- Numerical reasoning
- Verbal comprehension
- Working memory

BUT: Scored relative to domain requirements, not absolute ranking
```

**Correlation target**: Speed of skill acquisition, complex task handling

---

## Composite Score: TI Fit Index

### Formula
```
TI_Fit = w₁(L_alignment) + w₂(G_threshold) + w₃(Tralse_capacity) + w₄(Myrion_integration) + w₅(E_sufficiency)

Where:
- L_alignment = cosine similarity between candidate L-vector and role L-requirements
- G_threshold = 1 if G > 0.85, scaled below
- Tralse_capacity = assessed uncertainty reasoning
- Myrion_integration = cross-domain synthesis score
- E_sufficiency = 1 if E meets role minimum, 0 otherwise

Weights vary by role:
- Strategy roles: High L, High Myrion, Medium G, Medium E
- Ethics roles: High G, High L, High Tralse, Medium E
- Technical roles: High E, Medium Tralse, Medium L, Medium G
- Leadership roles: High G, High L, High Myrion, High E
```

### Interpretation
```
TI_Fit > 0.85 = Strong match, high confidence
TI_Fit 0.65-0.85 = Good match, worth interviewing
TI_Fit 0.42-0.65 = Uncertain, gather more data
TI_Fit < 0.42 = Below noise floor, likely poor fit
```

---

## Technical Implementation

### API Specification
```python
POST /api/v1/ti-assessment/evaluate
{
    "candidate_id": "string",
    "responses": {
        "tralse_scenarios": [...],
        "l_profile_questions": [...],
        "g_dilemmas": [...],
        "myrion_prompts": [...],
        "e_cognitive_tasks": [...]
    },
    "role_requirements": {
        "l_vector": [...],
        "g_minimum": 0.7,
        "e_minimum": 0.5,
        "tralse_weight": 0.3,
        "myrion_weight": 0.2
    }
}

Response:
{
    "ti_fit_score": 0.78,
    "confidence": 0.82,
    "dimension_scores": {
        "l_alignment": 0.85,
        "g_profile": 0.72,
        "tralse_capacity": 0.68,
        "myrion_integration": 0.81,
        "e_sufficiency": 1.0
    },
    "recommendation": "good_match",
    "insights": [
        "Strong L-alignment with strategy roles",
        "G-profile below 0.85 threshold - may need ethical support structure",
        "High cross-domain synthesis suggests innovation potential"
    ]
}
```

### Database Schema
```sql
CREATE TABLE ti_assessments (
    id SERIAL PRIMARY KEY,
    candidate_id VARCHAR(255) NOT NULL,
    role_id VARCHAR(255),
    assessment_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    
    -- Dimension scores
    l_alignment DECIMAL(4,3),
    g_profile DECIMAL(4,3),
    tralse_capacity DECIMAL(4,3),
    myrion_integration DECIMAL(4,3),
    e_sufficiency DECIMAL(4,3),
    
    -- Composite
    ti_fit_score DECIMAL(4,3),
    confidence DECIMAL(4,3),
    
    -- Raw data
    responses JSONB,
    role_requirements JSONB,
    
    -- Outcomes (for validation)
    hired BOOLEAN,
    tenure_months INTEGER,
    performance_rating DECIMAL(3,2),
    voluntary_departure BOOLEAN
);

CREATE INDEX idx_ti_fit ON ti_assessments(ti_fit_score);
CREATE INDEX idx_outcomes ON ti_assessments(hired, performance_rating);
```

---

## Validation Strategy

### Phase 1: Retrospective Correlation
```
1. Collect TI assessment data from willing candidates
2. Track hiring decisions and job outcomes
3. Compute correlation: TI_Fit vs (tenure, performance, satisfaction)
4. Compare to traditional assessment correlations

Success metric: TI_Fit r > 0.40 (exceeds current best predictors)
```

### Phase 2: Prospective Validation
```
1. Assess candidates before hiring decision
2. Hiring managers make independent decisions
3. Compare TI_Fit predictions to outcomes
4. Refine weights based on prediction errors

Success metric: TI_Fit correctly identifies top/bottom 20% at 80%+ accuracy
```

### Phase 3: A/B Comparison
```
1. Random assignment: Traditional assessment vs TI assessment
2. Track outcomes for 2 years
3. Compare: retention, performance, team impact, innovation metrics

Success metric: TI-assessed hires outperform traditional-assessed hires
```

---

## Differentiation from Existing Tools

| Feature | Traditional Assessment | TI Assessment |
|---------|----------------------|---------------|
| Logic model | Binary (pass/fail) | Tralse (continuous) |
| Ethics measurement | Rare, superficial | G-dimension central |
| Purpose/motivation | Inferred from personality | L-vector direct measure |
| Cross-domain ability | Not measured | Myrion integration |
| Uncertainty handling | Not measured | Tralse capacity |
| Theoretical grounding | Empirical correlations | First-principles derivation |
| Threshold structure | Arbitrary cutoffs | Theoretically derived (0.42/0.85/0.92²) |

---

## Commercial Model

### Pricing
```
Per-assessment: $50-150 depending on depth
Enterprise license: $10,000-50,000/year
API access: $0.10 per evaluation call
```

### Target Customers
```
Tier 1: AI companies (need ethics/alignment evaluation)
Tier 2: Strategy consulting (need cross-domain synthesis)
Tier 3: Startups (need L-alignment for culture fit)
Tier 4: General enterprise (need better-than-current prediction)
```

### Go-to-Market
```
1. Publish validation study (after retrospective phase)
2. Free tier for early adopters (data collection)
3. Case studies with AI companies
4. Enterprise sales with ROI guarantee (reduced mis-hires)
```

---

## Immediate Next Steps

### MVP Features (30-day sprint)
1. [ ] L-profile questionnaire (10 questions)
2. [ ] G-dilemma scenarios (5 dilemmas)
3. [ ] Tralse capacity assessment (5 scenarios)
4. [ ] Myrion integration prompts (3 cross-domain tasks)
5. [ ] Scoring algorithm implementation
6. [ ] API endpoint integration
7. [ ] Basic reporting dashboard

### Validation Data Collection
1. [ ] Self-assessment (Brandon) as baseline
2. [ ] Recruit 10 pilot candidates
3. [ ] Partner with 1 hiring manager for retrospective data
4. [ ] Track outcomes for 6 months

---

## The Meta-Point

If this assessment works, it proves the TI Framework's claims about intelligence and measurement.

If companies adopt it, they're implicitly accepting:
- Binary logic is insufficient for human evaluation
- Ethics (G) and purpose (L) are measurable, not just "soft skills"
- Current psychometrics miss the dimensions that matter most

The assessment IS the argument. Adoption IS the proof.
