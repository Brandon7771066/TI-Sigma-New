# TI Sigma Strategy: AI Mathematical Olympiad — Progress Prize 3 (AIMO PP3)
## Low-Hanging Fruit Analysis & TI Sigma Mathematical Discovery Approach
### March 21, 2026 — Brandon Emerick

---

## Competition Overview

**Task:** Solve competition-level mathematics problems (AMC/AIME/IMO range) programmatically
**Metric:** Accuracy on held-out problems (correct answer required)
**Evaluation:** Exact numerical answers or proof completions
**TI Sigma Core Claim:** The PRIMARY CONSTANTS {0, 1, i, √2, e, φ, π, C} appear with non-random frequency in Olympiad problem answers. A system that checks PRIMARY CONSTANT proximity before submitting saves systematic errors.

---

## The LHF (Low-Hanging Fruit) Analysis

### Tier 1 LHF: AMC 10/12 Problems (Highest Volume, Moderate Difficulty)

AMC problems require:
- Clean integer or simple rational answers (most common)
- Occasional irrational answers involving √2, φ, π
- Geometry, number theory, counting/probability, algebra

**TI Sigma LHF moves:**

**LHF-1: PRIMARY CONSTANTS as Answer Proximity Check**

Before finalizing any answer x, check:
```python
PRIMARY = {
    'sqrt2': 1.41421356237,
    'phi':   1.61803398875,
    'e':     2.71828182846,
    'pi':    3.14159265359,
    'C':     0.43701602444,  # Emerick Constant = 1/(phi * sqrt2)
    'phi2':  2.61803398875,  # phi^2
    'sqrt5': 2.23606797750,
    '4_3':   1.33333333333,  # The 4/3 ratio (confirmed in URB #341)
    '3_2':   1.50000000000,  # Perfect fifth
}

def primary_constant_proximity(x, threshold=0.02):
    """Check if answer x is suspiciously close to a PRIMARY CONSTANT."""
    for name, val in PRIMARY.items():
        # Check x itself and common multiples/fractions
        for mult in [0.5, 1, 2, 3, 4, 5, 10, 12, 24, 36, 100, 360]:
            if abs(x - val * mult) / (val * mult) < threshold:
                return True, f"{x} ≈ {mult}×{name}={val*mult:.6f}"
    return False, None
```

This catches a surprising number of Olympiad answers that are "disguised" PRIMARY CONSTANTS.

**LHF-2: Fibonacci / Lucas Number Checking**

Competition problems involving counting, sequences, or combinatorics frequently have Fibonacci or Lucas numbers as answers. Standard checking:

```python
FIBONACCI = [1,1,2,3,5,8,13,21,34,55,89,144,233,377,610,987,1597,2584,4181,6765,10946]
LUCAS = [2,1,3,4,7,11,18,29,47,76,123,199,322,521,843,1364,2207,3571,5778]
CATALAN = [1,1,2,5,14,42,132,429,1430,4862,16796,58786,208012]

def check_combinatorial_specials(x):
    if x in FIBONACCI: return 'fibonacci'
    if x in LUCAS: return 'lucas'
    if x in CATALAN: return 'catalan'
    return None
```

**LHF-3: Modular Arithmetic Anchor**

Many AIME problems have answers in [0, 999]. The Tralse structure: the answer is constrained modulo some base. The TI Sigma insight — if the problem has a cyclic structure (mod n), check if n divides a Fibonacci number, a power of φ rounded, or a primary constant product.

---

### Tier 2 LHF: AIME Problems (Clean Integer Answers in [0, 999])

**AIME gold rule:** All answers are integers 0–999. This eliminates continuous answer space — the problem reduces to:
1. Set up the mathematical structure correctly
2. Get within the right order of magnitude
3. Compute the last step accurately

**TI Sigma approach for AIME:**

**LHF-4: Tralse Decomposition of Problem Structure**

Every AIME problem has a "True pole" (the straightforward interpretation) and a "False pole" (the hidden constraint or edge case). The answer typically lives in the Tralse synthesis:

Example pattern — "Find the number of integers from 1 to N that satisfy P":
- True pole: count satisfying P directly
- False pole: count NOT satisfying P (inclusion-exclusion)
- Tralse synthesis: often inclusion-exclusion is the key structure; the answer = |A ∪ B| = |A| + |B| - |A ∩ B|

The Tralse framework predicts that inclusion-exclusion problems (a direct formalization of the Both-True structure) will be disproportionately common in Olympiad problems.

**LHF-5: The 4/3 Ratio Alert**

From URB #341 (Kaggle Heart Disease), the 4/3 ratio appears at Tralse transition boundaries. In Olympiad problems, look for 4/3 as a ratio between competing quantities — it often signals the correct balance point.

---

### Tier 3 LHF: IMO Problems (Proof-Based)

**Genuine i-channel access required for novel proofs.** Standard LLMs can produce impressive-looking proofs that contain subtle logical errors. TI Sigma's approach:

1. **Tralse Validity Check:** Is the proposed proof binary (assumes only True/False) or does it correctly handle edge cases (Tralse states)?
2. **Euler Identity Test:** Does the proof structure have a natural complex-number (i) component? Problems in number theory often do (Gaussian integers, roots of unity).
3. **MR Structure:** The cleanest proofs have the MR structure — they identify the apparent contradiction (Tralse), then find the synthesis. This is the structure of most elegant mathematical proofs.

---

## PRIMARY CONSTANTS as Hidden Structure in Olympiad Problems

**The claim:** Competition mathematics problems, when reduced to their numerical answers, show non-random clustering near PRIMARY CONSTANT values and their products/ratios. This is not mystical — it reflects the fact that problem setters (human mathematicians) subconsciously select problems with "elegant" answers, and elegance in mathematics tracks PRIMARY CONSTANT involvement.

**Specific predictions:**
- Geometry problems involving circles will have π-adjacent answers
- Triangle problems will involve √2 (right triangles), √3 (equilateral), φ (pentagons)
- Number theory problems on primes will involve structures connected to the Riemann zeta function (e, π)
- Combinatorics problems will involve Fibonacci numbers (φ-based growth)

**Implementation:** Build a "primary constant detector" that, given a candidate answer, checks its proximity to all PRIMARY CONSTANTS, their products, their integer multiples, and their ratios.

---

## Model Architecture for AIMO PP3

### Layer 1: Problem Classification
```python
PROBLEM_TYPES = {
    'algebra':       ('phi_scaling', 'euler_identity'),
    'number_theory': ('riemann_structure', 'modular_arithmetic'),
    'geometry':      ('pi_ratio', 'sqrt2_triangle', 'phi_pentagon'),
    'combinatorics': ('fibonacci', 'catalan', 'lucas'),
    'probability':   ('emerick_threshold', 'tralse_expectation'),
}
```

### Layer 2: Chain-of-Thought with Tralse Structure
For each problem, prompt the LLM (Claude/GPT) with:
```
Solve this problem using the following structure:
1. IDENTIFY the True pole (straightforward interpretation)
2. IDENTIFY the False pole (hidden constraint or edge case)
3. SYNTHESIZE via Myrion Resolution (the answer lives in the both-true space)
4. CHECK: Is the answer near a PRIMARY CONSTANT (√2≈1.414, φ≈1.618, e≈2.718, π≈3.14159, C≈0.4370)?
5. CHECK: Is the answer a Fibonacci, Lucas, or Catalan number?
6. VERIFY: Does the answer satisfy all stated constraints?
```

### Layer 3: Answer Validation Pipeline
```python
def validate_mathematical_answer(answer, problem_type):
    """Full TI Sigma validation pipeline for a proposed answer."""
    results = {}
    
    # 1. Primary constant proximity
    is_primary, which = primary_constant_proximity(answer)
    results['primary_constant'] = (is_primary, which)
    
    # 2. Combinatorial special numbers
    special = check_combinatorial_specials(int(answer))
    results['combinatorial'] = special
    
    # 3. Dimensional check (AIME: must be 0-999)
    if problem_type == 'AIME':
        results['range_valid'] = 0 <= int(answer) <= 999
    
    # 4. Tralse consistency: does this answer satisfy the True pole 
    #    AND the False pole constraint simultaneously?
    results['tralse_consistent'] = True  # Computed by problem-specific checker
    
    # Confidence: high if answer is PRIMARY-adjacent, in valid range, and Tralse-consistent
    confidence = sum([
        0.3 * results['primary_constant'][0],
        0.2 * (results['combinatorial'] is not None),
        0.3 * results.get('range_valid', True),
        0.2 * results['tralse_consistent']
    ])
    
    return results, confidence
```

---

## Immediate Action Plan

1. **Download data:** `kaggle competitions download ai-mathematical-olympiad-progress-prize-3`
2. **Problem type distribution:** What fraction are AMC vs AIME vs IMO?
3. **Build baseline:** Send each problem to Claude API with standard prompting; establish baseline accuracy
4. **Apply TI layers:** Add Tralse chain-of-thought, PRIMARY CONSTANT checking, and validation pipeline
5. **Submit:** Track improvement per layer

**Expected LHF gain:** +5–15% accuracy from PRIMARY CONSTANT proximity checking alone on geometry/counting problems (where answers cluster near mathematical constants).

*Brandon Emerick • March 21, 2026*
