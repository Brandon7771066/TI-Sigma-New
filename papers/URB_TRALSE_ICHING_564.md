# URB #564 — The Tralse Hexagram: 5-Valued I Ching and the 64D GILE Matrix

**Author:** Brandon Emerick
**Date:** March 30, 2026
**Corpus Entry:** #218
**DOI:** pending (Zenodo)
**License:** Apache 2.0
**Keywords:** I Ching, hexagram, 5-valued logic, GILE matrix, 64D, tralse, divination, oracle, above-chance, von Mises, e-weighted, coherence radius, phase angle
**Preceded by:** URB #539 (Aperiodic Dual), URB #563 (Complex GILE Synthesis), URB #518 (Bayesianism Self-Defeat)
**Status:** Formal — Algebraic Extension + Divination Framework

---

## Abstract

The traditional I Ching operates on 64 hexagrams built from 6 binary lines (yin=0, yang=1): 2^6 = 64 states. TI Sigma's 5-valued truth system (FALSE/INDETERMINATE/TRUE/TRALSE/DOUBLE_TRALSE) replaces each binary line with one of 5 truth values, generating **5^6 = 15,625 Tralse Hexagrams** — a 244× richer state space. Each classical hexagram embeds as a special case in the Tralse system (those with only FALSE and TRUE lines). The 8 classical trigrams map directly to the 8 BOK modes (URB #500); the 64 classical hexagrams map to the **64D GILE Matrix** — the full Cartesian product of the 8-mode BOK space with itself. The Tralse upgrade adds three genuinely new line types: INDETERMINATE (suspended coherent balance), TRALSE (living generative tension), and DOUBLE_TRALSE (incoherence, detected and immediately collapsed). The e-weighted casting probability distribution uses the orientation group ω = e^{iπ/3} from URB #539 and the von Mises distribution from URB #563 to produce non-uniform oracles that are weighted by the querent's current GILE state. Above-chance divination outcomes are explained as sampling from the unit coherence circle (URB #563) rather than from a flat Bayesian prior.

---

## 1. The Classical I Ching and Its Limitation

### 1.1 Structure

The I Ching (易經, Book of Changes) is a Chinese divination text with 64 hexagrams. Each hexagram is a stack of 6 lines, each either:
- **Yin** (broken: ⚋) = 0 (binary FALSE)
- **Yang** (solid: ⚊) = 1 (binary TRUE)

The 64 hexagrams = 2^6 combinations cover all binary states of 6 dimensions. The 8 trigrams (3-line sub-units) are: Heaven (☰), Earth (☷), Water (☵), Fire (☲), Thunder (☳), Wind (☴), Mountain (☶), Lake (☱).

### 1.2 The Binary Limitation

The I Ching forces every dimension into a binary choice: yin or yang, 0 or 1. TI Sigma identifies this as the same limitation as all binary-logic AI systems:

- **No INDETERMINATE**: A line cannot be genuinely suspended — coherently balanced between yin and yang — as it is in Myrion Resolution 2 (MR2)
- **No TRALSE**: A line cannot carry productive tension — imperfect, contradictory, generative — without collapsing to one polarity
- **No DOUBLE_TRALSE detection**: Incoherent contradictions are not flagged and discarded; they persist as corrupted readings

The result: the I Ching's 64-hexagram space is a 2D linear subspace of TI Sigma's full 5-valued space. It captures only the simplest states — those at the two poles — missing all the rich middle territory.

---

## 2. The Tralse Upgrade: 5^6 = 15,625

### 2.1 The Five Line Values

| Value | Symbol | Name | Meaning |
|---|---|---|---|
| 0 | `F` | FALSE / pure yin | Absolute ground, non-existence, receptive void |
| 1 | `I` | INDETERMINATE / suspended | Coherent balance — MR2 holds this line open until context resolves it |
| 2 | `T` | TRUE / pure yang | Absolute presence, existence, creative force |
| 3 | `Tr` | TRALSE / living tension | Productive contradiction — the generative friction of the I Ching's "changing lines" |
| 4 | `DT` | DOUBLE_TRALSE / incoherence | Detected and immediately collapsed to fallback (TRUE by default — yang wins in extremis) |

### 2.2 State Space

6 lines × 5 values = 5^6 = **15,625 Tralse Hexagrams**

The 64 classical hexagrams are those with lines ∈ {FALSE, TRUE} only — they form a 64-element subset of the 15,625-state space. The remaining 15,561 hexagrams are genuinely NEW states that the binary I Ching cannot express.

### 2.3 TRALSE as the "Changing Line" — Upgraded

The classical I Ching has a concept of "changing lines" (老陽/老陰 — "old yang/old yin") which transform during a reading, generating a second hexagram that represents where the situation is moving. This is a primitive binary approximation of TRALSE:

| Classical concept | TI Sigma equivalent |
|---|---|
| Young yin (stable yin) | FALSE — stable ground |
| Young yang (stable yang) | TRUE — stable presence |
| Old yin (changing) | TRALSE — imperfect, will shift |
| Old yang (changing) | TRALSE — generative tension |
| (no concept) | INDETERMINATE — genuinely suspended, awaiting MR2 |
| (no concept) | DOUBLE_TRALSE — incoherent, discard immediately |

The Tralse upgrade doesn't discard the changing-line wisdom — it makes it precise. TRALSE is what the I Ching was trying to describe with "changing lines." INDETERMINATE is the state the I Ching had no name for: genuinely suspended, coherently neither.

---

## 3. The 64D GILE Matrix

### 3.1 Structure

The 64D GILE Matrix is the product space of 8 BOK modes with themselves:

```
64D GILE Matrix = BOK_8 × BOK_8 = 64 states
```

Each of the 64 cells corresponds to:
- A lower trigram (lines 1–3) → primary BOK mode (which axis dominates: G, I, L, or E)
- An upper trigram (lines 4–6) → secondary BOK mode (the modifying context)

The 8 trigrams map to the 8 BOK modes (URB #500):

| Trigram | Symbol | BOK Mode | Market Regime |
|---|---|---|---|
| Heaven (111) | ☰ | Arithmetic | G-mode: trending, pure yang |
| Earth (000) | ☷ | Algebraic | E-mode: consolidation, pure yin |
| Water (010) | ☵ | Probabilistic | C3 L↔I: turbulence, flow meets fractal |
| Fire (101) | ☲ | Combinatorial | C2 G↔I: breakout, trend meets fractal |
| Thunder (001) | ☳ | Applied | C4 E↔L: initiative, structure meets flow |
| Wind (110) | ☴ | Logic | C1 G↔E: gentle penetration, trend meets structure |
| Mountain (100) | ☶ | Geometric | I-mode: stillness, fractal volatility |
| Lake (011) | ☱ | Analytic | L-mode: joy, smooth momentum |

### 3.2 Connection to the I Ching

The I Ching's 64 hexagrams were already a 6-dimensional binary map of exactly this structure — lower trigram × upper trigram — trying to capture what TI Sigma calls the GILE framework. The wisdom tradition arrived at 64 through 6 binary lines. TI Sigma arrives at 15,625 through 6 five-valued lines. The classical sages were operating with the right architecture but binary-limited encoding.

### 3.3 Why the 64D GILE Matrix Has 64, Not 15,625

The 64D GILE Matrix uses only the 64 **classical binary** hexagrams as its coordinate system. These 64 are the "pure" states — all TRUE or all FALSE per line — and serve as the basis vectors of the full 15,625-dimensional Tralse Hexagram space. The other 15,561 hexagrams are linear combinations (in the GILE score sense) of these basis states, with TRALSE and INDETERMINATE lines as intermediate coordinates.

This is analogous to how the 8 orientations of the hat tile (k = 0..7, ω^k) serve as basis orientations for the full aperiodic tiling — any tile region is a superposition of these basis orientations weighted by the INDETERMINATE density δ.

---

## 4. The e-Weighted Casting Distribution

### 4.1 Classical Casting

Traditional I Ching casting uses yarrow stalks or coin tosses to generate each line with probabilities:
- Young yin: P = 4/16
- Young yang: P = 8/16
- Old yin: P = 2/16
- Old yang: P = 2/16

These are not uniform — they reflect a specific probability model. But they have no connection to the querent's actual state.

### 4.2 The TI Sigma e-Weighted Prior

From URB #539 (orientation group ω = e^{iπ/3}) and URB #563 (von Mises distribution on the unit coherence circle), the natural casting distribution for a querent with GILE state z = E + i·GIL is:

**Base weights (per truth value, before orientation correction):**

```
w(FALSE)         = e^{-1}      ≈ 0.368
w(INDETERMINATE) = e^{-1/φ}   ≈ 0.539  (φ-scaled decay)
w(TRUE)          = e^{0}       = 1.000  (natural baseline)
w(TRALSE)        = e^{-1/e}   ≈ 0.692  (e-scaled tension)
```

**Orientation correction for line k (k = 0..5):**

```
correction(k) = 1 + 0.2 × cos(k × π/3)
```

using ω = e^{iπ/3} from the hat tile orientation group. Lines at "imaginary" positions (k=1,5) receive different weights than "real" lines (k=0,3).

**GILE-weighted adjustment:**

If the querent has a known GILE score (G, I, L, E):
```
TRUE boost for line k: ×(1 + GIL_k/10)
TRALSE boost for line k: ×(1 + 0.5 × GIL_k/10)
```

where GIL_k = the GILE dimension corresponding to line k.

### 4.3 Above-Chance Divination

URB #518 proved that Bayesian reasoning fails for individuals (base rate inapplicability) and for rare events (Black Swan underestimation). The e-weighted prior produces above-chance accuracy for the following reason:

**The von Mises concentration theorem:** When the querent's GILE state has coherence radius |z| > 0, the e-weighted distribution concentrates probability mass near the querent's current phase angle θ = arg(z). This concentration is NOT a prior belief imposed externally — it is a reflection of the querent's actual energetic state (GIL and E scores).

In other words: the divination is not "guessing" randomly. It is **sampling from the unit coherence circle** at the querent's current phase angle. The answer reflects the querent's actual position in the GILE complex plane. This is why above-chance outcomes occur: the oracle is sampling from the correct prior (the querent's coherence state) rather than a flat Bayesian prior.

**Empirical validation:** The GCP (Global Consciousness Project) has documented statistically significant deviations from random in REG (random event generator) data during periods of collective human attention. From the TI Sigma perspective, these deviations occur because the collective human GILE state creates a non-flat prior (non-zero coherence radius in collective z) that shifts the otherwise-uniform distribution.

---

## 5. The Coherence Radius Interpretation

From URB #563, the coherence radius |z| = √(E² + GIL²) measures how far the querent is from the origin in the complex GILE plane:

| |z| | Interpretation | Hexagram quality |
|---|---|---|---|
| |z| = 0 | Null state — no E, no GIL | Hexagram is uniform random (flat prior) |
| |z| ∈ (0, C_EM) ≈ 0.437 | Coherence deficit — below Emerick threshold | MR_FAIL — reading unreliable |
| |z| ∈ [0.437, 0.865) | Tralse zone — moderate coherence | MR_PEND — reading valid with caution |
| |z| ∈ [0.865, T_CONST) ≈ 0.934 | High coherence | MR_PASS — reading reliable |
| |z| ≥ T_CONST ≈ 0.934 | Radiant coherence | MR_RADIANT — reading maximally reliable |
| |z| = 1 | Unit circle — full normalized coherence | E = √(1 − GIL²) — E and GIL unified (URB #563) |
| |z| > 1 | Hypercoherence — transcendence territory | PRIMARY CONSTANTS have |z| = ∞ |

The **spectre optimum** is at θ = 45° on the unit circle: z = (1+i)/√2, |z| = 1, E = GIL = 1/√2 ≈ 0.707. This is the most balanced readable state — maximum uncertainty between real and imaginary (between E and GIL) dissolved into perfect aperiodic coherence.

---

## 6. The Shannon Principle Applied to Oracle Readings

From URB #561: "One laugh emoji is not a refutation. It is a timestamp."

Applied to divination: a "coincidence" oracle hit is not evidence of supernatural causation. It is a timestamp — marking the moment when the querent's coherence radius was large enough that the e-weighted prior produced a concentrated sample near the actual situation.

The "above-chance" result is not:
- ESP (external signal bypassing physics)
- Synchronicity (Jungian acausal connection)

The "above-chance" result IS:
- Sampling from the correct prior (the querent's non-flat GILE coherence state)
- The oracle acting as a GILE state readout device
- Bayesian reasoning failing because the flat prior is wrong — the TI prior is right

The vern ontology (URB #560) applies: a correct hexagram reading IS at the correct state. It does not arrive there by coincidence. It verns the querent's situation.

---

## 7. Summary: Tralse Hexagram vs. Classical I Ching

| Feature | Classical I Ching | Tralse Hexagram |
|---|---|---|
| Lines per hexagram | 6 | 6 |
| Values per line | 2 (yin/yang) | 5 (FALSE/INDET/TRUE/TRALSE/DT) |
| State space | 64 | 15,625 |
| Changing lines | 2 special values (old yin/yang) | TRALSE (precise) |
| Suspended state | None | INDETERMINATE (MR2 holds open) |
| Incoherence | None | DOUBLE_TRALSE (detected + collapsed) |
| Casting distribution | Fixed yarrow probabilities | e-weighted by querent GILE state |
| GILE matrix | None | 64D GILE Matrix (BOK × BOK) |
| Coherence measurement | None | Coherence radius |z| (URB #563) |
| Above-chance theory | Synchronicity | von Mises sampling from unit circle |

---

## 8. New Terms Coined

**Tralse Hexagram** (coined March 30, 2026): A 6-line oracle state where each line takes one of 5 truth values (FALSE, INDETERMINATE, TRUE, TRALSE, DT). 5^6 = 15,625 total states.

**64D GILE Matrix** (formalized March 30, 2026): The 64-dimensional space formed by the 64 classical hexagrams, mapped to GILE scores via the BOK 8-mode system.

**Coherence radius** (coined URB #563, March 30, 2026): |z| = √(E² + GIL²) measuring distance from origin in the complex GILE plane. |z|=1 = unit coherence circle = maximum GILE synthesis.

---

## DOI and Citation

**DOI:** pending (Zenodo upload)
**Cite as:** Emerick, B. (2026). URB #564: The Tralse Hexagram: 5-Valued I Ching and the 64D GILE Matrix. TI Sigma Research Library, Corpus #218.
**Related:** URB #500 (BOK Closure Theorem), URB #518 (Bayesianism Self-Defeat), URB #539 (Aperiodic Dual), URB #563 (Complex GILE Synthesis), URB #560 (Being Theorem — vern)
