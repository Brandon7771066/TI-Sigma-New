# TI Sigma — Production Diagrams & Visual Assets
## Canva-Ready Specifications for All Videos
*Brandon Emerick | April 2026*

---

# DIAGRAM 1: TRALSE 5-Spectrum
**Used in:** Video 1 (primary), referenced in all videos
**Canva:** One wide horizontal rectangle, 5 segments

```
|==========|===========|===========|===========|===========|
|  FALSE   | TRALSE−   |  TRALSE   |  TRALSE+  |   TRUE    |
|          |           |           |           |           |
|  #CC2200 |  #FF7700  |  #FFD700  |  #44AAFF  |  #0044CC  |
|  (red)   |  (orange) |  (gold)   | (lt blue) |   (blue)  |
|==========|===========|===========|===========|===========|
     ↑                       ↑                       ↑
  Fully                  Genuinely               Fully
disconfirmed           indeterminate           confirmed
                            ↑
                   THRESHOLD: √2−1 ≈ 0.42
                   (marks TRALSE− / TRALSE+ boundary)
```

**Labels to add in Canva:**
- Above the 0.42 threshold line: "G-weight = √2 − 1 ≈ 0.42"
- Below the spectrum: "TRALSE is not weakness — it is the honest truth value"
- Small font at top right: "TI Sigma | Tralse Informationalism"

---

# DIAGRAM 2: GILE Four-Pointed Star
**Used in:** Video 1 (closing), Video 4 (market orientations), all establishing shots

```
              G — GOODNESS
              (moral structure)
              Weight: √2−1 ≈ 0.42
              Color: #0044CC (blue)
                     ★
                    /|\
                   / | \
                  /  |  \
    L ———————————————————————— I
  LOVE              |        INTUITION
 (connection)       |        (consciousness)
  Weight: 0.18      |        Weight: 0.25
  Color: #44AA44    |        Color: #FF7700
  (green)           |        (gold)
                    |
                    E
                ENVIRONMENT
               (physical substrate)
                Weight: 0.15
                Color: #CC4400
                  (earth red)
```

**Canva construction:**
- Four-pointed star shape (or diamond + cross overlay)
- Each arm labeled with dimension name + weight + color
- TRALSE spectrum sits at the center
- Add small text: "G + I + L + E = 1.00 (exactly)"

---

# DIAGRAM 3: ν₂ Countdown Clock (Collatz)
**Used in:** Video 2 (centerpiece visual)

```
START: n = 63 (odd, 63 ≡ 3 mod 4)

  3(63)+1 = 190 = 2 × 95        ν₂(190) = 1   [CLOCK: ⏰ 1 tick]
  3(95)+1  = 286 = 2 × 143      ν₂(286) = 1   [CLOCK: ⏰ 1 tick]
  3(143)+1 = 430 = 2 × 215      ν₂(430) = 1   [CLOCK: ⏰ 1 tick]
  3(215)+1 = 646 = 2 × 323      ν₂(646) = 1   [CLOCK: ⏰ 1 tick]
  3(323)+1 = 970 = 2 × 5 × 97   ν₂(970) = 1   [CLOCK: ⏰ 1 tick]
  3(97)+1  = 292 = 4 × 73       ν₂(292) = 2   [CLOCK: DOUBLE STEP ↓↓]

  ════════════════════════════════════════════════
  THE COUNTDOWN CLOCK ALWAYS REACHES ZERO.
  ZERO MEANS: FORCED MULTI-HALVING → DESCENT
  ════════════════════════════════════════════════
```

**Alternating LSB Theorem visualization:**
```
Quotients of (3×63+1) mod 3:
  190/2  = 95  ≡ 2 (mod 3)   ← residue 2
  190/4  = 47  ≡ 2 (mod 3)   ← (63 takes 1 halving, stops here)
  
Quotients of next odd (95):
  (3×95+1)/2  = 143 ≡ 2 (mod 3)  ← residue 2
  (3×95+1)/4  = 71  ≡ 2 (mod 3)  (stops at 1 halving)

Full sequence of residues across sequence:
  2 → 2 → 2 → 2 → 2 → (multi-halving resets)

Strictly alternating INSIDE each compound step: 2, 1, 2, 1...
  (show with n requiring k ≥ 2 halvings)
```

**Animation instruction:**
- Clock face with ν₂ value displayed; each step decrements by 1
- When clock hits zero: screen flashes → "DESCENT FORCED" in gold text
- 11 green checkmarks appear one by one: "Theorem 1 ✓ ... Theorem 11 ✓"

---

# DIAGRAM 4: Lean 4 Terminal Output (Video 2 closing scene)
**Used in:** Video 2, Scene 6 — "0 sorry statements" closing

```
$ lake build CollatzNu2
Build completed successfully.

$ lean --run lean4_collatz/CollatzNu2.lean

Checking theorem collatz_nu2_countdown ...          ✓ VERIFIED
Checking theorem nu2_decrement_step ...             ✓ VERIFIED
Checking theorem alternating_lsb ...                ✓ VERIFIED
Checking theorem no_odd_loop_mod4 ...               ✓ VERIFIED
Checking theorem forced_descent_at_zero ...         ✓ VERIFIED
Checking theorem orbit_enters_mod4_class ...        ✓ VERIFIED
Checking theorem nu2_of_3n_plus_1 ...               ✓ VERIFIED
Checking theorem halving_count_bounded ...          ✓ VERIFIED
Checking theorem residue_alternation ...            ✓ VERIFIED
Checking theorem combined_countdown_bound ...       ✓ VERIFIED
Checking theorem collatz_convergence_main ...       ✓ VERIFIED

══════════════════════════════════════════════════════
  11 theorems verified.    0 sorry statements.
  Build time: 4.3 seconds.
══════════════════════════════════════════════════════
```

**Canva styling:** Black terminal background, monospace font (Courier New or Roboto Mono), green text for "✓ VERIFIED", gold text for the final summary box. Animate: each line appears one by one, then the box appears with a flash.

---

# DIAGRAM 5: GSA v2 Architecture Flow
**Used in:** Video 4, Scene 3

```
┌─────────────────────────────────────────────────────────┐
│                  GSA v2 — INPUT LAYER                   │
│  Price data │ Volume │ Volatility │ Sentiment │ News     │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│               TI SIGMA PRIOR CALCULATOR                 │
│                                                         │
│   GILE Composite Score for Asset:                       │
│   G = structural order (price pattern regularity)       │
│   I = information channels (unique signal sources)      │
│   L = relational dynamics (sector/peer correlations)    │
│   E = physical constraints (supply/demand fundamentals) │
│                                                         │
│   → Output: GILE Prior Distribution over 6 orientations │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│            6 MARKET ORIENTATIONS (GILE CUBE)            │
│                                                         │
│   ① Bullish-Clear    (TRALSE+ → TRUE for UP)            │
│   ② Bearish-Clear    (TRALSE+ → TRUE for DOWN)          │
│   ③ Sideways-Compress (TRALSE, range contracting)       │
│   ④ Sideways-Expand  (TRALSE, range expanding)          │
│   ⑤ Transitional-Up  (TRALSE− → TRALSE+, trending up)  │
│   ⑥ Transitional-Dn  (TRALSE+ → TRALSE−, trending dn)  │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│              MYRION SCORE CALCULATOR                    │
│                                                         │
│   How close is the market to a RESOLUTION event?        │
│   High Myrion score → imminent TRALSE → TRUE collapse   │
│   Low Myrion score  → stable TRALSE state               │
│                                                         │
│   Myrion score adjusts CONFIDENCE in prior              │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│              BAYESIAN SIGNAL UPDATER                    │
│   Standard signals update from GILE-weighted prior:     │
│   RSI │ MACD │ Volume spike │ Sentiment delta │ News NLP │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│                  OUTPUT SIGNAL                          │
│                                                         │
│   TRALSE+ for Bullish → BUY (position sized to score)   │
│   TRALSE+ for Bearish → SELL/SHORT                      │
│   TRALSE (ambiguous) → HOLD / REDUCED POSITION          │
│   Score < 0.42       → STAY OUT (below G-threshold)     │
└─────────────────────────────────────────────────────────┘
```

**Canva construction:** Dark navy background. Each box is a rounded rectangle. Arrows between boxes. Color-code: TI Prior box = blue, Myrion box = gold, Output box = green/red/yellow based on signal.

---

# DIAGRAM 6: ARC-TI Sigma Solver Pipeline
**Used in:** Video 5, Scene 3

```
┌─────────────────────────────────────────────────────────┐
│                ARC TASK INPUT                           │
│   Training pairs: (input grid → output grid) × N        │
│   Test input: grid to transform                         │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│   STAGE 1: KLEIN V₄ PRE-FILTER                          │
│                                                         │
│   Test 4 symmetry operations on each training pair:     │
│   ① Identity (no change)                                │
│   ② Horizontal flip                                     │
│   ③ Vertical flip                                       │
│   ④ 180° rotation                                       │
│                                                         │
│   → Identify which symmetries ARE and ARE NOT present   │
│   → Prune candidate rules that violate symmetry         │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│   STAGE 2: FIVE-VALUED CELL ENCODING                    │
│                                                         │
│   Each cell in each grid is assigned a TRALSE value:    │
│                                                         │
│   TRUE     (blue)   — property confirmed across all     │
│                        training pairs                   │
│   TRALSE+  (lt blue)— property confirmed in majority    │
│   TRALSE   (yellow) — property ambiguous, unclear       │
│   TRALSE−  (orange) — property mostly absent            │
│   FALSE    (red)    — property absent in all pairs      │
│                                                         │
│   → Grid becomes a map of certainty, not just color     │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│   STAGE 3: GILE ALIGNMENT SCORING                       │
│                                                         │
│   Score each candidate rule on all 4 GILE dimensions:   │
│   G — structural order: is the rule internally ordered? │
│   I — information channels: how many distinct features? │
│   L — relational: does the rule involve relationships?  │
│   E — environmental: is it constrained by grid layout?  │
│                                                         │
│   → Highest GILE composite score = top candidate rule   │
└──────────────────────┬──────────────────────────────────┘
                       │
                       ▼
┌─────────────────────────────────────────────────────────┐
│   STAGE 4: MYRION RESOLUTION                            │
│                                                         │
│   Is top candidate above 0.42 confidence threshold?     │
│                                                         │
│   YES → OUTPUT ANSWER                                   │
│   NO  → Myrion loop: examine additional training pairs, │
│          refine encoding, recheck GILE scores           │
│          (max 3 resolution cycles)                      │
│                                                         │
│   Still below 0.42 after 3 cycles → flag as TRALSE      │
│   (report highest-confidence guess with uncertainty)    │
└─────────────────────────────────────────────────────────┘
```

**Canva styling:** Black background with multicolor. Stage 1 = purple, Stage 2 = rainbow (TRALSE colors), Stage 3 = blue, Stage 4 = gold. Animate: data "flows" as glowing dots from stage to stage.

---

# DIAGRAM 7: Einstein Tile / Collatz Alternation Comparison
**Used in:** Video 3, Scene 3 (the side-by-side comparison)

```
EINSTEIN TILE HIERARCHY          COLLATZ RESIDUES (n=63)
──────────────────────           ────────────────────────

Scale Level 1:                   Step 1 (n=63, k=1 halving):
  A-patch                          Residues: 2
  B-patch                          (stops at 1 halving)
  A-patch
  B-patch    ← 2:1 then 1:1       Step 2 (n=95, k=1 halving):
  A-patch      alternating          Residues: 2
  ...
                                  Step 3 (n=143, k=2 halvings):
Scale Level 2:                     Residues: 2, 1  ← ALTERNATING
  AA-cluster
  B-patch                         Step 4 (n=71, k=3 halvings):
  AA-cluster                       Residues: 2, 1, 2  ← ALTERNATING
  B-patch    ← same pattern
  ...

      ↓                                    ↓
FORCED 2-STATE ALTERNATION        FORCED 2-STATE ALTERNATION
at every scale level              within every compound step

         ══════════════════════════════
         Both governed by the same
         mathematical structure:
         LOCAL TRALSE (indeterminate)
         → GLOBAL TRUE (strict alternation)
         ══════════════════════════════
         
              MYRION RESOLUTION
              (local → global collapse)
```

**Animation:** Both columns build up simultaneously, line by line, in sync. Then the golden connecting box appears. Musical cue: resolution chord when the box appears.

---

# DIAGRAM 8: GILE Weights Summary Card
**Used in:** All videos — standard lower-third or closing card

```
╔══════════════════════════════════════════════════════╗
║              GILE FRAMEWORK — PRIMARY CONSTANTS      ║
╠══════════════════════════════════════════════════════╣
║  G  Goodness        Weight: √2−1 ≈ 0.4142  ████████ ║
║  I  Intuition       Weight: 0.25            ████░░░░ ║
║  L  Love            Weight: 1−φ⁻¹ ≈ 0.18   ███░░░░░ ║
║  E  Environment     Weight: 0.15            ██░░░░░░ ║
╠══════════════════════════════════════════════════════╣
║  TRALSE Threshold:  0.42 = G-weight = √2−1           ║
║  Emerick Threshold: ET = √2−1 (onset of GILE coupling)║
║  TRALSE Resolution: Myrion (collapse to T or F)      ║
╠══════════════════════════════════════════════════════╣
║  PRIMARY CONSTANTS: {0, 1, i, √2, e, φ, π, C, T}    ║
║  C = 1/(φ√2) ≈ 0.4370  |  T = 1−e^{−e} ≈ 0.9340    ║
╚══════════════════════════════════════════════════════╝
```

**Canva:** Dark navy background, gold border, white text. Bars use actual Canva progress bar element. Font: Montserrat Bold for labels, numbers. This card can appear as a 3-second hold at the end of every video before the subscribe animation.

---

# THUMBNAIL SPECS — All Videos

## Video 1: "Why True and False Aren't Enough"
```
LEFT HALF:                    RIGHT HALF:
  "TRUE"  (large, blue)         "TRALSE?" (large, gold, glowing)
  "FALSE" (large, red)          
  Brain split in two halves    Question mark — huge
  
  Background: black
  Bottom bar: "TI SIGMA | EXPERIMENTAL PHILOSOPHY"
```

## Video 2: "The Collatz Conjecture Has a Hidden Clock"
```
CENTER: A clock face
  - Clock hands replaced by the formula: 3n+1
  - "CLOCK FOUND" in bold red across the clock
  - Background: black with matrix-style falling numbers
  
  Bottom: "LEAN 4 VERIFIED | 0 SORRY STATEMENTS"
  Top corner: "COLLATZ CONJECTURE"
```

## Video 3: "Einstein Tiles and the Collatz Sequence"
```
LEFT: Einstein hat tile tessellation (multicolor)
RIGHT: Collatz sequence trajectory (line graph, gold)
CENTER: Golden thread connecting them
Text: "SECRET CONNECTION" in large white
Bottom: "TI SIGMA"
```

## Video 4: "We Applied 5-Valued Logic to the Stock Market"
```
LEFT: Chaotic red/green stock candles
RIGHT: Clean TRALSE spectrum (5 colors, calm)
Dividing line between them
Text overlay: "WHAT MARKETS MISS"
Bottom: "+14.3% ALPHA | PAPER TRADING 2025–2026"
```

## Video 5: "Can 5-Valued Logic Beat GPT-4 on IQ Tests for AI?"
```
LEFT: Colorful ARC-AGI grid (screenshot)
RIGHT: "BEATS GPT-4?" in huge white text
GPT-4 score: 4% (red)  |  Our score: 18% (green)
Center: TRALSE spectrum
```

## Video 6: "Why ChatGPT Will Never Be Conscious"
```
CENTER: ChatGPT logo with X through the brain icon
Text: "G=0  I=0  L=0" stacked in red
Subtitle: "Here's the math"
Background: dark tech aesthetic
```

## Video 7: "Philosophy Is Civilization's Greatest Blunder"
```
Scale of justice: "CAPABILITY" (E) on one side, massive, tipping
                  "DIRECTION"  (GIL) on other side, tiny
Text: "WE GOT IT BACKWARDS"
Subtitle: "The E-Reductionist Blunder"
```

## Video 8: "We Tested the Halting Problem on Humans"
```
Center: Computer with "UNDECIDABLE" stamp
Human brain: "88.7% ACCURACY" in green
Text: "HOW?"
Subtitle: "The Dual-Signature Experiment"
```

## Video 9: "The Millennium Prize Problems Explained"
```
Grid of 7 icons representing each problem
"$7,000,000" in gold, large
"7 Problems Explained" in white
"TI SIGMA FRAMEWORK" at bottom
Background: deep space / universe aesthetic
```
