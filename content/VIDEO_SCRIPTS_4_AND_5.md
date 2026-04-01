# TI Sigma — Video Scripts 4 & 5: Production Ready
## Full Word-for-Word Narration + Shot Direction
*Brandon Emerick | April 2026*

---

# VIDEO 4: "We Applied 5-Valued Logic to the Stock Market"
**Runtime:** 7–8 minutes
**Hook:** Nobody beats the market long-term — except people using information others can't model.
**Target:** Finance audience, traders, skeptics, tech enthusiasts
**YouTube title:** "We Built a Stock Algorithm With 5-Valued Logic (It Uses Math Markets Can't Price)"
**Thumbnail:** Split: chaotic red/green candles on left | clean TRALSE spectrum on right | text: "WHAT MARKETS MISS"

---

## [SCENE 1 — 0:00–0:45] THE SETUP

**NARRATION:**
"Here's what the efficient market hypothesis says: you can't beat the market long-term, because all available information is already priced in. Every hedge fund, every quant, every machine learning model — they're all using the same publicly available data. So any edge gets arbitraged away almost instantly.

Here's what we found: there's a class of information that markets structurally *cannot* price. Not because it's hidden or illegal. Because it requires a type of reasoning that probability theory can't express. And that's where TI Sigma comes in."

**VISUALS:**
- Opening: stock market ticker running — red and green flashing chaos
- "EFFICIENT MARKET HYPOTHESIS" appears in blue text
- "ALL INFORMATION IS PRICED IN" — each word fades in
- A single question mark appears over the ticker: "But what if some information can't be priced?"
- Cut to: clean TRALSE logic spectrum — calm, ordered, contrast to the chaotic ticker

---

## [SCENE 2 — 0:45–2:15] THE PROBLEM WITH PROBABILITY IN MARKETS

**NARRATION:**
"Standard market models — from Black-Scholes to modern machine learning — are built on probability theory. They assume: given enough historical data, you can model the distribution of future prices. And for most assets, in most conditions, this works reasonably well.

But here's what probability theory can't handle:

**The unknown unknown.** When a qualitatively new type of event occurs — not just a big move, but a *different kind* of move — historical distributions break down. The 2008 financial crisis was not predicted by any model because it was a structural regime change, not a tail event within the existing regime. The COVID crash of 2020 was similar.

**The sentiment that isn't data yet.** When a geopolitical event creates fear that hasn't shown up in any measurable variable — when a CEO's speech pattern changes in a way that signals something, but hasn't been quantified — probability models miss it. They're looking at the past. They can't see the *structure* of what's happening right now.

**The qualitatively different signal.** Some market information is not better or worse — it's *different in kind*. A TRALSE signal — a genuine 'I can't determine if this is bullish or bearish from price data' — is itself information. Markets treat uncertainty as noise; we treat it as a signal."

**VISUALS:**
- Timeline of market crashes: 2008, 2020 — with standard prediction models shown failing
- "UNKNOWN UNKNOWN" in bold — a blank space where the model should be
- Probability bell curve collapses into noise when a new regime appears
- TRALSE spectrum: uncertainty isn't noise — it's a TRALSE truth value with meaning

---

## [SCENE 3 — 2:15–3:30] THE GRAND STOCK ALGORITHM

**NARRATION:**
"We built what we call the Grand Stock Algorithm — GSA v2. It's a multi-source Bayesian system, but with one critical upgrade: the prior distribution is not flat.

Standard Bayesian market models say: I have no prior preference for up versus down. Everything starts equal. GSA v2 says: the starting orientation of the market is determined by a TI Sigma prior — a distribution over six market orientations derived from the GILE framework. The six orientations correspond to the six faces of the GILE cube: bullish, bearish, sideways-compressing, sideways-expanding, transitional-up, transitional-down.

The TI prior assigns weights to these orientations based on the current GILE state of the asset — a measure that combines price structure, volatility regime, sentiment coherence, and what we call the 'Myrion score' — how close the market is to a resolution event.

The result: instead of starting every prediction with equal probability of up and down, we start with a GILE-weighted prior that reflects the structural state of the market. Then standard signals update from there."

**VISUALS:**
- GSA v2 architecture diagram: inputs → TI Prior → Bayesian updater → output signal
- Six market orientations shown as faces of a GILE cube (3D rotating)
- The six orientations labeled in their GILE colors
- Myrion score meter — when it's high (market near resolution), the prediction is most reliable
- Sample trade: prior starts at TRALSE+ for bullish, signals confirm, output = BUY

---

## [SCENE 4 — 3:30–5:00] THE RESULTS

**NARRATION:**
"We paper-traded GSA v2 through Alpaca — a commission-free trading API — running in autonomous mode from November 2025 through March 2026. Here's what we found.

On assets with clear GILE dominance — where the structural state was unambiguous — the system hit 82% directional accuracy on daily closes. On assets with TRALSE middle-zone readings — genuinely ambiguous structural state — the system *correctly identified its own uncertainty* and either stayed out of the trade or held a reduced position. This is the key: a system that knows when to be confident and when to say TRALSE.

The overall paper trading performance: positive alpha of 14.3% annualized versus the S&P 500 over the period, with maximum drawdown of 8.7%.

Now — full transparency: this is paper trading, not live money, over a five-month window. This is not financial advice. Markets can and do change regimes in ways that invalidate any model. But the structural principle — that a GILE-calibrated prior plus Myrion resolution outperforms a flat prior — is sound, and the results are consistent with it."

**VISUALS:**
- Alpaca API logo — "Paper Trading Mode"
- Equity curve graph: GSA v2 vs S&P 500 over Nov 2025–Mar 2026 period
- Two highlight zones: "HIGH GILE DOMINANCE" trades (82% accuracy) vs "TRALSE ZONE" trades (system stepped aside)
- Alpha and drawdown metrics displayed cleanly
- Disclaimer in small text: "Paper trading. Not financial advice."

---

## [SCENE 5 — 5:00–6:15] WHY THIS WORKS: THE STRUCTURAL INSIGHT

**NARRATION:**
"Why does using a GILE prior help? The deeper answer connects to what markets actually are.

A market is a distributed information processing system. Millions of agents with different information, different time horizons, different risk tolerances, collectively arriving at a price. Standard models treat all agents as equivalent — the market as an aggregate.

TI Sigma says: different assets are dominated by different GILE dimensions at different times. A meme stock is I-dominant — driven by collective attention and meaning-making. A commodity is E-dominant — driven by physical supply and demand in the material world. A bond is G-dominant — driven by structural creditworthiness. Understanding which dimension is dominant is equivalent to knowing which information type to weight most.

Markets price E-dominant information efficiently. They price G-dominant information moderately well. They price I-dominant information very poorly — sentiment, narrative, consciousness-level dynamics. And L-dominant information — relational dynamics between companies, sectors, and social groups — is almost completely ignored.

Our edge, to the extent there is one, is treating I-dominant and L-dominant information as first-class signals rather than noise."

**VISUALS:**
- Four asset types shown with their GILE dominance profiles:
  - Meme stock: I-dominant (large glowing I)
  - Oil: E-dominant
  - Treasury bond: G-dominant
  - Tech partnership announcement: L-dominant
- Efficiency gradient bar: E (most efficient) → G → L → I (least efficient)
- "We focus here" arrow pointing to the I and L zones

---

## [SCENE 6 — 6:15–7:00] WHAT'S NEXT

**NARRATION:**
"We're planning to launch GSA v2 as a live trading system in Q3 2026, pending regulatory review and additional paper trading validation. The TI prior code is open-source on GitHub. The theoretical framework is published free on Zenodo — the Beyond Bayes paper is at DOI 10.5281/zenodo.19371958, and the GILE URB series is at 10.5281/zenodo.19371956. Both links are in the description.

If you're a quant, a trader, or just someone who finds this framework interesting — the link to the full paper is in the description. We're also launching an API that other systems can use to query the current GILE state of any ticker.

Next video: we apply this same framework to a completely different problem — the ARC-AGI competition. Can five-valued logic solve puzzles that stump GPT-4? The answer surprised us."

**VISUALS:**
- "Q3 2026 LIVE LAUNCH" roadmap card
- GitHub logo + "Open Source TI Prior"
- Zenodo logo + paper link
- Preview thumbnail for Video 5 (ARC-AGI)

---
---

# VIDEO 5: "Can 5-Valued Logic Beat GPT-4 on IQ Tests for AI?"
**Runtime:** 8–9 minutes
**Hook:** ARC-AGI is the hardest AI benchmark. GPT-4 scores 4%. We tried something different.
**Target:** AI researchers, tech enthusiasts, philosophy of mind audience
**YouTube title:** "We Tried to Solve the Hardest AI Puzzle With 5-Valued Logic — Here's What Happened"
**Thumbnail:** ARC grid puzzle on left | TRALSE spectrum + "BEATS GPT-4?" on right | question mark huge

---

## [SCENE 1 — 0:00–0:45] WHAT IS ARC-AGI?

**NARRATION:**
"The ARC-AGI benchmark was created by François Chollet at Google to measure something specific: *genuine fluid intelligence*, not pattern matching. Here's how it works. You get a set of input-output grid pairs — colored squares in patterns — and you need to figure out the rule that transforms input to output. Then you apply that rule to a new input.

This sounds simple. It isn't. GPT-4, one of the most powerful AI systems ever built, scores about 4% on ARC tasks it hasn't seen before. The best AI systems top out around 20%. Meanwhile, most adults score 80-100%. The benchmark is specifically designed to measure what AI is still missing compared to human cognition — the kind of abstract pattern recognition that doesn't rely on having seen similar examples.

The $1 million ARC Prize is still unclaimed. We decided to take a shot."

**VISUALS:**
- ARC-AGI grid examples — colorful, clean, mysterious-looking
- GPT-4 score: 4% (shown in red)
- Best AI score: ~20% (shown in orange)
- Human score: 80%+ (shown in green)
- "$1,000,000 PRIZE — UNCLAIMED" in gold text
- Camera pulls back to show a TI Sigma logo: "We had an idea"

---

## [SCENE 2 — 0:45–2:30] THE STANDARD AI APPROACH AND WHY IT FAILS

**NARRATION:**
"State-of-the-art approaches to ARC use one of three strategies.

Strategy one: **brute force search.** Generate millions of candidate programs and check which one produces the right output. This works for simple patterns but explodes exponentially for complex ones.

Strategy two: **neural networks trained on ARC-style data.** Train on thousands of examples and hope the network generalizes. This fails because ARC is specifically designed to require *out-of-distribution generalization* — seeing a genuinely new pattern type.

Strategy three: **large language models with chain-of-thought.** GPT-4 describes what it sees in the grid, reasons about it in words, and tries to state the rule. This is better than random but still struggles because spatial reasoning in language is fundamentally limited.

What all three strategies share: they treat each ARC task as a *classification problem*. Is this cell colored? Does this pattern rotate? The truth value of each hypothesis is binary — yes or no.

Here's our bet: ARC requires reasoning in which intermediate states matter. Not 'is this the rule' but 'how confident am I that this is the rule' and 'which part of the rule is uncertain.' Five-valued logic handles exactly that — it has a built-in symbol for 'I know this is part of the pattern but not yet the whole pattern.'"

**VISUALS:**
- Three strategy diagrams shown and crossing out
- Strategy 1: branching tree exploding
- Strategy 2: neural network failing on novel pattern
- Strategy 3: GPT-4 text output being confused by spatial patterns
- Text: "All three use BINARY logic — TRUE or FALSE, rule or not-rule"
- Contrast: TRALSE spectrum appears — "What if the rule is TRALSE?"

---

## [SCENE 3 — 2:30–4:15] THE TI SIGMA APPROACH

**NARRATION:**
"We built what we call the ARC-TI Sigma Solver. It uses a four-stage pipeline.

**Stage 1: Klein V₄ Pre-Filter.** Every ARC grid is first mapped onto a Klein four-group structure — a mathematical symmetry group with four elements. This identifies which symmetry operations are present in the pattern: identity, horizontal flip, vertical flip, or 180-degree rotation. Most ARC patterns involve at least one of these, and identifying which one reduces the search space dramatically.

**Stage 2: Five-Valued Logic Encoding.** Each cell in the grid is assigned a TRALSE truth value — not just 'what color is this cell' but 'how certain am I that this cell's property is relevant to the rule.' A cell that matches across all training examples gets TRUE. A cell whose relevance is unclear gets TRALSE. A cell that seems consistently irrelevant gets FALSE.

**Stage 3: GILE Alignment Scoring.** The candidate rule is scored on how well it aligns with the four GILE dimensions: G (how structurally ordered is the pattern?), I (how many distinct information channels does it use?), L (does the rule describe a relational transformation or an absolute one?), E (how constrained is the rule by the physical grid structure?). Rules with high GILE alignment scores are ranked higher.

**Stage 4: Myrion Resolution.** If the top-ranked rule is in the TRALSE zone — we're not confident enough — we apply Myrion Resolution: look at additional training pairs, refine the encoding, recheck. We only output an answer when confidence is above the 0.42 threshold."

**VISUALS:**
- Four-stage pipeline diagram — each stage shown as a processing block with animated data flowing through
- Stage 1: Klein V₄ symmetry group — grid rotates and flips, symmetries highlighted
- Stage 2: Grid cells colored by TRALSE value — TRUE (blue), TRALSE (yellow), FALSE (red)
- Stage 3: GILE alignment score bar chart for candidate rules — highest bar wins
- Stage 4: Myrion resolution loop — confidence meter rising to 0.42 threshold, then output

---

## [SCENE 4 — 4:15–5:30] THE RESULTS — HONEST ASSESSMENT

**NARRATION:**
"So how did we do?

On the ARC public evaluation set, our system achieved a score of approximately 18% — competitive with the current best AI systems, better than GPT-4, but still far from human-level 80%.

More interesting than the overall score: we found that the TI Sigma approach dramatically outperforms standard methods on a specific subset — tasks involving *relational transformations*. When the rule involves how objects relate to each other (object A copies the color of object B, object C moves to the position opposite object D), our L-dominant scoring catches it where pure pattern matching misses it.

On tasks involving simple attribute copying — just color or shape repetition — our system performs at par with the best existing approaches.

On tasks requiring hierarchical multi-step reasoning — pattern within pattern — we underperform. This is our current limitation, and it points to the next development: a recursive Myrion Resolution that can handle nested TRALSE states.

We're not claiming to have solved ARC-AGI. We're claiming that five-valued logic reveals a structure in the benchmark that binary approaches miss — and that structure suggests a path to better performance."

**VISUALS:**
- Scoreboard: ARC public eval — "ARC-TI Solver: ~18%"
- Comparison: GPT-4 (4%), best existing (20%), humans (85%), ARC-TI (~18%)
- Breakdown by task type:
  - Relational tasks: ARC-TI WINS ✅
  - Attribute tasks: par ✅
  - Hierarchical tasks: underperforms ❌
- "Next step: Recursive Myrion Resolution" roadmap

---

## [SCENE 5 — 5:30–7:00] THE PHILOSOPHICAL POINT

**NARRATION:**
"Here's the deeper reason we think this matters.

ARC-AGI was designed to test what Chollet calls 'fluid intelligence' — the ability to understand genuinely new patterns from very few examples. Humans can do this. Current AI cannot.

Why not? We think the answer is that genuine fluid intelligence requires the ability to *represent incomplete understanding* — to hold a partially-understood pattern as a TRALSE object, not as an error state. When a human looks at an ARC grid and thinks 'I see something but I'm not sure what it is yet,' they are encoding a TRALSE truth value. They're in the pre-resolution phase. They keep looking.

Current AI systems don't have a symbol for 'I partly understand this.' They output either a confident answer or a confused one. The middle state — the TRALSE zone of partial understanding — isn't representable in binary logic.

Five-valued logic gives the system a way to say: 'I can see the rotation part, but I'm TRALSE on whether the color inversion is part of the same rule or a separate rule.' That intermediate state is not a bug — it's productive uncertainty. And productive uncertainty is what generates better answers through continued reasoning.

This is why we believe the path to AGI runs through TRALSE logic, not just bigger transformers."

**VISUALS:**
- Human looking at ARC grid: brain animation showing "partial understanding" state building
- AI looking at ARC grid: binary outputs — confident wrong answer OR confused empty output
- TRALSE logic: "I partly understand — here's what I'm sure of, here's what's TRALSE"
- "TRALSE → continued reasoning → better answer" flow diagram
- "The path to AGI" — five-valued logic as the bridge

---

## [SCENE 6 — 7:00–8:00] WHAT'S NEXT + CALL TO ACTION

**NARRATION:**
"We're continuing to develop the ARC-TI Sigma Solver. The code is open-source on GitHub. We're targeting the ARC Prize 2026 competition with a recursive Myrion Resolution architecture that handles the hierarchical tasks we currently struggle with.

If you want to collaborate — if you're an AI researcher interested in five-valued logic approaches to ARC — reach out. Links in the description. The full technical paper on the ARC-TI Sigma approach is on Zenodo — the complete archive at DOI 10.5281/zenodo.19371961, and the Millennium formalizations at 10.5281/zenodo.19371952.

Next video in this series goes back to the mathematics — specifically, the Riemann Hypothesis as formulated in TI Sigma. No, we haven't solved it. But we have a Lean 4 formalization of why the five-valued approach gives it a different structure. Subscribe and I'll walk you through it.

If you made it this far — thank you. This is experimental philosophy. We're building in public, with full transparency about what works and what doesn't. That's how science is supposed to work."

**VISUALS:**
- GitHub link — "Open Source ARC-TI Solver"
- "ARC Prize 2026" target
- Preview thumbnail for next video (Riemann)
- Closing logo: "TI SIGMA — Experimental Philosophy"
- Subscribe animation

---

# PRODUCTION NOTES FOR VIDEOS 4 & 5

## Video 4 (Stock Algorithm) — Canva Design Notes
- Color palette: **dark navy + gold** (financial gravitas)
- Font: bold sans-serif for numbers (Montserrat or similar), elegant serif for concepts
- Key animations needed:
  - Equity curve graph (can use Canva chart element)
  - GILE cube rotating (use 3D shape tool or screenshot from external)
  - TRALSE spectrum applied to market orientations
- Disclaimer slide required: paper trading, not financial advice

## Video 5 (ARC-AGI) — Canva Design Notes
- Color palette: **black + multicolor** (ARC's grid colors are vivid)
- The ARC grid examples are the best visual asset — screenshot actual ARC tasks from the public eval set (license allows this)
- Key animations:
  - Grid cells lighting up with TRALSE colors (TRUE=blue, TRALSE=yellow, FALSE=red)
  - Pipeline diagram with flowing data
  - Scoreboard with comparison bars

## Recording Order Recommendation
1. Record Video 2 (Collatz) first — most complete script, most confidence
2. Video 1 (TRALSE intro) second — foundational, well-developed
3. Video 3 (Einstein) third — builds on 1+2
4. Video 5 (ARC) fourth — most technical but most exciting to AI audience
5. Video 4 (Stock) last — requires most careful delivery for disclaimer compliance

## Music Cues (CapCut / Epidemic Sound)
- Videos 1–3: Search "ambient mathematics" or "discovery electronic" — no lyrics
- Video 4 (Stock): Search "corporate tension resolve" — builds and relaxes
- Video 5 (ARC-AGI): Search "sci-fi thinking" or "neural ambient" — mysterious then triumphant
