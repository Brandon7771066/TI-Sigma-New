# Pass-48 Architect Findings — Layman's Explanation (2026-05-13)

**What this is:** Plain-English explanation of why the architect (a code-review subagent) flagged 4 issues in the Pass-48 follow-up batch, and what we changed in response. No jargon.

---

## Finding 1 (CRITICAL — golden-ratio numerology) — "Don't claim a magic number is *the* answer when you only saw one example."

### What the architect saw
The LCC plan declared `C_EMERICK = 1/(φ√2) ≈ 0.4370` as a *constant of nature* — a fixed threshold derived from the golden ratio.

### Why that's a problem in plain English
The golden ratio (φ ≈ 1.618…) is famous for showing up in pinecones, sunflowers, and *every* numerology book ever written. If you fit one observation (here: an empirical value around 0.4370) to a closed-form expression involving φ, you'll almost always find *some* such expression that "matches" — because there are infinitely many simple φ-formulas that land near any given number. The fact that one of them matches doesn't mean it's the *real* explanation. Without (a) a derivation from first principles or (b) replication of the same constant on new, independent data, you're really just saying "I noticed a coincidence." Calling it `C_EMERICK` and treating it as a constant locks in a strong claim from very weak evidence.

### What we changed
We demoted `C_EMERICK` from "constant" to **"candidate threshold"**. The closed-form `1/(φ√2)` is now flagged "CONJECTURAL FIT pending Track C M5 first-principles derivation" — i.e., until we either prove it from theory or see it again in fresh data, we cite the empirical value (0.4370 ± its actual confidence interval) and we don't lean on the φ formula in any external communication. This is just intellectual honesty: don't sell the "magic" until you've earned it.

### Implication going forward
Any future paper that wants to use this threshold quotes the empirical number with its confidence interval. The φ story stays as a *conjecture* — interesting, possibly meaningful, currently unproven — until Track C delivers either a derivation or a second independent confirmation.

---

## Finding 2 (HIGH — too-narrow prediction window) — "If you can only win by hitting a tiny target, your test isn't really a test."

### What the architect saw
The D1 quantum-experiment pre-registration said: "We will count the result a CONFIRM if the measured Mermin value lands in the window 5.66 − 0.40 ± 0.05." That's a very narrow band.

### Why that's a problem in plain English
A pre-registration is a promise about what would *count as success* before you run the experiment. If the success window is tiny, two bad things happen:
1. **You probably miss it even if your theory is right.** Real-world quantum hardware has noise. A correct theory can still produce a result a few percent off the textbook prediction. Demanding hyper-precision in a noisy setting means even a *correct* theory looks wrong.
2. **It looks like cheating in reverse.** A suspiciously narrow window can be read as either over-confidence ("I know exactly what the answer will be") or as a contrived target ("I picked the narrow window because I knew the answer in advance"). Either reading hurts credibility.

The fix is to use a *directional* prediction: "We will count the result a CONFIRM if the measured value is *less than* X *and* the trend goes the predicted direction." Directional predictions are still falsifiable — if the result lands above X or trends the wrong way, the theory loses — but they don't require sniper-rifle precision.

### What we changed
The D1 pre-registration is now a directional inequality (`M < 5.40` AND positive slope = CONFIRM). We added a discriminator hierarchy so a near-miss is reported as WEAK rather than as a binary fail, and we kept the original narrow-band number as informational-only (post-hoc summary, not a pre-reg threshold).

### Implication going forward
This is now the standard form for all corpus pre-registrations involving real hardware. Point-predictions are reserved for theory-vs-theory comparisons where both sides are noiseless.

---

## Finding 3 (HIGH — IBM Quantum hardware access) — "Just because you ran on the fancy machine once doesn't mean you can run on it again."

### What the architect saw
The IBM Quantum experiments memo assumed continued access to `ibm_marrakesh` (a 156-qubit Heron-class machine) and `ibm_torino` for D1, D3, D4, D5.

### Why that's a problem in plain English
IBM Quantum has tiers. The free Open Plan gives you 10 minutes per month on older 127-qubit Eagle machines. The newer 156-qubit Heron machines (the ones that gave us the headline qc26 result) typically require either a paid Premium tier or membership in IBM Quantum Network — a partnership program. A standard credit-card Pay-As-You-Go account *might* reach Heron, but might not. We can't assume so just because one prior job succeeded; account access can change, partnerships expire, and the qc26 result might have been run under terms that no longer apply.

If we plan a Pass-49 batch assuming Heron access and then can't get on the machine, we waste planning time and risk making promises we can't keep.

### What we changed
We added a hardware-access caveat: *verify access by submitting a 1-shot trivial circuit before committing budget to Heron*. If Heron access is gone, we fall back to Eagle for D1, D4, D5 (accepting a reduced Mermin bound) and **defer D3 entirely** (it actually needs Heron's longer coherence times).

### Implication going forward
Every corpus claim involving real quantum hardware now needs a "where can we actually run this?" check before resources are committed. This is an operational discipline, not a theoretical one — but it's what separates a real research program from one that exists only on paper.

---

## Finding 4 (MEDIUM — Zenodo vs international patents contradiction) — "Publishing it for free *kills* your right to patent it overseas."

### What the architect saw
The patents memo recommended in §3 Phase 1: *"Mint Zenodo DOIs for [list including LCC-Virus, MI-detector, etc.]"* — but in §4 it warned that public disclosure destroys patent rights in Europe, Japan, and China, which have no grace period.

These two recommendations directly contradict each other on the same items.

### Why that's a problem in plain English
There are two different ways to protect intellectual property:
- **Defensive publication** (Zenodo): you publish the idea publicly so that nobody else can patent it later. Cost: $0. Cost-of-doing-it: you can no longer patent it yourself outside the US, because most countries treat *any* prior publication as a patent-disqualifier with no grace period.
- **Patent**: you keep the idea private until you file, then exchange disclosure for an exclusive monopoly. Cost: thousands of dollars per jurisdiction.

For most theory-level corpus items (truth labels, philosophical principles, framework papers), defensive publication is the right move — they're not patentable anyway, and Zenodo timestamps protect against someone else patenting derivatives.

For the *actual patent candidates* (LCC-Virus pipeline, MI-detector circuit, TJ-measurement instrument), defensive publication is **the wrong move**: it *permanently* destroys the EU/JP/CN patent rights you might want later. Once you've Zenodo'd it, it's done. Can't be un-published.

The original memo recommended defensive publication for *both* groups simultaneously, which would have wrecked the international patent option for the candidates.

### What we changed
Phase 1 defensive publication now **excludes** the 3 patent candidates. They go into controlled-disclosure (private repo, NDA-only) until either (a) a real commercial trigger fires and a US provisional gets filed first, or (b) Brandon affirmatively decides in writing to forgo international rights for those specific items.

### Implication going forward
Zenodo is a one-way door for international patent rights. The corpus needs explicit triage before *anything* goes to Zenodo: "Is this a patent candidate? If yes, hold; if no, publish." We added that checkpoint to the patents strategy.

---

## Bonus: Finding 5 (LOW — false positive)
The architect flagged that `papers/urb_659_dirac_equation_ti_sigma.md` was missing. It's not — the file exists; the architect just didn't see it in the reviewed file set. Verified pre-write. No action needed.

---

## Why this kind of review matters

Three of the four real findings were about **resisting the temptation to over-claim**: don't elevate one observation to a constant of nature (Finding 1); don't pretend you can predict noisy hardware to 4 decimal places (Finding 2); don't assume your future access is what your past access was (Finding 3); don't accidentally give up rights you might want later (Finding 4). None of them were about the science being *wrong*. They were about the *framing* being too confident for the evidence in hand. That's exactly the discipline #69 (asymmetric standards / brutal honesty) is supposed to enforce, and the architect caught what we missed.

All four findings are now corrected in the live papers. The originating memos are tagged with the architect-fix lines so any future reader sees the trail.
