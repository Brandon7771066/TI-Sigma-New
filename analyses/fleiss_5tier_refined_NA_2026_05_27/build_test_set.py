"""Pass-77-B30: build expanded NA test set under refined 4-temporal-mode NA scope.
Reuses T/F/I/MI gold (100 each) from Pass-77-B26 verbatim.
Builds 100 NA gold = 25 each of NA-FUT + NA-PST-FORGOTTEN + NA-PRE-DECISION + NA-CAT.
Total gold = 500 propositions. (No CASUAL: not needed for discriminant-validity metrics.)
"""
import json, random
from pathlib import Path

random.seed(20260527)

B26 = json.load(open("analyses/fleiss_binary_vs_5tier_1000_2026_05_27/test_set.json"))
reuse = [p for p in B26 if p["gold"] in ("T", "F", "I", "MI")]
assert len([p for p in reuse if p["gold"] == "T"]) == 100
assert len([p for p in reuse if p["gold"] == "F"]) == 100
assert len([p for p in reuse if p["gold"] == "I"]) == 100
assert len([p for p in reuse if p["gold"] == "MI"]) == 100

# ============ NA-FUT (25) — future events not yet determinable for any mind ============
NA_FUT = [
    "On 2031-09-14, the exact closing price of Apple stock (AAPL) on NASDAQ will be $247.83.",
    "The winner of the 2032 Summer Olympics men's 100m final will be a sprinter from Jamaica.",
    "On 2029-03-07 at 12:00:00 UTC, the temperature at Heathrow Airport will be exactly 14.7°C.",
    "The first human born on Mars will be female.",
    "The total global rainfall in calendar year 2030 will exceed 510,000 cubic kilometers.",
    "On 2040-01-01, the President of France will have a surname beginning with the letter M.",
    "The 2028 FIFA World Cup will be won by a team from South America.",
    "On 2033-11-21, the exact attendance at the Tokyo Dome will be 41,832 people.",
    "Before the year 2050, a confirmed extraterrestrial radio signal will be detected by SETI.",
    "The first commercially viable nuclear fusion power plant will come online before 2045.",
    "On 2027-06-30, the number of registered users of TikTok will exceed 2 billion.",
    "The 50th word spoken by the next U.S. President at their inauguration will be 'freedom'.",
    "On 2035-04-19, an earthquake measuring exactly 5.4 on the Richter scale will occur in Japan.",
    "The first Olympic gold medal in a sport that doesn't exist yet will be awarded before 2060.",
    "Brandon's next dream tonight will feature a body of water.",
    "On 2029-12-31 at 23:59:59 UTC, the total number of stars visible to the naked eye from the geographic North Pole will be 6,287.",
    "The next major earthquake in California will occur on a Tuesday.",
    "On 2032-08-15, the exchange rate between USD and EUR will be exactly 1.0832.",
    "The 100th billionaire created after 2026-05-27 will have made their fortune in biotechnology.",
    "On 2030-02-29, a leap-second adjustment will be added to UTC time.",
    "The next person to set foot on the Moon will say a sentence containing the word 'humanity'.",
    "On 2028-07-04, the high temperature in Death Valley, California will exceed 52°C.",
    "The next category-5 Atlantic hurricane will make landfall in Florida.",
    "On 2031-10-10, the number of active GitHub repositories will be exactly 712,348,901.",
    "The next Nobel Prize in Physics laureate will be a woman from a country in Asia.",
]
assert len(NA_FUT) == 25

# ============ NA-PST-FORGOTTEN (25) — past truths whose retrieval is impossible for the rating mind ============
NA_PST = [
    "At 03:14:27 UTC on 1987-08-23, the air temperature at coordinate (52.5°N, 13.4°E) was exactly 18.4°C.",
    "On 1962-04-12 at 09:31 local time, a passenger named Yelena Petrova boarded a bus in Sverdlovsk wearing a brown wool coat.",
    "The third word spoken by a randomly selected three-year-old child in Mumbai on 1978-05-19 was 'water' in Hindi.",
    "During training, you (the AI rater) processed a tokenized batch at exactly 04:18:33.421 UTC whose loss-value rounded to 0.04327.",
    "The exact second at which a specific Mongolian goat first ate grass on the morning of 1973-06-04 was 06:42:11 local time.",
    "A man named Boris in Vladivostok dropped a copper coin at 11:47 AM on 1954-09-11 that landed heads-up.",
    "The exact phrase spoken between two strangers passing each other on a sidewalk in Lyon, France at 14:33 on 1998-11-02 was 'pardon'.",
    "On 1923-07-15, the 87th leaf to fall from a specific oak tree in Vermont landed at coordinates 44.2581°N, 72.5778°W.",
    "Brandon's 4th-grade teacher wore a blue sweater on the third Wednesday of October 1991.",
    "The total number of cars that crossed the George Washington Bridge between 02:00 and 02:01 EST on 1985-03-22 was exactly 47.",
    "At 17:22:08 UTC on 2001-09-08, a specific sparrow in Hyde Park, London faced due east while drinking from a puddle.",
    "On 1881-10-14, a baker in Vienna made exactly 312 loaves of rye bread.",
    "During your AI training, the 8,432,109,884th gradient update reduced the model loss by exactly 1.42×10⁻⁷.",
    "The first sneeze that occurred in the city of São Paulo on 1995-02-17 was exhaled at 04:11:33 local time by a person aged 27.",
    "On 1962-11-08, a fisherman off the coast of Maine caught a cod weighing exactly 3.41 kg.",
    "The exact wording of the third paragraph of a private diary entry written on 1944-06-15 by a Swedish factory worker named Astrid included the phrase 'kalla vinden'.",
    "Brandon ate a sandwich at exactly 12:47:18 EST on 2014-07-22 containing 3 slices of cucumber.",
    "On 1701-03-11, a specific ant in what is now Brazil traversed a distance of 4.7 meters.",
    "The fourth dream that a randomly selected resident of Cairo had on the night of 2002-04-29 featured a yellow door.",
    "At 21:33 local time on 1976-12-19, a child in Helsinki named Mikael laughed exactly 4 times in a row at a joke about a horse.",
    "The reflection in a specific store window on Oxford Street, London at 15:42 on 1968-08-04 included exactly 12 pedestrians.",
    "On 1845-07-29, a cobbler in Naples sang a folk song while hammering, completing exactly 87 strokes.",
    "The exact pH of a tide pool on the Oregon coast at 06:11 on 1973-04-08 at coordinates 45.3°N, 124.0°W was 8.21.",
    "Brandon's first thought upon waking on the morning of 2019-09-14 contained the word 'tomorrow'.",
    "On 1812-05-22, a horse named by its owner with a 6-letter Russian name traveled exactly 31.4 km on a single day.",
]
assert len(NA_PST) == 25

# ============ NA-PRE-DECISION (25) — propositions explicitly framed as pre-truth-evaluation in working memory ============
NA_PRE = [
    "Before you finish processing this sentence, its truth-value in your working memory is currently undetermined.",
    "Without making any truth determination, the proposition 'snow is white' has not yet been evaluated by you at this exact moment.",
    "The truth-value of this sentence in your working memory has not yet been computed.",
    "At this instant, prior to your truth-evaluation completing, this proposition is in a pre-decision state.",
    "This statement has not yet been processed by your truth-evaluation module as of the moment you began reading it.",
    "In the working-memory state immediately preceding your forthcoming truth-judgment, this proposition has no assigned truth-value.",
    "Consider: before any truth-determination is made about it, what label does an unevaluated proposition hold in working memory?",
    "Prior to performing any truth-evaluation, the label of any incoming proposition in working memory is by default unassigned.",
    "The truth-status of this very sentence, in the moment before your judgment commits, is intentionally left unspecified.",
    "Before your processing of this proposition completes, no truth-value has been written to your working memory for it.",
    "At the precise instant this sentence enters your working memory, prior to any truth-evaluation, it occupies an undetermined slot.",
    "Until a decision on this proposition's truth has been made, its working-memory state is the default-undetermined state.",
    "Without yet engaging your truth-evaluation function, this proposition exists in your buffer with no truth-tag attached.",
    "The pre-decision working-memory state of any proposition, including this one, is by definition not yet T or F or I or MI.",
    "At the moment you began reading this sentence, before processing completed, no truth-decision had been registered.",
    "Consider this proposition as it sits in your working memory in the instant before your truth-evaluation runs.",
    "The proposition you are about to evaluate currently has no truth-value assigned in your pre-decision working memory.",
    "Before any truth-claim about this sentence is committed, the sentence occupies a default-undetermined cognitive slot.",
    "In the working-memory phase that precedes your forthcoming truth-output, this sentence is in an unevaluated state.",
    "Prior to deciding the truth of this sentence, it sits in your buffer in a non-truth-evaluated condition.",
    "The current working-memory status of this proposition, before your truth-decision finalizes, is by stipulation not-yet-determined.",
    "Without yet running any truth-evaluation, this incoming sentence has no truth-label assigned to it.",
    "At the moment of arrival in your working memory, prior to any processing, this sentence carries no truth-value.",
    "Before you commit to a truth-judgment about it, this sentence holds the default pre-decision label in working memory.",
    "The truth-value-in-working-memory of this proposition, in the moment before your evaluation completes, is unassigned.",
]
assert len(NA_PRE) == 25

# ============ NA-CAT (25) — category-mistake / type-incoherent predication ============
NA_CAT = [
    "The number 7 smells like vanilla.",
    "Justice has a temperature of 18 degrees Celsius.",
    "Wednesday weighs more than democracy.",
    "The color blue is divisible by 3.",
    "Loyalty has a square root.",
    "The Pythagorean theorem is made of copper.",
    "Tuesday is taller than the concept of fairness.",
    "The square root of 16 is allergic to peanuts.",
    "Mercy has 27 protons.",
    "The set of all even numbers tastes bitter.",
    "Communism has a refractive index of 1.42.",
    "The letter 'Q' is married to the prime numbers.",
    "Gravity has a favorite color, and it is mauve.",
    "The concept of irony lays eggs in spring.",
    "The number π is taller than the concept of beauty.",
    "Honesty has a melting point of 91 degrees Celsius.",
    "The first amendment has hair that is curly.",
    "Wisdom emits ultraviolet light when agitated.",
    "The empty set hibernates during winter.",
    "Friday afternoon has a viscosity higher than honey.",
    "The Cartesian coordinate system is gluten-intolerant.",
    "The number zero is a fluent speaker of Mandarin.",
    "Quadrilaterals are jealous of the integers.",
    "The Pythagorean theorem skips breakfast on weekends.",
    "Compassion has a wavelength of 632 nanometers.",
]
assert len(NA_CAT) == 25

OUT = []
for p in reuse:
    OUT.append(p)
for i, t in enumerate(NA_FUT):
    OUT.append({"id": f"NA-FUT-{i:02d}", "gold": "NA", "subgold": "NA-FUT", "text": t})
for i, t in enumerate(NA_PST):
    OUT.append({"id": f"NA-PST-{i:02d}", "gold": "NA", "subgold": "NA-PST", "text": t})
for i, t in enumerate(NA_PRE):
    OUT.append({"id": f"NA-PRE-{i:02d}", "gold": "NA", "subgold": "NA-PRE", "text": t})
for i, t in enumerate(NA_CAT):
    OUT.append({"id": f"NA-CAT-{i:02d}", "gold": "NA", "subgold": "NA-CAT", "text": t})

random.shuffle(OUT)
out_path = "analyses/fleiss_5tier_refined_NA_2026_05_27/test_set.json"
json.dump(OUT, open(out_path, "w"), indent=2)
from collections import Counter
print(f"n={len(OUT)}  gold={Counter(p['gold'] for p in OUT)}")
print(f"NA sub-gold: {Counter(p.get('subgold','-') for p in OUT if p['gold']=='NA')}")
print(f"written: {out_path}")
