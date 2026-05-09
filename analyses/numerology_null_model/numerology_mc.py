"""
Pass 14 — Monte Carlo null model for Brandon's family-names numerology
cluster.

Tests Brandon's hypothesis: for each person in the family, at least one
of {first-name letter count, first-name phoneme count} (each reduced
mod 9 to {1..9} per standard numerology) matches one of the person's
T genuine archetype-traits.

Brandon's actual cluster:
  - Brandon: 7 letters, 7 phonemes, claimed-archetype 7 (wisdom/pattern)
  - Lisa:    4 letters, 4 phonemes, claimed-archetype 4 (structural)
  - Jeffrey: 7 letters, 5 phonemes; or Jeff: 4 letters, 3 phonemes;
             claimed-archetype 3 (structural action)
  - Gloria:  6 letters, 6 phonemes, claimed-archetype 6 (caregiver)
  - Ray:     3 letters, 2 phonemes, claimed-archetype 3 (communicator)

Null model: sample first-name letter counts from a realistic English
distribution; phoneme counts as letter_count - 1 with noise; archetypes
uniform in {1..9}; T = number of genuine archetype-traits per person.

Reports:
  - P(any single person matches | T)
  - P(all 5 match | T) for T in {2, 3}
  - P(at least 4 of 5 match | T) for T in {2, 3}
  - Comparison with the actual observed Brandon cluster

Deterministic seed 20260509.
"""
import numpy as np

np.random.seed(20260509)

N_TRIALS = 50_000
N_FAMILY = 5
ARCHETYPES = np.arange(1, 10)  # standard numerology 1..9


def reduce_to_digit_arr(arr):
    """Vectorized numerological reduction to {1..9}: ((n-1) % 9) + 1."""
    return ((arr - 1) % 9) + 1


def trial_vec(T, n_trials):
    """Vectorized: sample n_trials families, return per-trial match counts."""
    # Letter counts: 3..10 with realistic distribution
    letter_p = np.array([0.02, 0.10, 0.22, 0.28, 0.20, 0.10, 0.05, 0.03])
    letters = np.random.choice(np.arange(3, 11), size=(n_trials, N_FAMILY), p=letter_p)
    # Phonemes: letters + noise in {-2,-1,0}
    noise = np.random.choice([-2, -1, 0], size=(n_trials, N_FAMILY), p=[0.2, 0.5, 0.3])
    phonemes = np.maximum(2, letters + noise)
    L = reduce_to_digit_arr(letters)
    P = reduce_to_digit_arr(phonemes)
    # Sample T traits per person (no replacement within person)
    # Use random argpartition trick: random key per archetype, take T smallest
    keys = np.random.random((n_trials, N_FAMILY, 9))
    trait_idx = np.argpartition(keys, T, axis=2)[:, :, :T]  # indices 0..8
    traits = trait_idx + 1  # values 1..9
    # match per person if L or P in traits
    L_match = np.any(traits == L[:, :, None], axis=2)
    P_match = np.any(traits == P[:, :, None], axis=2)
    person_match = L_match | P_match
    return person_match.sum(axis=1)  # n_matches per family


print("=" * 70)
print("Pass 14 — Numerology family-names cluster — Monte Carlo null model")
print("=" * 70)
print(f"Trials per condition: N = {N_TRIALS:,}")
print(f"Family size: {N_FAMILY}")
print(f"Archetype space: {{1..9}}")
print(f"Match rule: name-letter-count OR name-phoneme-count (each reduced")
print(f"            to 1..9) is in the person's trait-archetype set.")
print()

# Per-person base rate (analytical)
print("## Analytical per-person match probability")
print("Under generous null: P(match) = 1 - [(9-T)/9]^|{L,P}|.")
print("With L != P typical for English first names (~85% of cases):")
for T in [1, 2, 3, 4]:
    p_distinct = 1 - ((9 - T) / 9) ** 2  # |{L,P}|=2
    p_same     = 1 - ((9 - T) / 9) ** 1  # |{L,P}|=1
    p_blend    = 0.85 * p_distinct + 0.15 * p_same
    print(f"  T={T}: P(person matches) ~ {p_blend:.3f}  (distinct={p_distinct:.3f}, same={p_same:.3f})")

print()

# Monte Carlo
print("## Monte Carlo (numerical) — joint family probabilities")
print(f"  {'T':>3} {'P(person)':>12} {'P(all 5)':>12} {'P(>=4 of 5)':>14} {'P(>=3 of 5)':>14}")
results = {}
for T in [1, 2, 3, 4]:
    counts = trial_vec(T, N_TRIALS)
    p_person = counts.mean() / N_FAMILY
    p_all5   = (counts == 5).mean()
    p_ge4    = (counts >= 4).mean()
    p_ge3    = (counts >= 3).mean()
    results[T] = (p_person, p_all5, p_ge4, p_ge3)
    print(f"  {T:>3} {p_person:>12.4f} {p_all5:>12.4f} {p_ge4:>14.4f} {p_ge3:>14.4f}")

print()

# Brandon's actual cluster: how many of his 5 family members are claimed matches?
print("## Brandon's actual family cluster (per BRANDON_BIOGRAPHY_MASTER_INDEX.md)")
brandon_family = [
    ("Brandon", 7, 7, 7),  # name, letters, phonemes, claimed archetype
    ("Lisa",    4, 4, 4),
    ("Jeff",    4, 3, 3),  # using nickname; Jeffrey/7-letters does NOT match the 3-claim
    ("Gloria",  6, 6, 6),
    ("Ray",     3, 2, 3),
]
print(f"  {'Name':>10} {'Lett':>5} {'Phon':>5} {'L%9':>5} {'P%9':>5} {'Claim':>6} {'Match':>7}")
n_match = 0
for name, L, P, claim in brandon_family:
    Lr = ((L - 1) % 9) + 1
    Pr = ((P - 1) % 9) + 1
    matches = (claim == Lr) or (claim == Pr)
    if matches: n_match += 1
    flag = "YES" if matches else "no"
    print(f"  {name:>10} {L:>5} {P:>5} {Lr:>5} {Pr:>5} {claim:>6} {flag:>7}")

print(f"\n  Observed: {n_match} of {N_FAMILY} family members match.")
if n_match == 5:
    print(f"  Under T=2 null: P(all 5 match by chance) = {results[2][1]:.4f}")
    print(f"  Under T=3 null: P(all 5 match by chance) = {results[3][1]:.4f}")
elif n_match >= 4:
    print(f"  Under T=2 null: P(>=4 of 5 match)        = {results[2][2]:.4f}")
    print(f"  Under T=3 null: P(>=4 of 5 match)        = {results[3][2]:.4f}")

print()
print("## Honest #69 verdicts")
print("  - Pre-registration would tighten this: pick the family list, the")
print("    archetype mapping, and the operationalization BEFORE looking.")
print("  - The Jeff vs Jeffrey choice is post-hoc selection (Jeffrey's 7/5")
print("    does NOT match the 3-claim; Jeff's 4/3 does).")
print("  - The matrilineal life-path-6 cascade (Mimi/Lisa/Brandon) is a")
print("    SEPARATE, tighter claim on birth-date numerology, not the name")
print("    phonetic claim. P(3 generations share life-path) ~ (1/9)^2 = 1.2%")
print("    under simplest null, but partially confounded by birth-date heritage.")
print("  - Recommendation: pre-register a PROSPECTIVE test on >=5 NEW people.")
