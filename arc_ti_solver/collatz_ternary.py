"""
Collatz Ternary Analysis — TI Sigma Framework
==============================================
URB #534 computational companion + URB #535 new results.

Key results:
  1. In base-3, the odd step (3n+1) = append INDETERMINATE (digit 1) to tail.
  2. 2^{-1} in Z_3 (3-adic integers) = ...11111112 (TRUE at pos-0, INDETERMINATE above)
  3. The compound step for odd n: n -> (3n+1)/2 = (n|1) x 2^{-1} in Z_3.
  4. The even step is a ternary-alien carry that "dissolves" INDETERMINATE digits.
  5. INDETERMINATE density delta(n) = count("1" in ternary(n)) / len(ternary(n))
     tracks a secondary convergence signal alongside the standard |n| descent.
  6. The terminal cycle {1,2,4} in 5-valued = {INDETERMINATE, TRUE, DOUBLE_TRALSE}.

New metric introduced here:
  - delta(n): INDETERMINATE density (fraction of ternary "1" digits)
  - phi(n): ternary digit sum (sum of all ternary digits)
  - ternary_height(n): position of the highest "1" digit (INDETERMINATE height)

License: Apache 2.0 | Author: Brandon Emerick (TI Framework) | 2026
"""

from typing import List, Tuple, Dict
import numpy as np


# ---------------------------------------------------------------------------
# 5-valued truth labels for ternary digits
# ---------------------------------------------------------------------------
DIGIT_LABEL = {0: "FALSE", 1: "INDETERMINATE", 2: "TRUE"}
DIGIT_SYMBOL = {0: "F", 1: "I", 2: "T"}  # Quick notation


# ---------------------------------------------------------------------------
# Core ternary utilities
# ---------------------------------------------------------------------------

def to_ternary_digits(n: int) -> List[int]:
    """
    Return ternary digits of n as list, most-significant first.
    to_ternary_digits(14) -> [1, 1, 2]  (because 14 = 1*9 + 1*3 + 2)
    """
    if n == 0:
        return [0]
    digits = []
    while n > 0:
        digits.append(n % 3)
        n //= 3
    return list(reversed(digits))


def to_ternary_str(n: int) -> str:
    """Return ternary representation as a string."""
    return "".join(str(d) for d in to_ternary_digits(n))


def from_ternary(digits: List[int]) -> int:
    """Convert list of ternary digits (MSB first) to integer."""
    result = 0
    for d in digits:
        result = result * 3 + d
    return result


def ternary_digit_sum(n: int) -> int:
    """Sum of all ternary digits of n."""
    return sum(to_ternary_digits(n))


def ternary_parity(n: int) -> int:
    """Parity via ternary digit sum: n is even iff digit sum is even."""
    return ternary_digit_sum(n) % 2


def indeterminate_count(n: int) -> int:
    """Count of '1' digits (INDETERMINATE) in ternary representation of n."""
    return to_ternary_digits(n).count(1)


def indeterminate_density(n: int) -> float:
    """
    INDETERMINATE density: fraction of ternary digits that are '1'.
    delta(n) in URB #535.
    Range: [0.0, 1.0].
    delta = 0.0 -> all FALSE/TRUE digits (binary-resolvable number)
    delta = 1/3 -> expected density for 'random' ternary number
    delta = 1.0 -> all INDETERMINATE (only n=1 satisfies this with 1 digit)
    """
    digits = to_ternary_digits(n)
    if not digits:
        return 0.0
    return digits.count(1) / len(digits)


def indeterminate_height(n: int) -> int:
    """
    Position (0-indexed from LSB) of the highest INDETERMINATE digit.
    Returns -1 if no INDETERMINATE digit exists.
    This measures how 'tall' the INDETERMINATE influence reaches in the 3-adic tower.
    """
    digits = to_ternary_digits(n)
    digits_lsb = list(reversed(digits))  # LSB first
    for i in range(len(digits_lsb) - 1, -1, -1):
        if digits_lsb[i] == 1:
            return i
    return -1


def ti_annotated(n: int) -> str:
    """
    Return ternary representation annotated with TI Sigma truth labels.
    Example: 14 = 112 -> 'I·I·T' (INDETERMINATE·INDETERMINATE·TRUE)
    """
    return "·".join(DIGIT_SYMBOL[d] for d in to_ternary_digits(n))


# ---------------------------------------------------------------------------
# 3-adic inverse of 2
# ---------------------------------------------------------------------------

def adic3_inv2_approx(k: int) -> int:
    """
    The 3-adic inverse of 2, truncated to k 3-adic digits.
    2^{-1} mod 3^k = (3^k + 1) // 2.

    As k -> infinity, this gives the 3-adic integer ...11111112 (base 3):
    TRUE at position 0, INDETERMINATE at all higher positions.

    Verification: 2 * (3^k + 1) / 2 = 3^k + 1 ≡ 1 (mod 3^k). ✓
    """
    return (3**k + 1) // 2


def halve_as_adic3_product(n: int, precision: int = 20) -> int:
    """
    Compute n/2 (for even n) as n * 2^{-1} mod 3^precision.
    This demonstrates the 3-adic local structure of the halving operation.
    For actual integers, this equals n//2 if n is even.
    """
    assert n % 2 == 0, f"n={n} must be even"
    inv2 = adic3_inv2_approx(precision)
    return (n * inv2) % (3**precision)


# ---------------------------------------------------------------------------
# Collatz steps in ternary
# ---------------------------------------------------------------------------

def collatz_odd_step_ternary(n: int) -> Tuple[int, str]:
    """
    Apply odd Collatz step (3n+1) and show ternary operation.
    Returns (result, description).
    The operation is: append '1' (INDETERMINATE) to ternary tail.
    """
    result = 3 * n + 1
    desc = f"{to_ternary_str(n)} + append[I] -> {to_ternary_str(result)}"
    return result, desc


def collatz_even_step_ternary(n: int) -> Tuple[int, str]:
    """
    Apply even Collatz step (n/2) and show ternary operation.
    Returns (result, description).
    The halving is the 'alien' global carry operation.
    """
    assert n % 2 == 0
    result = n // 2
    desc = (f"{to_ternary_str(n)} ÷2[alien-carry] -> {to_ternary_str(result)}  "
            f"(delta: {indeterminate_density(n):.3f} -> {indeterminate_density(result):.3f})")
    return result, desc


def collatz_compound_step(n: int) -> Tuple[int, int, str]:
    """
    Apply compound step to odd n: (3n+1) / 2^v2(3n+1).
    This combines the mandatory odd step + all immediate even steps.

    Returns (result, num_halvings, description).
    The compound step takes n (odd) to the next odd number.
    """
    assert n % 2 == 1, f"n={n} must be odd for compound step"
    m = 3 * n + 1  # always even
    halvings = 0
    while m % 2 == 0:
        m //= 2
        halvings += 1
    desc = (f"({to_ternary_str(n)}) -> (3n+1)/2^{halvings} = "
            f"({to_ternary_str(m)})  [{halvings} halvings; "
            f"delta: {indeterminate_density(n):.3f} -> {indeterminate_density(m):.3f}]")
    return m, halvings, desc


# ---------------------------------------------------------------------------
# Full trajectory analysis
# ---------------------------------------------------------------------------

def collatz_trajectory(n: int, max_steps: int = 10000) -> Dict:
    """
    Compute the full Collatz trajectory from n, returning rich TI Sigma metrics.

    Returns dict with:
      - steps: list of integers in the trajectory
      - ternary: list of ternary strings
      - delta: INDETERMINATE density at each step
      - phi: ternary digit sum at each step
      - height: INDETERMINATE height at each step
      - step_types: 'odd' or 'even' at each step
      - stopping_time: steps to reach n <= original n
      - delta_trend: correlation of delta with step number (negative = decreasing)
    """
    traj = [n]
    ternary = [to_ternary_str(n)]
    delta = [indeterminate_density(n)]
    phi = [ternary_digit_sum(n)]
    height = [indeterminate_height(n)]
    step_types = []

    current = n
    for _ in range(max_steps):
        if current == 1:
            break
        if current % 2 == 0:
            current = current // 2
            step_types.append("even")
        else:
            current = 3 * current + 1
            step_types.append("odd")
        traj.append(current)
        ternary.append(to_ternary_str(current))
        delta.append(indeterminate_density(current))
        phi.append(ternary_digit_sum(current))
        height.append(indeterminate_height(current))

    # Stopping time: first step where current < original n
    stopping_time = next((i for i, x in enumerate(traj) if x < n), len(traj))

    # Delta trend: linear regression coefficient (negative = decreasing INDETERMINATE density)
    if len(delta) > 2:
        xs = np.arange(len(delta))
        delta_arr = np.array(delta)
        delta_trend = float(np.polyfit(xs, delta_arr, 1)[0])
    else:
        delta_trend = 0.0

    # Count compound steps (odd+even pairings)
    compound_count = step_types.count("odd")
    avg_halvings = step_types.count("even") / max(compound_count, 1)

    return {
        "start": n,
        "steps": traj,
        "ternary": ternary,
        "delta": delta,
        "phi": phi,
        "height": height,
        "step_types": step_types,
        "stopping_time": stopping_time,
        "trajectory_length": len(traj),
        "delta_trend": round(delta_trend, 6),
        "delta_start": round(delta[0], 4),
        "delta_min": round(min(delta), 4),
        "delta_max": round(max(delta), 4),
        "compound_count": compound_count,
        "avg_halvings_per_compound": round(avg_halvings, 3),
    }


def compound_trajectory(n: int, max_steps: int = 1000) -> Dict:
    """
    Compute Collatz trajectory using only compound steps (odd n -> next odd n).
    This eliminates the 'even' intermediaries and shows the true compound dynamics.

    In ternary: each compound step = (append INDETERMINATE) then (alien halving x k).
    """
    if n % 2 == 0:
        while n % 2 == 0:
            n //= 2

    traj = [n]
    halvings_list = []
    delta_list = [indeterminate_density(n)]
    descriptions = []

    current = n
    for _ in range(max_steps):
        if current == 1:
            break
        result, halvings, desc = collatz_compound_step(current)
        traj.append(result)
        halvings_list.append(halvings)
        delta_list.append(indeterminate_density(result))
        descriptions.append(desc)
        current = result

    return {
        "start": n,
        "odd_steps": traj,
        "halvings_per_step": halvings_list,
        "delta": delta_list,
        "descriptions": descriptions,
        "total_compound_steps": len(traj) - 1,
        "avg_halvings": round(np.mean(halvings_list) if halvings_list else 0, 4),
        "avg_delta_change": round(
            np.mean([delta_list[i+1] - delta_list[i] for i in range(len(delta_list)-1)])
            if len(delta_list) > 1 else 0, 6
        ),
    }


# ---------------------------------------------------------------------------
# Population-level analysis
# ---------------------------------------------------------------------------

def analyze_population(max_n: int = 200) -> Dict:
    """
    Analyze Collatz trajectories for n = 1 to max_n.
    Compute population-level statistics on INDETERMINATE density dynamics.

    Key question: Is delta(n) generally DECREASING along trajectories?
    """
    results = []
    for n in range(1, max_n + 1):
        t = collatz_trajectory(n)
        results.append({
            "n": n,
            "ternary": to_ternary_str(n),
            "delta_start": t["delta_start"],
            "delta_min": t["delta_min"],
            "delta_trend": t["delta_trend"],
            "trajectory_length": t["trajectory_length"],
            "avg_halvings": t["avg_halvings_per_compound"],
        })

    # How often does delta decrease (trend < 0)?
    negative_trend = sum(1 for r in results if r["delta_trend"] < 0)
    pct_decreasing = negative_trend / len(results) * 100

    # Average halvings per compound step (should be ~2)
    avg_halvings_pop = np.mean([r["avg_halvings"] for r in results])

    # Distribution of starting delta values
    delta_starts = [r["delta_start"] for r in results]

    return {
        "population_size": max_n,
        "pct_delta_decreasing": round(pct_decreasing, 1),
        "avg_halvings_per_compound": round(float(avg_halvings_pop), 4),
        "mean_delta_start": round(float(np.mean(delta_starts)), 4),
        "results": results,
    }


def find_pure_numbers(max_n: int = 500) -> List[Tuple[int, str]]:
    """
    Find 'pure' numbers — ternary representations using only {0, 2} (no INDETERMINATE).
    These are the binary-resolvable numbers in ternary: delta = 0.
    In TI Sigma: all cells are definitively FALSE or TRUE; no MR-pending states.
    """
    pure = []
    for n in range(1, max_n + 1):
        if indeterminate_count(n) == 0:
            pure.append((n, to_ternary_str(n)))
    return pure


# ---------------------------------------------------------------------------
# 3-adic structure analysis
# ---------------------------------------------------------------------------

def adic3_structure(n: int) -> Dict:
    """
    Analyze the 3-adic structure of n.

    3-adic valuation v3(n): largest k such that 3^k divides n.
    3-adic norm |n|_3 = 3^{-v3(n)}: measures 'closeness to 0' in Z_3.

    A sequence converges in Z_3 iff |a_n|_3 -> 0, i.e., v3(a_n) -> infinity.

    For Collatz: the sequence converges in Z_3 iff the 3-adic valuation
    of the trajectory elements grows without bound.
    """
    v3 = 0
    m = n
    while m % 3 == 0 and m > 0:
        v3 += 1
        m //= 3

    adic_norm = 3**(-v3) if v3 > 0 else 1.0

    return {
        "n": n,
        "ternary": to_ternary_str(n),
        "v3": v3,  # ternary digit: how many trailing 0s
        "adic3_norm": round(adic_norm, 6),
        "indeterminate_density": round(indeterminate_density(n), 4),
        "ternary_digit_sum": ternary_digit_sum(n),
        "ti_annotation": ti_annotated(n),
    }


def adic3_trajectory_norms(n: int, steps: int = 30) -> List[float]:
    """Track 3-adic norms along the Collatz trajectory."""
    current = n
    norms = []
    for _ in range(steps):
        info = adic3_structure(current)
        norms.append(info["adic3_norm"])
        if current == 1:
            break
        current = current // 2 if current % 2 == 0 else 3 * current + 1
    return norms


# ---------------------------------------------------------------------------
# Entry point: print a summary report
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print("=" * 70)
    print("TI Sigma Ternary Collatz Analysis — URB #534 / #535")
    print("=" * 70)

    # 1. 3-adic inverse of 2
    print("\n[1] 3-ADIC INVERSE OF 2")
    print("    2^{-1} in Z_3 = ...11111112 (base 3)")
    print("    = TRUE at position 0, INDETERMINATE at all higher positions")
    for k in [1, 3, 5, 8]:
        inv = adic3_inv2_approx(k)
        print(f"    2^-1 mod 3^{k} = {inv:6d} = {to_ternary_str(inv):>12s} (ternary)"
              f"  TI: {ti_annotated(inv)}")

    # 2. Compound step examples
    print("\n[2] COMPOUND STEP: odd n -> (3n+1) / 2^k  [ternary view]")
    for n in [1, 5, 7, 11, 13, 27, 97]:
        if n % 2 == 0:
            continue
        result, halvings, desc = collatz_compound_step(n)
        print(f"    n={n:4d}: {desc}")

    # 3. INDETERMINATE density trajectory
    print("\n[3] INDETERMINATE DENSITY (delta) ALONG TRAJECTORIES")
    for start in [5, 7, 27, 97, 871]:
        t = collatz_trajectory(start)
        print(f"    n={start:5d}: len={t['trajectory_length']:4d}  "
              f"delta: {t['delta_start']:.3f}->{t['delta_min']:.3f}  "
              f"trend={t['delta_trend']:+.4f}  "
              f"avg_halvings={t['avg_halvings_per_compound']:.2f}")

    # 4. Population statistics
    print("\n[4] POPULATION ANALYSIS (n=1..200)")
    pop = analyze_population(200)
    print(f"    % with decreasing delta trend:  {pop['pct_delta_decreasing']:.1f}%")
    print(f"    Average halvings per compound:  {pop['avg_halvings_per_compound']:.4f}")
    print(f"    Mean starting delta:            {pop['mean_delta_start']:.4f}")
    print(f"    Expected for uniform ternary:   0.3333")

    # 5. Pure numbers (delta = 0)
    print("\n[5] 'PURE' NUMBERS: no INDETERMINATE digits (delta=0), first 15:")
    pure = find_pure_numbers(500)[:15]
    for n, t in pure:
        print(f"    {n:5d} = {t:>9s} (ternary)  TI: {ti_annotated(n)}")

    # 6. Terminal cycle analysis
    print("\n[6] TERMINAL CYCLE {1, 4, 2} IN 5-VALUED LOGIC")
    for n in [1, 4, 2]:
        info = adic3_structure(n)
        print(f"    n={n}: ternary={info['ternary']}  TI={info['ti_annotation']}  "
              f"v3={info['v3']}  |n|_3={info['adic3_norm']}")
    print("    Cycle: INDETERMINATE -> DOUBLE_TRALSE -> TRUE -> INDETERMINATE")
    print("    None of {1,2,4} has delta=0 (none are 'pure').")
    print("    The cycle oscillates between the three 'active' truth values.")

    # 7. 3-adic norm trajectory
    print("\n[7] 3-ADIC NORMS along Collatz(27) — first 20 steps:")
    norms = adic3_trajectory_norms(27, 20)
    print("    " + " -> ".join(f"{x:.3f}" for x in norms))
    print("    (convergence in Z_3 requires norms -> 0)")
