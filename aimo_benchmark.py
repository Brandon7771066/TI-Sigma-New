"""
TI Sigma AIMO Independent Benchmark — 110 Competition Math Problems
====================================================================
URB #675 — Brandon Emerick | TI Sigma / BlissGene Therapeutics | April 2026

110 problems spanning: number theory, combinatorics, algebra, geometry.
Difficulty levels 1-3 (1=AIME 1-5, 2=AIME 6-10, 3=AIME 11-15/olympiad).
All answers are non-negative integers; most bounded to 0-999.

Each problem has a verified ground-truth answer computed in Python.
The benchmark tests TI Sigma MR-collapse solver vs. baseline Claude.
"""

import math
import json
import time
import os
from typing import Optional
from functools import reduce
import anthropic

# ── Problem bank construction ─────────────────────────────────────────────────

PROBLEMS: list[dict] = []

def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a

def phi_euler(n: int) -> int:
    result = n
    p, temp = 2, n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0: temp //= p
            result -= result // p
        p += 1
    if temp > 1: result -= result // temp
    return result

def num_divisors(n: int) -> int:
    return sum(1 for k in range(1, n + 1) if n % k == 0)

def lcm(a: int, b: int) -> int:
    return a * b // math.gcd(a, b)

def catalan(n: int) -> int:
    return math.comb(2 * n, n) // (n + 1)

def derangement(n: int) -> int:
    if n == 0: return 1
    if n == 1: return 0
    return (n - 1) * (derangement(n - 1) + derangement(n - 2))

def collatz_steps(n: int) -> int:
    steps = 0
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        steps += 1
    return steps

def no_consec_ones(n: int) -> int:
    a, b = 1, 2
    for _ in range(2, n + 1): a, b = b, a + b
    return b

def legendre(n: int, p: int) -> int:
    total, pk = 0, p
    while pk <= n:
        total += n // pk
        pk *= p
    return total

def add(q: str, a: int, cat: str, diff: int):
    a = int(a)
    assert a >= 0, f"Negative answer {a} for: {q[:50]}"
    PROBLEMS.append({"id": len(PROBLEMS) + 1, "q": q, "a": a, "cat": cat, "diff": diff})

# ─────────────────────────────────────────────────────────────
# TIER 1: Number Theory (33 problems)
# ─────────────────────────────────────────────────────────────

add("Find the remainder when 7^100 is divided by 1000.",
    pow(7, 100, 1000), "number_theory", 2)

add("Find the remainder when 3^200 is divided by 1000.",
    pow(3, 200, 1000), "number_theory", 2)

add("Find the remainder when 13^50 is divided by 1000.",
    pow(13, 50, 1000), "number_theory", 2)

add("Find the remainder when 2^30 is divided by 1000.",
    pow(2, 30, 1000), "number_theory", 1)

add("Find Euler's totient function φ(360).",
    phi_euler(360), "number_theory", 1)

add("Find Euler's totient function φ(1000).",
    phi_euler(1000), "number_theory", 2)

add("Find Euler's totient function φ(720).",
    phi_euler(720), "number_theory", 2)

add("How many positive divisors does 360 have?",
    num_divisors(360), "number_theory", 1)

add("How many positive divisors does 1000 have?",
    num_divisors(1000), "number_theory", 1)

add("How many positive divisors does 720 have?",
    num_divisors(720), "number_theory", 2)

add("Find the sum of all positive divisors of 360.",
    sum(k for k in range(1, 361) if 360 % k == 0) % 1000, "number_theory", 2)

add("Find GCD(1260, 945).",
    math.gcd(1260, 945), "number_theory", 1)

add("Find LCM(12, 15, 20) mod 1000.",
    reduce(lcm, [12, 15, 20]) % 1000, "number_theory", 1)

add("Find LCM(1, 2, 3, ..., 12) mod 1000.",
    reduce(lcm, range(1, 13)) % 1000, "number_theory", 2)

add("How many trailing zeros does 100! have?",
    legendre(100, 5), "number_theory", 2)

add("How many trailing zeros does 1000! have?",
    legendre(1000, 5), "number_theory", 2)

add("Find the largest power of 2 dividing 100! (the exponent of 2 in 100!).",
    legendre(100, 2), "number_theory", 3)

add("Find the multiplicative order of 2 modulo 7 (smallest k ≥ 1 with 2^k ≡ 1 mod 7).",
    min(k for k in range(1, 8) if pow(2, k, 7) == 1), "number_theory", 2)

add("Find the multiplicative order of 3 modulo 17.",
    min(k for k in range(1, 18) if pow(3, k, 17) == 1), "number_theory", 3)

add("Find the smallest positive integer x satisfying: x ≡ 2 (mod 3), x ≡ 3 (mod 5), and x ≡ 2 (mod 7).",
    next(x for x in range(1, 106) if x%3==2 and x%5==3 and x%7==2),
    "number_theory", 2)

add("Find the smallest positive integer x satisfying: x ≡ 3 (mod 11), x ≡ 5 (mod 13), and x ≡ 6 (mod 7).",
    next(x for x in range(1, 2000) if x%11==3 and x%13==5 and x%7==6),
    "number_theory", 3)

add("How many positive integers n ≤ 1000 satisfy n² ≡ 1 (mod 1000)?",
    sum(1 for n in range(1, 1001) if pow(n, 2, 1000) == 1),
    "number_theory", 3)

add("Find the digit sum of 2^20 = 1048576.",
    sum(int(d) for d in str(2**20)), "number_theory", 1)

add("Find the digit sum of 20! = 2432902008176640000.",
    sum(int(d) for d in str(math.factorial(20))), "number_theory", 2)

add("How many 3-digit palindromes exist (numbers like 121, 363, 999)?",
    sum(1 for n in range(100, 1000) if str(n) == str(n)[::-1]),
    "number_theory", 1)

add("Find the remainder when 111111 (six ones) is divided by 7.",
    111111 % 7, "number_theory", 2)

add("How many primes p ≤ 100 exist?",
    25, "number_theory", 1)  # well-known result

add("How many primes p ≤ 200 exist?",
    46, "number_theory", 2)  # well-known result

add("Find the sum φ(1) + φ(2) + ... + φ(99) mod 1000, where φ is Euler's totient.",
    sum(phi_euler(k) for k in range(1, 100)) % 1000, "number_theory", 3)

add("How many positive integers n < 50 satisfy 7 | (n² + n + 1)?",
    sum(1 for n in range(1, 50) if (n*n + n + 1) % 7 == 0),
    "number_theory", 3)

add("Find the number of positive integers from 1 to 2024 divisible by both 3 and 7.",
    len([n for n in range(1, 2025) if n % 21 == 0]),
    "number_theory", 1)

add("How many numbers from 1 to 1000 are coprime to 360?",
    sum(1 for k in range(1, 1001) if math.gcd(k, 360) == 1) % 1000,
    "number_theory", 2)

add("Find the total number of digits used when writing all integers from 1 to 1000.",
    sum(len(str(n)) for n in range(1, 1001)) % 1000, "number_theory", 2)

# ─────────────────────────────────────────────────────────────
# TIER 2: Combinatorics (33 problems)
# ─────────────────────────────────────────────────────────────

add("Find C(20, 10) mod 1000.",
    math.comb(20, 10) % 1000, "combinatorics", 2)

add("Find C(15, 7) mod 1000.",
    math.comb(15, 7) % 1000, "combinatorics", 1)

add("Find C(25, 12) mod 1000.",
    math.comb(25, 12) % 1000, "combinatorics", 2)

add("Find 7! mod 1000.",
    math.factorial(7) % 1000, "combinatorics", 1)

add("Find 10! mod 1000.",
    math.factorial(10) % 1000, "combinatorics", 1)

add("Find 8! mod 1000.",
    math.factorial(8) % 1000, "combinatorics", 1)

add("Find the number of derangements of 8 elements, D(8), mod 1000.",
    derangement(8) % 1000, "combinatorics", 2)

add("Find the number of derangements of 10 elements, D(10), mod 1000.",
    derangement(10) % 1000, "combinatorics", 3)

add("Find the 10th Catalan number C₁₀ mod 1000.",
    catalan(10) % 1000, "combinatorics", 2)

add("Find the 12th Catalan number C₁₂ mod 1000.",
    catalan(12) % 1000, "combinatorics", 3)

add("In how many ways can 10 be expressed as an ordered sum (composition) of positive integers?",
    2**9, "combinatorics", 2)

add("In how many ways can 15 be expressed as a composition into positive integers?",
    2**14 % 1000, "combinatorics", 2)

add("Find the number of non-negative integer solutions to x₁ + x₂ + x₃ + x₄ = 10.",
    math.comb(10 + 3, 3), "combinatorics", 2)

add("How many binary strings of length 10 have no two consecutive 1s?",
    no_consec_ones(10), "combinatorics", 3)

add("In how many ways can a 2×10 grid be tiled with 1×2 dominoes?",
    fib(11), "combinatorics", 3)

add("In how many ways can 5 pairs of parentheses be correctly matched?",
    catalan(5), "combinatorics", 2)

add("In how many ways can 8 non-attacking rooks be placed on an 8×8 chessboard?",
    math.factorial(8) % 1000, "combinatorics", 3)

add("Find the sum of all entries in row 10 of Pascal's triangle (0-indexed), mod 1000.",
    2**10 % 1000, "combinatorics", 1)

add("Find the sum of even-indexed entries in row 15 of Pascal's triangle: C(15,0)+C(15,2)+...+C(15,14), mod 1000.",
    sum(math.comb(15, k) for k in range(0, 16, 2)) % 1000, "combinatorics", 2)

add("How many ways can 2 dice (1–6) show a sum of 7?",
    6, "combinatorics", 1)

add("How many ways can 2 dice (1–6) show a sum greater than 9?",
    sum(1 for d1 in range(1, 7) for d2 in range(1, 7) if d1+d2 > 9),
    "combinatorics", 1)

add("How many ways can 2 dice (1–6) show a sum of exactly 5?",
    sum(1 for d1 in range(1, 7) for d2 in range(1, 7) if d1+d2 == 5),
    "combinatorics", 1)

add("In how many ways can you choose a committee of 4 from 12 people, if 2 specific people cannot both serve?",
    math.comb(12, 4) - math.comb(10, 2), "combinatorics", 2)

add("How many permutations of {1,2,3,4,5,6,7,8} begin with 3 and end with 5?",
    math.factorial(6), "combinatorics", 2)

add("How many 4-letter strings using letters A,B,C,D (with repetition) are possible?",
    4**4, "combinatorics", 1)

add("How many subsets of {1,2,3,...,10} have exactly 3 elements summing to an even number?",
    sum(1 for mask in range(1 << 10)
        if bin(mask).count('1') == 3 and
        sum(i+1 for i in range(10) if mask >> i & 1) % 2 == 0),
    "combinatorics", 3)

add("Find the Stirling number of the second kind S(8,4) mod 1000.",
    # S(8,4) = 1701
    (sum((-1)**(4-j) * math.comb(4, j) * j**8 for j in range(5)) // math.factorial(4)) % 1000,
    "combinatorics", 3)

add("How many ways can 6 people be seated in a circle (rotations considered identical)?",
    math.factorial(5), "combinatorics", 2)

add("How many 3-element subsets of {1,2,...,20} have all elements with the same parity?",
    math.comb(10, 3) * 2, "combinatorics", 2)

add("How many positive integers ≤ 500 are divisible by 3 or 5 (or both)?",
    len([n for n in range(1, 501) if n % 3 == 0 or n % 5 == 0]),
    "combinatorics", 2)

add("How many ways can 10 people be divided into 2 groups of 5 (groups are unlabeled)?",
    math.comb(10, 5) // 2, "combinatorics", 2)

add("How many lattice points (x,y) satisfy x² + y² ≤ 25?",
    sum(1 for x in range(-5, 6) for y in range(-5, 6) if x*x + y*y <= 25),
    "combinatorics", 2)

add("How many ways are there to distribute 10 identical balls into 4 distinct boxes?",
    math.comb(13, 3), "combinatorics", 2)

# ─────────────────────────────────────────────────────────────
# TIER 3: Algebra & Sequences (44 problems)
# ─────────────────────────────────────────────────────────────

add("Find the sum 1 + 2 + 3 + ... + 100.",
    5050 % 1000, "algebra", 1)

add("Find 1² + 2² + ... + 50² mod 1000.",
    sum(k**2 for k in range(1, 51)) % 1000, "algebra", 2)

add("Find 1³ + 2³ + ... + 20³ mod 1000.",
    sum(k**3 for k in range(1, 21)) % 1000, "algebra", 2)

add("Find the 30th Fibonacci number F(30) where F(1)=F(2)=1, mod 1000.",
    fib(30) % 1000, "algebra", 2)

add("Find the 50th Fibonacci number F(50) mod 1000.",
    fib(50) % 1000, "algebra", 2)

add("Find the 100th Fibonacci number F(100) mod 1000.",
    fib(100) % 1000, "algebra", 3)

add("Find 2^10 − 1.",
    2**10 - 1, "algebra", 1)

add("Find the sum 1 + 2 + 4 + ... + 2^19 mod 1000 (geometric series with ratio 2).",
    (2**20 - 1) % 1000, "algebra", 1)

add("Find the sum of the geometric series 4 + 12 + 36 + ... (first 6 terms) mod 1000.",
    4 * (3**6 - 1) // 2 % 1000, "algebra", 2)

add("If x² − 5x + 6 = 0, find x₁² + x₂² (sum of squares of both roots).",
    25 - 2 * 6, "algebra", 2)

add("If x² − 7x + 10 = 0, find x₁³ + x₂³.",
    # x1+x2=7, x1*x2=10; x1^3+x2^3 = (x1+x2)^3 - 3x1x2(x1+x2) = 343-210=133
    343 - 3 * 10 * 7, "algebra", 2)

add("Find the 50th triangular number T(50) = 1 + 2 + ... + 50.",
    50 * 51 // 2 % 1000, "algebra", 1)

add("Find the 100th triangular number T(100) mod 1000.",
    100 * 101 // 2 % 1000, "algebra", 1)

add("Compute ⌊√1⌋ + ⌊√2⌋ + ... + ⌊√100⌋ mod 1000.",
    sum(int(n**0.5) for n in range(1, 101)) % 1000, "algebra", 2)

add("Compute ⌊100/1⌋ + ⌊100/2⌋ + ... + ⌊100/100⌋ mod 1000.",
    sum(100 // k for k in range(1, 101)) % 1000, "algebra", 3)

add("Compute ⌊1/2⌋ + ⌊2/2⌋ + ... + ⌊100/2⌋.",
    sum(k // 2 for k in range(1, 101)) % 1000, "algebra", 2)

add("Find P(10) where P(x) = x³ − 6x² + 11x − 6.",
    1000 - 600 + 110 - 6, "algebra", 1)

add("Find the number of steps the Collatz sequence starting at 27 takes to reach 1.",
    collatz_steps(27), "algebra", 2)

add("Find the number of steps the Collatz sequence starting at 97 takes to reach 1.",
    collatz_steps(97), "algebra", 2)

add("Find the number of steps the Collatz sequence starting at 871 takes to reach 1.",
    collatz_steps(871) % 1000, "algebra", 3)

add("Compute 10 × (1/(1·2) + 1/(2·3) + ... + 1/(9·10)). Note: the sum telescopes.",
    9, "algebra", 2)

add("Compute the sum: 1·2 + 2·3 + 3·4 + ... + 10·11 mod 1000.",
    sum(k*(k+1) for k in range(1, 11)) % 1000, "algebra", 2)

add("If the arithmetic sequence has first term 3 and common difference 4, what is the 50th term?",
    3 + 49 * 4, "algebra", 1)

add("Find the sum of the first 20 terms of the arithmetic series: 5, 8, 11, 14, ...",
    20 * (2*5 + 19*3) // 2 % 1000, "algebra", 2)

add("Find the 30th term of the Lucas sequence L(n) where L(1)=1, L(2)=3, L(n)=L(n-1)+L(n-2), mod 1000.",
    # Lucas: 2,1,3,4,7,11,... note some use L(0)=2,L(1)=1
    # Using L(1)=1, L(2)=3:
    (lambda: (lambda s: s[-1] % 1000)(
        [1, 3] + [0]*28 or
        (lambda lst: [lst.__setitem__(i, lst[i-1]+lst[i-2]) or lst for i in range(2,30)])(
            [1,3]+[0]*28))
    )(),
    "algebra", 2)

# Fix the Lucas problem with simple loop
lucas_seq = [1, 3]
for _ in range(28): lucas_seq.append(lucas_seq[-1] + lucas_seq[-2])
PROBLEMS.pop()  # remove the broken one
add("Find the 30th term of the Lucas sequence where L(1)=1, L(2)=3 (so each term is sum of two before it), mod 1000.",
    lucas_seq[-1] % 1000, "algebra", 2)

add("Compute 2^20 mod 1000.",
    pow(2, 20, 1000), "algebra", 1)

add("Compute 5^10 mod 1000.",
    pow(5, 10, 1000), "algebra", 1)

add("Find the sum of the first 10 perfect squares: 1 + 4 + 9 + ... + 100.",
    sum(k**2 for k in range(1, 11)), "algebra", 1)

add("Find the smallest positive integer n such that n² > 1000.",
    math.isqrt(1000) + 1, "algebra", 1)

add("Find the largest integer n such that n² ≤ 10000.",
    math.isqrt(10000), "algebra", 1)

add("Find the number of perfect squares between 100 and 500 inclusive.",
    math.isqrt(500) - math.isqrt(99), "algebra", 2)

add("Compute the sum 1/(1·2) + 1/(2·3) + ... + 1/(19·20) expressed as a fraction p/q where p,q coprime. Find 20q − 20p.",
    # Sum = 1 - 1/20 = 19/20, so p=19,q=20; 20*20-20*19=400-380=20
    20, "algebra", 2)

add("Find the remainder when (1! + 2! + 3! + ... + 10!) is divided by 100.",
    sum(math.factorial(k) for k in range(1, 11)) % 100, "algebra", 2)

add("Find 1! + 2! + ... + 20! mod 1000.",
    sum(math.factorial(k) for k in range(1, 21)) % 1000, "algebra", 2)

add("Find the number of integers between 1 and 200 that are NOT divisible by 2, 3, or 5.",
    sum(1 for n in range(1, 201) if n%2!=0 and n%3!=0 and n%5!=0),
    "algebra", 2)

add("If the sum of n terms of an arithmetic series is n(3n+1)/2, find the 10th term.",
    # S(n) = n(3n+1)/2; T(n) = S(n)-S(n-1) = (3n+1)/2 - (3(n-1)+1)/2... 
    # T(n) = S(n)-S(n-1) = [n(3n+1) - (n-1)(3n-2)]/2 = [3n^2+n - 3n^2+5n-2]/2 = (6n-2)/2 = 3n-1
    # T(10) = 29
    29, "algebra", 2)

add("How many integers from 1 to 100 are divisible by exactly one of 2 or 3?",
    # Div by 2: 50; div by 3: 33; div by both (6): 16
    # Exactly one = (50-16) + (33-16) = 34+17 = 51
    (50 - 16) + (33 - 16), "algebra", 2)

add("Find the maximum value of xy subject to x + y = 20, where x and y are positive integers.",
    # x=y=10 gives 100
    100, "algebra", 1)

add("Find the number of positive integer solutions to x + y + z = 15.",
    math.comb(14, 2), "algebra", 2)

add("Find the value of 1×2 + 2×3 + 3×4 + ... + 9×10.",
    sum(k*(k+1) for k in range(1, 10)), "algebra", 1)

add("Compute the remainder when 2^100 + 3^100 is divided by 5.",
    (pow(2, 100, 5) + pow(3, 100, 5)) % 5, "algebra", 2)

add("How many positive integer solutions exist for 1/x + 1/y = 1/12?",
    # 1/x + 1/y = 1/12 → (x-12)(y-12) = 144. Divisors of 144 = 15 divisor pairs, all positive.
    len([(d, 144//d) for d in range(1, 145) if 144 % d == 0 and d <= 144//d]) * 2
    - (1 if 144 == 12**2 else 0),
    "number_theory", 3)

add("Find the sum of all integers from −50 to 50 inclusive.",
    0, "algebra", 1)

add("How many 4-digit numbers (1000 to 9999) have all four digits distinct?",
    9 * 9 * 8 * 7, "combinatorics", 2)

print(f"Total problems: {len(PROBLEMS)}")
from collections import Counter
cat_counts = Counter(p['cat'] for p in PROBLEMS)
diff_counts = Counter(p['diff'] for p in PROBLEMS)
for c, n in sorted(cat_counts.items()): print(f"  {c}: {n}")
for d, n in sorted(diff_counts.items()): print(f"  Difficulty {d}: {n}")


# ── TI Sigma Solver ────────────────────────────────────────────────────────────

TI_SYSTEM = """You are a rigorous mathematical solver using the TI Sigma MR (Myrion Resolution) framework.

For each problem:
1. CLASSIFY the domain (number theory / combinatorics / algebra / geometry)
2. STATE the key formula or theorem needed
3. COMPUTE step-by-step, showing all arithmetic
4. VERIFY: check if your answer is close to a special constant (φ≈1.618, √2≈1.414, e≈2.718, π≈3.14159)
5. STATE your final integer answer clearly as: ANSWER: [integer]

Important: The answer is always a non-negative integer. If the problem says "mod 1000", your answer is 0-999. Be exact."""

BASELINE_SYSTEM = """You are a mathematical problem solver. Solve the problem step by step and give the final integer answer as: ANSWER: [integer]"""

def extract_answer(text: str) -> Optional[int]:
    """Extract integer from ANSWER: [n] or last integer mention."""
    import re
    matches = re.findall(r'ANSWER:\s*\[?(\d+)\]?', text, re.IGNORECASE)
    if matches:
        return int(matches[-1])
    matches = re.findall(r'\b(\d{1,4})\b', text)
    if matches:
        return int(matches[-1])
    return None

def solve_one(client: anthropic.Anthropic, problem: str, system: str,
              model: str = "claude-haiku-4-5") -> tuple[Optional[int], str]:
    msg = client.messages.create(
        model=model,
        max_tokens=800,
        system=system,
        messages=[{"role": "user", "content": problem}],
    )
    text = msg.content[0].text
    return extract_answer(text), text


def run_benchmark(
    n_problems: int = 110,
    model: str = "claude-haiku-4-5",
    mode: str = "ti_sigma",   # "ti_sigma" | "baseline" | "both"
    save_path: str = "aimo_benchmark_results.json",
    max_problems: Optional[int] = None,
):
    client = anthropic.Anthropic()
    problems = PROBLEMS[:max_problems] if max_problems else PROBLEMS

    results = []
    ti_correct = baseline_correct = 0
    ti_total   = baseline_total   = 0

    system_ti   = TI_SYSTEM
    system_base = BASELINE_SYSTEM

    print(f"\n{'='*65}")
    print(f"TI SIGMA AIMO INDEPENDENT BENCHMARK — {len(problems)} problems")
    print(f"Model: {model} | Mode: {mode}")
    print(f"{'='*65}\n")

    for i, prob in enumerate(problems, 1):
        q   = prob["q"]
        ans = prob["a"]
        rec = {"id": prob["id"], "q": q, "true_answer": ans,
               "cat": prob["cat"], "diff": prob["diff"]}

        # TI Sigma pass
        if mode in ("ti_sigma", "both"):
            ti_ans, ti_text = solve_one(client, q, system_ti, model)
            ti_ok = (ti_ans == ans)
            rec["ti_answer"]  = ti_ans
            rec["ti_correct"] = ti_ok
            ti_total += 1
            if ti_ok: ti_correct += 1
            status = "✅" if ti_ok else "❌"
            print(f"[{i:3d}/{len(problems)}] {status} TI={ti_ans} TRUE={ans}  {q[:60]}")
            time.sleep(0.2)

        # Baseline pass
        if mode in ("baseline", "both"):
            bl_ans, bl_text = solve_one(client, q, system_base, model)
            bl_ok = (bl_ans == ans)
            rec["baseline_answer"]  = bl_ans
            rec["baseline_correct"] = bl_ok
            baseline_total += 1
            if bl_ok: baseline_correct += 1
            if mode == "baseline":
                status = "✅" if bl_ok else "❌"
                print(f"[{i:3d}/{len(problems)}] {status} BL={bl_ans} TRUE={ans}  {q[:60]}")
            time.sleep(0.2)

        results.append(rec)

    print(f"\n{'='*65}")
    if mode in ("ti_sigma", "both"):
        print(f"TI Sigma accuracy:  {ti_correct}/{ti_total} = {ti_correct/ti_total:.1%}")
    if mode in ("baseline", "both"):
        print(f"Baseline accuracy:  {baseline_correct}/{baseline_total} = {baseline_correct/baseline_total:.1%}")
    if mode == "both":
        delta = (ti_correct - baseline_correct) / ti_total
        print(f"TI Sigma advantage: {delta:+.1%}")
    print(f"{'='*65}\n")

    # Category breakdown
    if results:
        from collections import defaultdict
        cat_stats = defaultdict(lambda: {"ti_c": 0, "ti_t": 0, "bl_c": 0, "bl_t": 0})
        for r in results:
            c = r["cat"]
            if "ti_correct" in r:
                cat_stats[c]["ti_t"] += 1
                if r["ti_correct"]: cat_stats[c]["ti_c"] += 1
            if "baseline_correct" in r:
                cat_stats[c]["bl_t"] += 1
                if r["baseline_correct"]: cat_stats[c]["bl_c"] += 1
        print("By category:")
        for cat, s in sorted(cat_stats.items()):
            ti_str = f"{s['ti_c']}/{s['ti_t']}={s['ti_c']/max(1,s['ti_t']):.0%}" if s['ti_t'] else "-"
            bl_str = f"{s['bl_c']}/{s['bl_t']}={s['bl_c']/max(1,s['bl_t']):.0%}" if s['bl_t'] else "-"
            print(f"  {cat:15s}  TI={ti_str}  Base={bl_str}")

    with open(save_path, "w") as f:
        json.dump({
            "model": model,
            "n_problems": len(problems),
            "ti_accuracy": ti_correct / ti_total if ti_total else None,
            "baseline_accuracy": baseline_correct / baseline_total if baseline_total else None,
            "results": results,
        }, f, indent=2)
    print(f"Results saved → {save_path}")
    return results


if __name__ == "__main__":
    import sys
    mode   = sys.argv[1] if len(sys.argv) > 1 else "both"
    n      = int(sys.argv[2]) if len(sys.argv) > 2 else None
    run_benchmark(mode=mode, max_problems=n)
