"""
Step-Skipping Experiment Engine

Generates mathematical problems with KNOWN solutions requiring N intermediate
steps, then tests whether a consciousness-inspired solver can reach correct
answers WITHOUT computing all steps. Compares accuracy against random guessing
and full computation baselines across four problem domains.

Author: TI Framework
Date: February 2026
"""

import time
import math
import hashlib
import heapq
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass, field
from collections import defaultdict
from enum import Enum

import numpy as np
from scipy import stats


class ProblemType(Enum):
    MATRIX_CHAIN = "matrix_chain"
    NUMBER_SEQUENCE = "number_sequence"
    GRAPH_SHORTEST_PATH = "graph_shortest_path"
    LOGICAL_DEDUCTION = "logical_deduction"


class ShortcutMethod(Enum):
    STRUCTURAL_RESONANCE = "structural_resonance"
    DIMENSIONAL_REDUCTION = "dimensional_reduction"
    ENSEMBLE_VOTING = "ensemble_voting"
    BOUNDARY_ANALYSIS = "boundary_analysis"
    SYMMETRY_DETECTION = "symmetry_detection"


@dataclass
class Problem:
    problem_type: ProblemType
    difficulty: int
    data: Dict[str, Any]
    correct_answer: Any
    num_steps_required: int
    answer_space_size: int


@dataclass
class SolverResult:
    answer: Any
    correct: bool
    steps_taken: int
    time_taken: float
    method: str
    metadata: Dict[str, Any] = field(default_factory=dict)


@dataclass
class TrialResult:
    problem_type: str
    difficulty: int
    num_problems: int
    full_accuracy: float
    shortcut_accuracy: float
    random_accuracy: float
    shortcut_steps_saved_pct: float
    shortcut_speedup: float
    p_value: float
    problems: List[Dict[str, Any]]


def _extrapolate_finite_differences(seq: List[int], max_degree: int) -> int:
    diffs = [list(seq)]
    for d in range(max_degree):
        if len(diffs[-1]) < 2:
            break
        diffs.append([diffs[-1][i + 1] - diffs[-1][i] for i in range(len(diffs[-1]) - 1)])
    for d in range(len(diffs) - 1, 0, -1):
        diffs[d].append(diffs[d][-1])
    for d in range(len(diffs) - 2, -1, -1):
        diffs[d].append(diffs[d][-1] + diffs[d + 1][-1])
    return diffs[0][-1]


class MatrixChainGenerator:

    @staticmethod
    def generate(difficulty: int, rng: np.random.RandomState) -> Problem:
        n = difficulty + 3
        dims = [rng.randint(5, 50) for _ in range(n + 1)]
        m: list[list[float]] = [[0.0] * n for _ in range(n)]
        s = [[0] * n for _ in range(n)]
        for cl in range(2, n + 1):
            for i in range(n - cl + 1):
                j = i + cl - 1
                m[i][j] = float('inf')
                for k in range(i, j):
                    cost = m[i][k] + m[k + 1][j] + dims[i] * dims[k + 1] * dims[j + 1]
                    if cost < m[i][j]:
                        m[i][j] = cost
                        s[i][j] = k
        return Problem(
            problem_type=ProblemType.MATRIX_CHAIN, difficulty=difficulty,
            data={'dimensions': dims, 'n_matrices': n},
            correct_answer={'cost': m[0][n - 1], 'first_split': s[0][n - 1]},
            num_steps_required=n * (n - 1) * (n + 1) // 6, answer_space_size=n - 1,
        )

    @staticmethod
    def solve_full(problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        dims, n = problem.data['dimensions'], problem.data['n_matrices']
        m = [[0] * n for _ in range(n)]
        s = [[0] * n for _ in range(n)]
        steps = 0
        for cl in range(2, n + 1):
            for i in range(n - cl + 1):
                j = i + cl - 1
                m[i][j] = float('inf')
                for k in range(i, j):
                    cost = m[i][k] + m[k + 1][j] + dims[i] * dims[k + 1] * dims[j + 1]
                    steps += 1
                    if cost < m[i][j]:
                        m[i][j] = cost
                        s[i][j] = k
        answer = {'cost': m[0][n - 1], 'first_split': s[0][n - 1]}
        return SolverResult(answer=answer, correct=(answer['cost'] == problem.correct_answer['cost']),
                            steps_taken=steps, time_taken=time.perf_counter() - t0, method='full_dp')

    @staticmethod
    def solve_random(problem: Problem, rng: np.random.RandomState) -> SolverResult:
        t0 = time.perf_counter()
        n, dims = problem.data['n_matrices'], problem.data['dimensions']
        split = rng.randint(0, n - 1)
        answer = {'cost': dims[0] * dims[split + 1] * dims[n], 'first_split': split}
        return SolverResult(answer=answer, correct=(split == problem.correct_answer['first_split']),
                            steps_taken=0, time_taken=time.perf_counter() - t0, method='random')


class NumberSequenceGenerator:

    @staticmethod
    def _make_polynomial(degree: int, length: int, rng: np.random.RandomState) -> Tuple[List[int], int]:
        coeffs = [rng.randint(-5, 5) for _ in range(degree + 1)]
        if coeffs[-1] == 0:
            coeffs[-1] = 1
        seq = [sum(c * (x ** i) for i, c in enumerate(coeffs)) for x in range(length + 1)]
        return [int(v) for v in seq[:length]], int(seq[length])

    @staticmethod
    def _make_recurrence(order: int, length: int, rng: np.random.RandomState) -> Tuple[List[int], int]:
        coeffs = [rng.randint(-3, 3) for _ in range(order)]
        if all(c == 0 for c in coeffs):
            coeffs[0] = 1
        seq = [rng.randint(1, 10) for _ in range(order)]
        for _ in range(length - order + 1):
            seq.append(int(sum(c * seq[-(i + 1)] for i, c in enumerate(coeffs))))
        return seq[:length], seq[length]

    @staticmethod
    def _make_modular(mod: int, length: int, rng: np.random.RandomState) -> Tuple[List[int], int]:
        a, b = rng.randint(1, mod), rng.randint(0, mod)
        seq = [rng.randint(0, mod - 1)]
        for _ in range(length):
            seq.append((a * seq[-1] + b) % mod)
        return seq[:length], seq[length]

    @staticmethod
    def generate(difficulty: int, rng: np.random.RandomState) -> Problem:
        length = 6 + difficulty
        seq_type = rng.choice(['polynomial', 'recurrence', 'modular'])
        if seq_type == 'polynomial':
            degree = min(difficulty + 1, 4)
            seq, answer = NumberSequenceGenerator._make_polynomial(degree, length, rng)
            num_steps = degree + 1
        elif seq_type == 'recurrence':
            order = min(difficulty + 1, 4)
            seq, answer = NumberSequenceGenerator._make_recurrence(order, length, rng)
            num_steps = order * 2
        else:
            mod = 7 + difficulty * 3
            seq, answer = NumberSequenceGenerator._make_modular(mod, length, rng)
            num_steps = 3
        spread = max(abs(answer), max(abs(s) for s in seq), 10)
        return Problem(
            problem_type=ProblemType.NUMBER_SEQUENCE, difficulty=difficulty,
            data={'sequence': seq, 'seq_type': seq_type, 'length': length},
            correct_answer=answer, num_steps_required=num_steps,
            answer_space_size=max(spread * 4, 20),
        )

    @staticmethod
    def solve_full(problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        seq = problem.data['sequence']
        steps = 0
        for degree in range(1, min(len(seq), 6)):
            diffs = [list(seq)]
            for d in range(degree):
                new_diff = [diffs[-1][i + 1] - diffs[-1][i] for i in range(len(diffs[-1]) - 1)]
                diffs.append(new_diff)
                steps += len(new_diff)
            if all(v == diffs[-1][0] for v in diffs[-1]):
                answer = _extrapolate_finite_differences(seq, degree)
                return SolverResult(answer=answer, correct=(answer == problem.correct_answer),
                                    steps_taken=steps, time_taken=time.perf_counter() - t0,
                                    method='finite_differences')
        answer = seq[-1] + (seq[-1] - seq[-2]) if len(seq) >= 2 else seq[-1]
        return SolverResult(answer=answer, correct=(answer == problem.correct_answer),
                            steps_taken=steps, time_taken=time.perf_counter() - t0,
                            method='linear_extrapolation')

    @staticmethod
    def solve_random(problem: Problem, rng: np.random.RandomState) -> SolverResult:
        t0 = time.perf_counter()
        seq = problem.data['sequence']
        spread = max(abs(max(seq) - min(seq)), 10)
        lo, hi = min(seq) - spread, max(seq) + spread
        answer = int(rng.randint(lo, hi + 1))
        return SolverResult(answer=answer, correct=(answer == problem.correct_answer),
                            steps_taken=0, time_taken=time.perf_counter() - t0, method='random')


class GraphShortestPathGenerator:

    @staticmethod
    def generate(difficulty: int, rng: np.random.RandomState) -> Problem:
        n = 5 + difficulty * 2
        adj = defaultdict(list)
        for i in range(n - 1):
            w = rng.randint(1, 20)
            adj[i].append((i + 1, w))
            adj[i + 1].append((i, w))
        num_extra = int(n * (n - 1) * min(0.3 + difficulty * 0.05, 0.6) / 2) - (n - 1)
        for _ in range(max(0, num_extra)):
            u, v = rng.randint(0, n), rng.randint(0, n)
            if u != v:
                w = rng.randint(1, 30)
                adj[u].append((v, w))
                adj[v].append((u, w))
        source, target = 0, n - 1
        dist = [float('inf')] * n
        dist[source] = 0
        prev_node = [-1] * n
        visited = [False] * n
        steps = 0
        for _ in range(n):
            u = -1
            for v in range(n):
                if not visited[v] and (u == -1 or dist[v] < dist[u]):
                    u = v
                steps += 1
            if u == -1 or dist[u] == float('inf'):
                break
            visited[u] = True
            for v, w in adj[u]:
                steps += 1
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    prev_node[v] = u
        path = []
        curr = target
        while curr != -1:
            path.append(curr)
            curr = prev_node[curr]
        path.reverse()
        return Problem(
            problem_type=ProblemType.GRAPH_SHORTEST_PATH, difficulty=difficulty,
            data={'n_nodes': n, 'adj': {str(k): v for k, v in adj.items()},
                  'source': source, 'target': target},
            correct_answer={'distance': dist[target], 'path': path},
            num_steps_required=steps, answer_space_size=n * 5,
        )

    @staticmethod
    def solve_full(problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        n = problem.data['n_nodes']
        adj = defaultdict(list)
        for k, v in problem.data['adj'].items():
            adj[int(k)] = v
        source, target = problem.data['source'], problem.data['target']
        dist = [float('inf')] * n
        dist[source] = 0
        prev_node = [-1] * n
        pq = [(0, source)]
        steps = 0
        while pq:
            d, u = heapq.heappop(pq)
            steps += 1
            if d > dist[u]:
                continue
            for v, w in adj[u]:
                steps += 1
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    prev_node[v] = u
                    heapq.heappush(pq, (dist[v], v))
        path = []
        curr = target
        while curr != -1:
            path.append(curr)
            curr = prev_node[curr]
        path.reverse()
        answer = {'distance': dist[target], 'path': path}
        return SolverResult(answer=answer, correct=(answer['distance'] == problem.correct_answer['distance']),
                            steps_taken=steps, time_taken=time.perf_counter() - t0, method='dijkstra')

    @staticmethod
    def solve_random(problem: Problem, rng: np.random.RandomState) -> SolverResult:
        t0 = time.perf_counter()
        n, s, t = problem.data['n_nodes'], problem.data['source'], problem.data['target']
        return SolverResult(
            answer={'distance': int(rng.randint(1, n * 30)), 'path': [s, t]},
            correct=False, steps_taken=0, time_taken=time.perf_counter() - t0, method='random')


class LogicalDeductionGenerator:

    @staticmethod
    def generate(difficulty: int, rng: np.random.RandomState) -> Problem:
        n_vars = 3 + difficulty
        variables = [chr(ord('A') + i) for i in range(min(n_vars, 26))]
        assignment = {v: bool(rng.randint(0, 2)) for v in variables}
        premises = []
        for _ in range(3 + difficulty * 2):
            ptype = rng.choice(['implication', 'disjunction', 'conjunction', 'negation'])
            v1, v2 = rng.choice(variables, size=2, replace=False)
            if ptype == 'implication':
                if assignment[v1] and not assignment[v2]:
                    premises.append({'type': 'implication', 'antecedent': v2, 'consequent': v1})
                else:
                    premises.append({'type': 'implication', 'antecedent': v1, 'consequent': v2})
            elif ptype == 'disjunction':
                premises.append({'type': 'disjunction', 'left': v1, 'right': v2})
            elif ptype == 'conjunction':
                if assignment[v1] and assignment[v2]:
                    premises.append({'type': 'conjunction', 'left': v1, 'right': v2})
                else:
                    v_true = [v for v in variables if assignment[v]]
                    if len(v_true) >= 2:
                        pair = rng.choice(v_true, size=2, replace=False)
                        premises.append({'type': 'conjunction', 'left': pair[0], 'right': pair[1]})
                    else:
                        premises.append({'type': 'disjunction', 'left': v1, 'right': v2})
            else:
                v_neg = rng.choice(variables)
                premises.append({'type': 'negation', 'variable': v_neg, 'value': not assignment[v_neg]})
        conclusion_var = rng.choice(variables)
        conclusion_value = assignment[conclusion_var] if rng.random() < 0.6 else not assignment[conclusion_var]
        valid = LogicalDeductionGenerator._check_validity(premises, variables, conclusion_var, conclusion_value)
        return Problem(
            problem_type=ProblemType.LOGICAL_DEDUCTION, difficulty=difficulty,
            data={'variables': variables, 'premises': premises,
                  'conclusion_var': conclusion_var, 'conclusion_value': conclusion_value,
                  'n_vars': n_vars},
            correct_answer=valid, num_steps_required=2 ** n_vars, answer_space_size=2,
        )

    @staticmethod
    def _eval_premise(p: Dict, a: Dict[str, bool]) -> bool:
        if p['type'] == 'implication':
            return (not a.get(p['antecedent'], False)) or a.get(p['consequent'], False)
        if p['type'] == 'disjunction':
            return a.get(p['left'], False) or a.get(p['right'], False)
        if p['type'] == 'conjunction':
            return a.get(p['left'], False) and a.get(p['right'], False)
        if p['type'] == 'negation':
            return a.get(p['variable'], False) == p['value']
        return True

    @staticmethod
    def _check_validity(premises, variables, conclusion_var, conclusion_value) -> bool:
        n = len(variables)
        for bits in range(2 ** n):
            assignment = {v: bool((bits >> i) & 1) for i, v in enumerate(variables)}
            if all(LogicalDeductionGenerator._eval_premise(p, assignment) for p in premises):
                if assignment[conclusion_var] != conclusion_value:
                    return False
        return True

    @staticmethod
    def solve_full(problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        variables = problem.data['variables']
        premises = problem.data['premises']
        c_var, c_val = problem.data['conclusion_var'], problem.data['conclusion_value']
        n = len(variables)
        steps, valid = 0, True
        for bits in range(2 ** n):
            assignment = {v: bool((bits >> i) & 1) for i, v in enumerate(variables)}
            steps += 1
            if all(LogicalDeductionGenerator._eval_premise(p, assignment) for p in premises):
                steps += len(premises)
                if assignment[c_var] != c_val:
                    valid = False
                    break
            else:
                steps += len(premises)
        return SolverResult(answer=valid, correct=(valid == problem.correct_answer),
                            steps_taken=steps, time_taken=time.perf_counter() - t0, method='truth_table')

    @staticmethod
    def solve_random(problem: Problem, rng: np.random.RandomState) -> SolverResult:
        t0 = time.perf_counter()
        answer = bool(rng.randint(0, 2))
        return SolverResult(answer=answer, correct=(answer == problem.correct_answer),
                            steps_taken=0, time_taken=time.perf_counter() - t0, method='random')


class ConsciousnessShortcutSolver:
    """
    Consciousness-inspired solver that attempts to skip computational steps
    using structural resonance, dimensional reduction, ensemble voting,
    boundary analysis, and symmetry detection.
    """

    def __init__(self, rng: np.random.RandomState):
        self.rng = rng

    def solve(self, problem: Problem) -> SolverResult:
        dispatch = {
            ProblemType.MATRIX_CHAIN: self._solve_matrix_chain,
            ProblemType.NUMBER_SEQUENCE: self._solve_sequence,
            ProblemType.GRAPH_SHORTEST_PATH: self._solve_graph,
            ProblemType.LOGICAL_DEDUCTION: self._solve_logic,
        }
        return dispatch[problem.problem_type](problem)

    def _structural_hash(self, data: Any) -> str:
        raw = str(sorted(data.items()) if isinstance(data, dict) else data)
        return hashlib.md5(raw.encode()).hexdigest()[:8]

    def _gile_score(self, candidate: Any, problem: Problem) -> float:
        """GILE coherence: G(oodness), I(ntuition), L(ove/harmony), E(nvironment)."""
        g, i, l, e = 0.5, 0.5, 0.5, 0.5
        if problem.problem_type == ProblemType.MATRIX_CHAIN and isinstance(candidate, dict):
            dims, n = problem.data['dimensions'], problem.data['n_matrices']
            split = candidate.get('first_split', 0)
            if 0 <= split < n - 1:
                g = 0.8
                i = 0.6 + 0.3 * (1 - abs(split - (n - 2) / 2) / max(1, (n - 2) / 2))
                inner = dims[1:-1] if len(dims) > 2 else dims
                mn, mx = min(inner), max(inner)
                l = 0.5 + 0.4 * (1 - (dims[split + 1] - mn) / max(1, mx - mn)) if mx > mn else 0.7
                e = 0.7
        elif problem.problem_type == ProblemType.NUMBER_SEQUENCE and isinstance(candidate, (int, float)):
            seq = problem.data['sequence']
            if len(seq) >= 2:
                trend = seq[-1] - seq[-2]
                expected = seq[-1] + trend
                dev = abs(candidate - expected) / max(1, abs(expected)) if expected != 0 else abs(candidate)
                g = max(0, 1 - dev * 0.1)
                i = 0.7 if abs(candidate) < abs(max(seq, key=lambda x: abs(x))) * 5 else 0.3
                l, e = 0.6, 0.5
        elif problem.problem_type == ProblemType.GRAPH_SHORTEST_PATH and isinstance(candidate, dict):
            n = problem.data['n_nodes']
            d = candidate.get('distance', 0)
            if 0 < d < n * 30:
                g, i, e = 0.7, 0.6, 0.6
                path = candidate.get('path', [])
                l = 0.5 + 0.3 * min(1, len(path) / n) if len(path) > 1 else 0.4
        return 0.3 * g + 0.25 * i + 0.2 * l + 0.25 * e

    def _solve_matrix_chain(self, problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        dims, n = problem.data['dimensions'], problem.data['n_matrices']
        steps, candidates, methods = 0, [], []

        min_inner, min_split = float('inf'), 0
        for k in range(n - 1):
            steps += 1
            if dims[k + 1] < min_inner:
                min_inner, min_split = dims[k + 1], k
        candidates.append(min_split)
        methods.append(ShortcutMethod.BOUNDARY_ANALYSIS)

        candidates.append((n - 2) // 2)
        methods.append(ShortcutMethod.SYMMETRY_DETECTION)

        costs = []
        for k in range(n - 1):
            steps += 1
            costs.append((dims[0] * dims[k + 1] * dims[n], k))
        costs.sort()
        candidates.append(costs[0][1])
        methods.append(ShortcutMethod.DIMENSIONAL_REDUCTION)

        weighted = {}
        for k in range(n - 1):
            steps += 1
            dim_penalty = dims[k + 1] / max(dims)
            balance = 1 - abs(k - (n - 2) / 2) / max(1, (n - 2) / 2)
            weighted[k] = 0.6 * (1 - dim_penalty) + 0.4 * balance
        candidates.append(max(weighted, key=lambda k: weighted[k]))
        methods.append(ShortcutMethod.ENSEMBLE_VOTING)

        candidates.append(hash(self._structural_hash({'dims': dims[:3], 'n': n})) % (n - 1))
        methods.append(ShortcutMethod.STRUCTURAL_RESONANCE)

        scored = [(self._gile_score({'first_split': c, 'cost': 0}, problem), c) for c in candidates]
        scored.sort(reverse=True)
        best = scored[0][1]
        answer = {'cost': dims[0] * dims[best + 1] * dims[n], 'first_split': best}

        return SolverResult(
            answer=answer, correct=(best == problem.correct_answer['first_split']),
            steps_taken=steps, time_taken=time.perf_counter() - t0,
            method='consciousness_shortcut',
            metadata={'methods': [m.value for m in methods], 'gile_scores': [s[0] for s in scored]})

    def _solve_sequence(self, problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        seq = problem.data['sequence']
        steps, candidates, methods = 0, [], []

        if len(seq) >= 2:
            candidates.append(seq[-1] + (seq[-1] - seq[-2]))
            methods.append(ShortcutMethod.BOUNDARY_ANALYSIS)
            steps += 1

        if len(seq) >= 3:
            d1, d2 = seq[-1] - seq[-2], seq[-2] - seq[-3]
            candidates.append(seq[-1] + d1 + (d1 - d2))
            methods.append(ShortcutMethod.DIMENSIONAL_REDUCTION)
            steps += 2

        if len(seq) >= 4:
            diffs = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
            steps += len(diffs)
            diffs2 = [diffs[i + 1] - diffs[i] for i in range(len(diffs) - 1)]
            steps += len(diffs2)
            if len(set(diffs)) == 1:
                candidates.append(seq[-1] + diffs[0])
            elif len(set(diffs2)) == 1:
                candidates.append(seq[-1] + diffs[-1] + diffs2[0])
            if diffs2:
                diffs3 = [diffs2[i + 1] - diffs2[i] for i in range(len(diffs2) - 1)]
                steps += len(diffs3)
                if diffs3 and len(set(diffs3)) == 1:
                    candidates.append(seq[-1] + diffs[-1] + diffs2[-1] + diffs3[0])
            methods.append(ShortcutMethod.ENSEMBLE_VOTING)

        nonzero = [s for s in seq if s != 0]
        if len(nonzero) >= 2:
            ratios = [nonzero[i + 1] / nonzero[i] for i in range(len(nonzero) - 1) if nonzero[i] != 0]
            if ratios and all(abs(r - ratios[0]) < 0.01 for r in ratios):
                candidates.append(int(round(seq[-1] * ratios[0])))
                methods.append(ShortcutMethod.SYMMETRY_DETECTION)
                steps += len(ratios)

        if len(seq) >= 2:
            h = self._structural_hash({'f3': seq[:3], 'l2': seq[-2:]})
            diff_mean = np.mean([seq[i + 1] - seq[i] for i in range(len(seq) - 1)])
            r_rng = np.random.RandomState(int(h, 16) % 1000)
            candidates.append(int(round(seq[-1] + diff_mean + r_rng.normal(0, max(1, abs(diff_mean) * 0.1)))))
            methods.append(ShortcutMethod.STRUCTURAL_RESONANCE)
            steps += 2

        if not candidates:
            candidates.append(seq[-1] if seq else 0)

        scored = [(self._gile_score(c, problem), c) for c in candidates]
        scored.sort(reverse=True)
        best = scored[0][1]

        return SolverResult(
            answer=best, correct=(best == problem.correct_answer),
            steps_taken=steps, time_taken=time.perf_counter() - t0,
            method='consciousness_shortcut',
            metadata={'methods': [m.value for m in methods], 'n_candidates': len(candidates)})

    def _solve_graph(self, problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        n = problem.data['n_nodes']
        source, target = problem.data['source'], problem.data['target']
        adj = defaultdict(list)
        for k, v in problem.data['adj'].items():
            adj[int(k)] = v
        steps, candidates, methods = 0, [], []

        direct = {v: w for v, w in adj[source]}
        steps += len(direct)
        if target in direct:
            candidates.append({'distance': direct[target], 'path': [source, target]})
        methods.append(ShortcutMethod.BOUNDARY_ANALYSIS)

        dist_g, path_g, visited_g, curr = 0, [source], {source}, source
        for _ in range(n):
            if curr == target:
                break
            nbrs = [(v, w) for v, w in adj[curr] if v not in visited_g]
            steps += len(nbrs)
            if not nbrs:
                break
            nbrs.sort(key=lambda x: x[1] + abs(x[0] - target) * 0.5)
            best_v, best_w = nbrs[0]
            dist_g += best_w
            path_g.append(best_v)
            visited_g.add(best_v)
            curr = best_v
        if curr == target:
            candidates.append({'distance': dist_g, 'path': path_g})
        methods.append(ShortcutMethod.DIMENSIONAL_REDUCTION)

        dist_bfs = [float('inf')] * n
        dist_bfs[source] = 0
        prev_bfs = [-1] * n
        pq = [(0, source)]
        bfs_visited = set()
        while pq and steps < n * 6:
            d, u = heapq.heappop(pq)
            steps += 1
            if u in bfs_visited:
                continue
            bfs_visited.add(u)
            if u == target:
                break
            selected = sorted(adj[u], key=lambda x: x[1])[:max(1, len(adj[u]) // 2 + 1)]
            for v, w in selected:
                steps += 1
                if dist_bfs[u] + w < dist_bfs[v]:
                    dist_bfs[v] = dist_bfs[u] + w
                    prev_bfs[v] = u
                    heapq.heappush(pq, (dist_bfs[v], v))
        if dist_bfs[target] < float('inf'):
            path_b = []
            c = target
            while c != -1:
                path_b.append(c)
                c = prev_bfs[c]
            path_b.reverse()
            candidates.append({'distance': dist_bfs[target], 'path': path_b})
        methods.append(ShortcutMethod.ENSEMBLE_VOTING)

        if not candidates:
            candidates.append({'distance': n * 10, 'path': [source, target]})

        scored = [(self._gile_score(c, problem), idx, c) for idx, c in enumerate(candidates)]
        scored.sort(key=lambda x: x[0], reverse=True)
        best = scored[0][2]

        return SolverResult(
            answer=best, correct=(best['distance'] == problem.correct_answer['distance']),
            steps_taken=steps, time_taken=time.perf_counter() - t0,
            method='consciousness_shortcut',
            metadata={'methods': [m.value for m in methods], 'n_candidates': len(candidates)})

    def _solve_logic(self, problem: Problem) -> SolverResult:
        t0 = time.perf_counter()
        variables = problem.data['variables']
        premises = problem.data['premises']
        c_var = problem.data['conclusion_var']
        c_val = problem.data['conclusion_value']
        steps, methods = 0, []

        forced = {}
        for p in premises:
            steps += 1
            if p['type'] == 'negation':
                forced[p['variable']] = p['value']
            elif p['type'] == 'conjunction':
                forced[p['left']] = True
                forced[p['right']] = True
        methods.append(ShortcutMethod.DIMENSIONAL_REDUCTION)

        if c_var in forced:
            answer = (forced[c_var] == c_val)
            return SolverResult(answer=answer, correct=(answer == problem.correct_answer),
                                steps_taken=steps, time_taken=time.perf_counter() - t0,
                                method='consciousness_shortcut',
                                metadata={'methods': [ShortcutMethod.DIMENSIONAL_REDUCTION.value], 'early': True})

        implied = dict(forced)
        changed = True
        while changed:
            changed = False
            for p in premises:
                steps += 1
                if p['type'] == 'implication':
                    ant, con = p['antecedent'], p['consequent']
                    if ant in implied and implied[ant] and con not in implied:
                        implied[con] = True
                        changed = True
                    if con in implied and not implied[con] and ant not in implied:
                        implied[ant] = False
                        changed = True
        methods.append(ShortcutMethod.STRUCTURAL_RESONANCE)

        if c_var in implied:
            answer = (implied[c_var] == c_val)
            return SolverResult(answer=answer, correct=(answer == problem.correct_answer),
                                steps_taken=steps, time_taken=time.perf_counter() - t0,
                                method='consciousness_shortcut',
                                metadata={'methods': [m.value for m in methods], 'propagation': True})

        free_vars = [v for v in variables if v not in implied]
        n_free = len(free_vars)
        votes = []

        n_check = min(2 ** n_free, 32)
        valid_with, valid_without = 0, 0
        for idx in range(n_check):
            assignment = dict(implied)
            if n_free <= 5:
                for i, v in enumerate(free_vars):
                    assignment[v] = bool((idx >> i) & 1)
            else:
                for v in free_vars:
                    assignment[v] = bool(self.rng.randint(0, 2))
            steps += 1
            if all(LogicalDeductionGenerator._eval_premise(p, assignment) for p in premises):
                if assignment.get(c_var) == c_val:
                    valid_with += 1
                else:
                    valid_without += 1
        votes.append(valid_without == 0 and valid_with > 0)
        methods.append(ShortcutMethod.ENSEMBLE_VOTING)

        imp_support = sum(1 for p in premises if p['type'] == 'implication' and p['consequent'] == c_var)
        votes.append(c_val if imp_support > 0 else not c_val)
        methods.append(ShortcutMethod.BOUNDARY_ANALYSIS)

        h = self._structural_hash({'nv': len(variables), 'np': len(premises)})
        votes.append(bool(int(h, 16) % 2) == c_val)
        methods.append(ShortcutMethod.STRUCTURAL_RESONANCE)

        answer = sum(1 for v in votes if v) > len(votes) / 2

        return SolverResult(
            answer=answer, correct=(answer == problem.correct_answer),
            steps_taken=steps, time_taken=time.perf_counter() - t0,
            method='consciousness_shortcut',
            metadata={'methods': [m.value for m in methods], 'votes': votes, 'n_free': n_free})


class StepSkippingExperiment:
    """
    Measures whether consciousness-inspired heuristics achieve accuracy
    significantly greater than random chance while skipping computational steps.
    """

    def __init__(self, seed: int = 42):
        self.seed = seed
        self.rng = np.random.RandomState(seed)
        self.trials: List[TrialResult] = []
        self.results: Dict[str, Any] = {}
        self.shortcut_solver = ConsciousnessShortcutSolver(self.rng)

    def generate_problem(self, problem_type: ProblemType, difficulty: int) -> Problem:
        generators = {
            ProblemType.MATRIX_CHAIN: MatrixChainGenerator,
            ProblemType.NUMBER_SEQUENCE: NumberSequenceGenerator,
            ProblemType.GRAPH_SHORTEST_PATH: GraphShortestPathGenerator,
            ProblemType.LOGICAL_DEDUCTION: LogicalDeductionGenerator,
        }
        return generators[problem_type].generate(difficulty, self.rng)

    def solve_full(self, problem: Problem) -> SolverResult:
        solvers = {
            ProblemType.MATRIX_CHAIN: MatrixChainGenerator,
            ProblemType.NUMBER_SEQUENCE: NumberSequenceGenerator,
            ProblemType.GRAPH_SHORTEST_PATH: GraphShortestPathGenerator,
            ProblemType.LOGICAL_DEDUCTION: LogicalDeductionGenerator,
        }
        return solvers[problem.problem_type].solve_full(problem)

    def solve_consciousness_shortcut(self, problem: Problem) -> SolverResult:
        return self.shortcut_solver.solve(problem)

    def solve_random(self, problem: Problem) -> SolverResult:
        solvers = {
            ProblemType.MATRIX_CHAIN: MatrixChainGenerator,
            ProblemType.NUMBER_SEQUENCE: NumberSequenceGenerator,
            ProblemType.GRAPH_SHORTEST_PATH: GraphShortestPathGenerator,
            ProblemType.LOGICAL_DEDUCTION: LogicalDeductionGenerator,
        }
        return solvers[problem.problem_type].solve_random(problem, self.rng)

    def _binom_test(self, successes: int, n: int, p: float) -> float:
        if p <= 0 or p >= 1:
            return 1.0
        return float(1 - stats.binom.cdf(successes - 1, n, p))

    def run_trial(self, problem_type: ProblemType, difficulty: int,
                  num_problems: int = 10) -> TrialResult:
        problems_results = []
        full_c, short_c, rand_c = 0, 0, 0
        full_steps, short_steps = 0, 0
        full_time, short_time = 0.0, 0.0

        for i in range(num_problems):
            problem = self.generate_problem(problem_type, difficulty)
            fr = self.solve_full(problem)
            sr = self.solve_consciousness_shortcut(problem)
            rr = self.solve_random(problem)

            full_c += fr.correct
            short_c += sr.correct
            rand_c += rr.correct
            full_steps += fr.steps_taken
            short_steps += sr.steps_taken
            full_time += fr.time_taken
            short_time += sr.time_taken

            problems_results.append({
                'index': i, 'type': problem_type.value, 'difficulty': difficulty,
                'steps_required': problem.num_steps_required,
                'answer_space': problem.answer_space_size,
                'correct_answer': str(problem.correct_answer),
                'full': {'correct': fr.correct, 'steps': fr.steps_taken, 'time': fr.time_taken},
                'shortcut': {'correct': sr.correct, 'steps': sr.steps_taken,
                             'time': sr.time_taken, 'metadata': sr.metadata},
                'random': {'correct': rr.correct, 'time': rr.time_taken},
            })

        n = num_problems
        rand_chance = max(rand_c / n, 1.0 / max(1, problems_results[0]['answer_space']))
        if rand_chance >= 1.0:
            rand_chance = 0.5
        p_val = self._binom_test(short_c, n, rand_chance)
        steps_saved = (1 - short_steps / full_steps) * 100 if full_steps > 0 else 0.0
        speedup = full_time / short_time if short_time > 0 else (float('inf') if full_time > 0 else 1.0)

        trial = TrialResult(
            problem_type=problem_type.value, difficulty=difficulty, num_problems=n,
            full_accuracy=full_c / n, shortcut_accuracy=short_c / n,
            random_accuracy=rand_c / n, shortcut_steps_saved_pct=steps_saved,
            shortcut_speedup=speedup, p_value=float(p_val), problems=problems_results,
        )
        self.trials.append(trial)
        return trial

    def run_full_experiment(self, trials_per_type: int = 10,
                            problems_per_trial: int = 10) -> Dict[str, Any]:
        all_results = {}
        for ptype in ProblemType:
            type_results = []
            for diff in [1, 2, 3]:
                for t_idx in range(trials_per_type):
                    trial = self.run_trial(ptype, diff, problems_per_trial)
                    type_results.append({
                        'trial': t_idx, 'difficulty': diff,
                        'full_acc': trial.full_accuracy, 'shortcut_acc': trial.shortcut_accuracy,
                        'random_acc': trial.random_accuracy, 'steps_saved': trial.shortcut_steps_saved_pct,
                        'speedup': trial.shortcut_speedup, 'p_value': trial.p_value,
                    })
            all_results[ptype.value] = type_results
        self.results = {
            'experiment': 'step_skipping', 'seed': self.seed,
            'trials_per_type': trials_per_type, 'problems_per_trial': problems_per_trial,
            'difficulties': [1, 2, 3], 'types': [p.value for p in ProblemType],
            'type_results': all_results, 'summary': self.get_statistical_summary(),
        }
        return self.results

    def get_statistical_summary(self) -> Dict[str, Any]:
        """
        Chi-square test, binomial test, effect size (Cohen's h).
        Is shortcut accuracy significantly > random?
        """
        if not self.trials:
            return {'error': 'No trials have been run yet'}

        sc_ok, sc_n, rc_ok, rc_n, fc_ok, fc_n = 0, 0, 0, 0, 0, 0
        per_type: Dict[str, Dict[str, list]] = defaultdict(lambda: defaultdict(list))

        for t in self.trials:
            n = t.num_problems
            sc = int(round(t.shortcut_accuracy * n))
            rc = int(round(t.random_accuracy * n))
            fc = int(round(t.full_accuracy * n))
            sc_ok += sc; sc_n += n
            rc_ok += rc; rc_n += n
            fc_ok += fc; fc_n += n
            d = per_type[t.problem_type]
            d['s_acc'].append(t.shortcut_accuracy)
            d['r_acc'].append(t.random_accuracy)
            d['f_acc'].append(t.full_accuracy)
            d['steps'].append(t.shortcut_steps_saved_pct)
            d['speed'].append(t.shortcut_speedup)
            d['pval'].append(t.p_value)

        s_acc = sc_ok / max(1, sc_n)
        r_acc = rc_ok / max(1, rc_n)
        f_acc = fc_ok / max(1, fc_n)

        base_p = max(r_acc, 0.01)
        exp = np.array([sc_n * base_p, sc_n * (1 - base_p)])
        exp = np.maximum(exp, 1)
        obs = np.array([sc_ok, sc_n - sc_ok])
        chi2 = float(np.sum((obs - exp) ** 2 / exp))
        chi2_p = float(1 - stats.chi2.cdf(chi2, df=1))
        binom_p = self._binom_test(sc_ok, sc_n, base_p)

        h1 = 2 * math.asin(math.sqrt(max(0, min(1, s_acc))))
        h2 = 2 * math.asin(math.sqrt(max(0, min(1, r_acc))))
        cohens_h = h1 - h2
        mag = 'large' if abs(cohens_h) > 0.8 else 'medium' if abs(cohens_h) > 0.5 else 'small' if abs(cohens_h) > 0.2 else 'negligible'

        type_summaries = {}
        for pt, d in per_type.items():
            ms, mr = float(np.mean(d['s_acc'])), float(np.mean(d['r_acc']))
            ps = float(np.sqrt((np.var(d['s_acc']) + np.var(d['r_acc'])) / 2)) if len(d['s_acc']) > 1 else 1.0
            cd = (ms - mr) / max(ps, 0.001)
            if len(d['s_acc']) > 1 and np.std(d['s_acc']) > 0:
                t_stat, t_p = stats.ttest_ind(d['s_acc'], d['r_acc'])
            else:
                t_stat, t_p = 0.0, 1.0
            fin_speeds = [s for s in d['speed'] if s != float('inf')]
            type_summaries[pt] = {
                'n_trials': len(d['s_acc']),
                'mean_shortcut_accuracy': ms,
                'mean_random_accuracy': mr,
                'mean_full_accuracy': float(np.mean(d['f_acc'])),
                'std_shortcut': float(np.std(d['s_acc'])),
                'mean_steps_saved_pct': float(np.mean(d['steps'])),
                'mean_speedup': float(np.mean(fin_speeds)) if fin_speeds else 0.0,
                'significant_trials': sum(1 for p in d['pval'] if p < 0.05),
                'ttest_p': float(t_p), 'cohens_d': float(cd),
                'beats_random': ms > mr,
            }

        sig = chi2_p < 0.05 or binom_p < 0.05
        best = max(type_summaries, key=lambda k: type_summaries[k]['mean_shortcut_accuracy'] - type_summaries[k]['mean_random_accuracy']) if type_summaries else None
        worst = min(type_summaries, key=lambda k: type_summaries[k]['mean_shortcut_accuracy'] - type_summaries[k]['mean_random_accuracy']) if type_summaries else None

        return {
            'total_trials': len(self.trials), 'total_problems': sc_n,
            'overall_shortcut_accuracy': s_acc, 'overall_random_accuracy': r_acc,
            'overall_full_accuracy': f_acc,
            'accuracy_improvement': s_acc - r_acc,
            'chi_square': {'statistic': chi2, 'p_value': chi2_p, 'significant': chi2_p < 0.05},
            'binomial_test': {'successes': sc_ok, 'total': sc_n, 'baseline': base_p,
                              'p_value': binom_p, 'significant': binom_p < 0.05},
            'effect_size': {'cohens_h': cohens_h, 'magnitude': mag},
            'per_type': type_summaries,
            'conclusion': {
                'significant': sig, 'effect': mag,
                'strongest_domain': best, 'weakest_domain': worst,
            },
        }

    def format_report(self) -> str:
        s = self.get_statistical_summary()
        if 'error' in s:
            return f"Error: {s['error']}"
        lines = [
            "=" * 70, "STEP-SKIPPING EXPERIMENT REPORT", "=" * 70, "",
            f"Total Trials: {s['total_trials']}  |  Total Problems: {s['total_problems']}", "",
            "OVERALL ACCURACY:",
            f"  Full computation:       {s['overall_full_accuracy']:.1%}",
            f"  Consciousness shortcut: {s['overall_shortcut_accuracy']:.1%}",
            f"  Random baseline:        {s['overall_random_accuracy']:.1%}",
            f"  Improvement over random: {s['accuracy_improvement']:+.1%}", "",
            "STATISTICAL SIGNIFICANCE:",
            f"  Chi-square: X2={s['chi_square']['statistic']:.2f}, p={s['chi_square']['p_value']:.6f} "
            f"{'*** SIGNIFICANT' if s['chi_square']['significant'] else ''}",
            f"  Binomial:   p={s['binomial_test']['p_value']:.6f} "
            f"{'*** SIGNIFICANT' if s['binomial_test']['significant'] else ''}",
            f"  Cohen's h:  {s['effect_size']['cohens_h']:.3f} ({s['effect_size']['magnitude']})", "",
            "PER-DOMAIN RESULTS:", "-" * 70,
        ]
        for pt, d in s.get('per_type', {}).items():
            lines += [
                f"\n  {pt.upper()}:",
                f"    Shortcut: {d['mean_shortcut_accuracy']:.1%} (+-{d['std_shortcut']:.1%})",
                f"    Random:   {d['mean_random_accuracy']:.1%}  |  Full: {d['mean_full_accuracy']:.1%}",
                f"    Steps saved: {d['mean_steps_saved_pct']:.1f}%  |  Speedup: {d['mean_speedup']:.1f}x",
                f"    Cohen's d: {d['cohens_d']:.2f}  |  Sig trials: {d['significant_trials']}/{d['n_trials']}",
                f"    Beats random: {'YES' if d['beats_random'] else 'NO'}",
            ]
        lines += ["", "=" * 70]
        c = s['conclusion']
        if c['significant']:
            lines.append(f"CONCLUSION: Shortcut SIGNIFICANTLY outperforms random ({c['effect']} effect)")
        else:
            lines.append("CONCLUSION: Shortcut does NOT significantly outperform random")
        lines += [f"  Strongest: {c.get('strongest_domain', 'N/A')}",
                  f"  Weakest:   {c.get('weakest_domain', 'N/A')}", "=" * 70]
        return "\n".join(lines)


def run_quick_experiment() -> Dict[str, Any]:
    experiment = StepSkippingExperiment(seed=42)
    results = experiment.run_full_experiment(trials_per_type=3, problems_per_trial=10)
    print(experiment.format_report())
    return results


def run_full_experiment() -> Dict[str, Any]:
    experiment = StepSkippingExperiment(seed=42)
    results = experiment.run_full_experiment(trials_per_type=10, problems_per_trial=15)
    print(experiment.format_report())
    return results


if __name__ == '__main__':
    run_quick_experiment()
