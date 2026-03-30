"""
ARC-AGI Phase 7 Meta-Learner

Orchestrates the full solving pipeline:
  1. Try every skill in the library (fast, deterministic)
  2. If no skill works, try LLM program synthesis (Claude/GPT-4)
  3. If LLM works, add the synthesized skill to a session cache for reuse
  4. Return the best result with confidence score

This mirrors how an infant solves novel problems:
  experience (skill library) → recognition (skill matching) → application
"""

from __future__ import annotations
import numpy as np
import json
from pathlib import Path
from typing import Optional

from arc_ti_solver.skill_library import SKILL_REGISTRY, Skill


# ── Result ─────────────────────────────────────────────────────────────────────

class SolveResult:
    def __init__(self, output, lcc, skill_name, method="rule_based", source="skill_library"):
        self.output = output
        self.lcc = lcc
        self.skill_name = skill_name
        self.method = method
        self.source = source

    def to_dict(self):
        return {
            "output": self.output,
            "lcc": self.lcc,
            "skill": self.skill_name,
            "method": self.method,
            "source": self.source,
        }


# ── Skill Session Cache ────────────────────────────────────────────────────────

class SkillSessionCache:
    """
    Stores LLM-generated skills during a session so they can be reused
    across tasks (e.g., if the LLM synthesizes a 'checkerboard_fill'
    function for task A, it can try it on task B without re-querying the LLM).
    """
    def __init__(self):
        self._cache: list[Skill] = []

    def add(self, skill: Skill):
        self._cache.append(skill)

    def all_skills(self) -> list[Skill]:
        return self._cache

    def __len__(self):
        return len(self._cache)


SESSION_CACHE = SkillSessionCache()


# ── Meta-Learner ───────────────────────────────────────────────────────────────

class MetaLearner:
    """
    The primary entry point for Phase 7 solving.

    Usage:
        learner = MetaLearner(task, task_id="abc123")
        result = learner.solve(use_llm=True, verbose=True)
        if result:
            print(result.output)
    """

    def __init__(self, task: dict, task_id: str = "unknown"):
        self.task = task
        self.task_id = task_id
        self.train = task.get("train", [])
        self.test_input = task.get("test", [{}])[0].get("input", [])

    # ── Phase 7a: Rule-Based Skill Matching ────────────────────────────────────

    def _try_skill_library(self, verbose=False) -> Optional[SolveResult]:
        all_skills = SKILL_REGISTRY + SESSION_CACHE.all_skills()
        candidates = []

        for skill in all_skills:
            exact_match, lcc = skill.verify(self.task)
            if lcc > 0:
                candidates.append((lcc, skill))

        if not candidates:
            return None

        candidates.sort(key=lambda x: -x[0])
        best_lcc, best_skill = candidates[0]

        if verbose:
            status = "EXACT" if best_lcc == 1.0 else f"PARTIAL({best_lcc:.2f})"
            print(f"  [{self.task_id}] Best skill: {best_skill.name} [{status}]")

        if best_lcc == 1.0:
            output = best_skill.apply(self.test_input, self.task)
            if output is not None:
                return SolveResult(
                    output=output,
                    lcc=1.0,
                    skill_name=best_skill.name,
                    method="rule_based",
                    source=best_skill.family,
                )

        return None

    # ── Phase 7b: LLM Program Synthesis ────────────────────────────────────────

    def _try_llm(self, verbose=False) -> Optional[SolveResult]:
        try:
            from arc_ti_solver.llm_program_solver import solve_with_llm
        except ImportError:
            return None

        if verbose:
            print(f"  [{self.task_id}] Falling back to LLM program synthesis...")

        result = solve_with_llm(
            self.task,
            task_id=self.task_id,
            max_retries=3,
            verbose=verbose,
        )

        if result is None:
            return None

        return SolveResult(
            output=result["output"],
            lcc=result.get("lcc", 0.0),
            skill_name=result.get("method", "llm_synthesized"),
            method="llm_synthesized",
            source="llm",
        )

    # ── Main Solve ──────────────────────────────────────────────────────────────

    def solve(self, use_llm: bool = True, verbose: bool = False) -> Optional[SolveResult]:
        if not self.train or not self.test_input:
            return None

        # Step 1: Try the rule-based skill library
        result = self._try_skill_library(verbose=verbose)
        if result and result.lcc == 1.0:
            if verbose:
                print(f"  [{self.task_id}] Rule-based EXACT match: {result.skill_name}")
            return result

        # Step 2: LLM program synthesis
        if use_llm:
            llm_result = self._try_llm(verbose=verbose)
            if llm_result and llm_result.lcc >= 0.85:
                if verbose:
                    print(f"  [{self.task_id}] LLM result accepted (LCC={llm_result.lcc:.2f})")
                return llm_result

        # Return best partial match if nothing else works
        if result:
            return result

        return None


# ── Batch Evaluation ───────────────────────────────────────────────────────────

def run_meta_benchmark(
    data_dir: str = "arc_ti_solver/data/training",
    use_llm: bool = False,
    verbose: bool = False,
    max_tasks: Optional[int] = None,
) -> dict:
    """
    Run the meta-learner over all training tasks and report accuracy.
    """
    task_files = sorted(Path(data_dir).glob("*.json"))
    if max_tasks:
        task_files = task_files[:max_tasks]

    solved = []
    skill_wins = {}
    total = 0

    for tf in task_files:
        with open(tf) as f:
            task = json.load(f)

        learner = MetaLearner(task, task_id=tf.stem)
        result = learner.solve(use_llm=use_llm, verbose=verbose)

        gt = task.get("test", [{}])[0].get("output", [])
        correct = False

        if result and gt:
            pred = np.array(result.output)
            gta = np.array(gt)
            correct = pred.shape == gta.shape and np.array_equal(pred, gta)

        if correct:
            solved.append(tf.stem)
            skill_wins[result.skill_name] = skill_wins.get(result.skill_name, 0) + 1

        total += 1

    return {
        "solved": solved,
        "n_solved": len(solved),
        "total": total,
        "accuracy": len(solved) / total if total else 0,
        "skill_wins": skill_wins,
    }


# ── Skill Coverage Report ──────────────────────────────────────────────────────

def skill_coverage_report(data_dir: str = "arc_ti_solver/data/training") -> None:
    """
    Report how many tasks each skill can solve (training accuracy per skill).
    """
    task_files = sorted(Path(data_dir).glob("*.json"))
    skill_matches = {s.name: 0 for s in SKILL_REGISTRY}

    for tf in task_files:
        with open(tf) as f:
            task = json.load(f)
        for skill in SKILL_REGISTRY:
            exact, lcc = skill.verify(task)
            if exact:
                skill_matches[skill.name] += 1

    print("Skill coverage (exact matches on 400 training tasks):")
    print(f"{'Skill':<35} {'Matches':>7}  {'Family'}")
    print("-" * 65)
    for name, count in sorted(skill_matches.items(), key=lambda x: -x[1]):
        skill = next(s for s in SKILL_REGISTRY if s.name == name)
        if count > 0:
            print(f"{name:<35} {count:>7}  {skill.family}")
    total = sum(skill_matches.values())
    print(f"\nTotal skill matches (may overlap): {total}")


if __name__ == "__main__":
    print("Running skill coverage report...")
    skill_coverage_report()
    print()
    print("Running meta-benchmark (rule-based only)...")
    results = run_meta_benchmark(use_llm=False, verbose=False)
    print(f"Solved: {results['n_solved']}/{results['total']} "
          f"({100*results['accuracy']:.1f}%)")
    print("By skill:", results["skill_wins"])
