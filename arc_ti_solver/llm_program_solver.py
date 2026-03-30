"""
LLM Program Synthesis Solver — ARC-AGI Phase 6
================================================

Best-practice ARC architecture: ask an LLM to analyze training examples
and write a Python `transform(grid)` function. Test the function on all
training pairs. If it passes, apply to test.

Architecture (state-of-the-art):
  1. Format training examples clearly (grid + ASCII + color names)
  2. Prompt LLM to reason about the pattern, then write Python code
  3. Execute generated code safely in a subprocess sandbox
  4. Validate against all training pairs (exact match required)
  5. If validation fails, send error feedback + ask for a fix (up to 3 retries)

TI Sigma integration:
  - Domain classification guides the system prompt
  - LCC scoring validates the generated function
  - If LLM solution found: LCC=1.0 (exact match guaranteed by validation)
  - Failed attempts go to TRALSE log (DT immunity for that pattern)

Models used:
  - Primary: Claude (claude-opus-4-5) — best spatial/visual reasoning
  - Backup:  GPT-4 (gpt-4o) — used if Claude fails or times out

Author: Brandon Emerick (TI Sigma / ARC Phase 6)
Date: March 30, 2026
"""

import os
import json
import subprocess
import tempfile
import textwrap
import numpy as np
from typing import Optional

# ── Color naming for LLM prompts ─────────────────────────────────────────────
ARC_COLOR_NAMES = {
    0: "black",
    1: "blue",
    2: "red",
    3: "green",
    4: "yellow",
    5: "gray",
    6: "magenta",
    7: "orange",
    8: "azure",
    9: "maroon",
}

ARC_SYMBOLS = {
    0: ".",
    1: "b",
    2: "r",
    3: "g",
    4: "y",
    5: "a",
    6: "m",
    7: "o",
    8: "c",
    9: "w",
}


def _grid_to_ascii(grid: list) -> str:
    """Convert grid to ASCII art for LLM readability."""
    return "\n".join(" ".join(ARC_SYMBOLS.get(c, str(c)) for c in row)
                     for row in grid)


def _grid_to_str(grid: list) -> str:
    """Convert grid to compact list-of-lists string."""
    return json.dumps(grid)


def _format_examples(task: dict, max_pairs: int = 5) -> str:
    """Format training pairs for the LLM prompt."""
    lines = []
    for i, pair in enumerate(task["train"][:max_pairs]):
        inp = pair["input"]
        out = pair["output"]
        lines.append(f"=== Example {i+1} ===")
        lines.append(f"INPUT ({len(inp)}×{len(inp[0])}):")
        lines.append(_grid_to_ascii(inp))
        lines.append(f"OUTPUT ({len(out)}×{len(out[0])}):")
        lines.append(_grid_to_ascii(out))
        lines.append("")
    return "\n".join(lines)


def _build_prompt(task: dict, domain_hint: str = "", error_feedback: str = "") -> str:
    """Build the LLM prompt for program synthesis, grounded in the skill library."""
    examples_str = _format_examples(task)

    # Color legend
    colors_in_task = set()
    for pair in task["train"]:
        for row in pair["input"]:
            colors_in_task.update(row)
        for row in pair["output"]:
            colors_in_task.update(row)
    color_legend = ", ".join(
        f"{c}={ARC_COLOR_NAMES.get(c, str(c))}"
        for c in sorted(colors_in_task)
    )

    domain_hint_str = f"\n[Domain hint: {domain_hint}]" if domain_hint else ""

    error_str = ""
    if error_feedback:
        error_str = f"""
=== PREVIOUS ATTEMPT FAILED ===
Error / mismatch:
{error_feedback}

Please fix the transform() function. The issue is above.
"""

    # Include known skill descriptions as context
    try:
        from arc_ti_solver.skill_library import SKILL_REGISTRY
        skill_hints = "\n".join(
            f"  - {s.name}: {s.description}"
            for s in SKILL_REGISTRY
        )
        skill_section = f"""
Known transformation primitives (check these first before inventing new ones):
{skill_hints}
"""
    except ImportError:
        skill_section = ""

    prompt = f"""You are solving an ARC-AGI visual reasoning puzzle.
{domain_hint_str}
Color legend: {color_legend}
Symbol key: . = black, b = blue, r = red, g = green, y = yellow, a = gray, m = magenta, o = orange, c = azure, w = maroon
{skill_section}
{examples_str}
{error_str}
Your task:
1. Study the examples and identify the exact transformation rule
2. Check if any known primitive above fits (or a simple composition of them)
3. Write a Python function `transform(grid)` that implements the rule
4. The function takes a list[list[int]] and returns a list[list[int]]
5. The rule must generalize — do NOT hardcode outputs

Rules:
- Use only Python standard library + numpy (import as needed)
- Background color is almost always the most common color (usually 0=black)
- Return the output as a list of lists of integers (not numpy arrays)

Think step by step, then write the code.

Respond EXACTLY in this format:
<reasoning>
[Your step-by-step analysis — which primitive fits, or what new rule applies]
</reasoning>
<code>
def transform(grid):
    import numpy as np
    # your implementation
    ...
    return result  # list[list[int]]
</code>"""
    return prompt


def _extract_code(llm_response: str) -> Optional[str]:
    """Extract the Python function from LLM response."""
    if "<code>" in llm_response and "</code>" in llm_response:
        start = llm_response.index("<code>") + len("<code>")
        end = llm_response.index("</code>")
        code = llm_response[start:end].strip()
        return code

    # Fallback: find ```python blocks
    if "```python" in llm_response:
        start = llm_response.index("```python") + len("```python")
        end = llm_response.index("```", start)
        return llm_response[start:end].strip()

    if "```" in llm_response:
        start = llm_response.index("```") + 3
        end = llm_response.index("```", start)
        code = llm_response[start:end].strip()
        if "def transform" in code:
            return code

    # Last resort: find the function directly
    if "def transform" in llm_response:
        idx = llm_response.index("def transform")
        return llm_response[idx:].strip()

    return None


def _execute_function_safely(code: str, test_input: list, timeout: float = 5.0) -> Optional[list]:
    """
    Execute the generated transform function in a subprocess sandbox.
    Returns the result or None on error.
    """
    # Write test script to temp file
    script = textwrap.dedent(f"""
import json, sys, numpy as np

{code}

inp = json.loads('{json.dumps(test_input)}')
try:
    result = transform(inp)
    if isinstance(result, np.ndarray):
        result = result.tolist()
    print(json.dumps(result))
except Exception as e:
    print(f"ERROR: {{e}}", file=sys.stderr)
    sys.exit(1)
""")

    with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
        f.write(script)
        fname = f.name

    try:
        result = subprocess.run(
            ["python3", fname],
            capture_output=True, text=True, timeout=timeout
        )
        if result.returncode == 0:
            output = result.stdout.strip()
            if output:
                return json.loads(output)
        return None
    except (subprocess.TimeoutExpired, json.JSONDecodeError, Exception):
        return None
    finally:
        try:
            os.unlink(fname)
        except Exception:
            pass


def _validate_on_training(code: str, train_pairs: list) -> dict:
    """
    Test the generated function on all training pairs.
    Returns: {
        'perfect': bool,       # all pairs match exactly
        'accuracy': float,     # cell-level accuracy across all pairs
        'errors': list[str],   # error descriptions
    }
    """
    errors = []
    total_cells = 0
    correct_cells = 0

    for i, pair in enumerate(train_pairs):
        predicted = _execute_function_safely(code, pair["input"])
        if predicted is None:
            errors.append(f"Pair {i+1}: function crashed or timed out")
            continue

        gt = pair["output"]
        pg = np.array(predicted)
        gg = np.array(gt)

        if pg.shape != gg.shape:
            errors.append(
                f"Pair {i+1}: wrong output size — got {list(pg.shape)}, "
                f"expected {list(gg.shape)}"
            )
            continue

        cells = pg.size
        correct = int(np.sum(pg == gg))
        total_cells += cells
        correct_cells += correct

        if not np.array_equal(pg, gg):
            # Show first few diffs
            diffs = np.argwhere(pg != gg)[:3]
            diff_str = ", ".join(
                f"[{r},{c}]: got {pg[r,c]} expected {gg[r,c]}"
                for r, c in diffs
            )
            errors.append(f"Pair {i+1}: mismatch at {diff_str}")

    perfect = (len(errors) == 0)
    accuracy = correct_cells / total_cells if total_cells > 0 else 0.0

    return {"perfect": perfect, "accuracy": accuracy, "errors": errors}


def _call_claude(prompt: str, max_tokens: int = 2048) -> Optional[str]:
    """
    Call Claude.
    Priority:
      1. Direct ANTHROPIC_API_KEY secret (user's own key — bypasses modelfarm)
      2. Replit modelfarm (AI_INTEGRATIONS_ANTHROPIC_API_KEY)
    """
    from anthropic import Anthropic

    # 1. Try direct key first
    direct_key = os.environ.get("ANTHROPIC_API_KEY")
    if direct_key:
        try:
            client = Anthropic(api_key=direct_key)
            msg = client.messages.create(
                model="claude-opus-4-5",
                max_tokens=max_tokens,
                messages=[{"role": "user", "content": prompt}],
            )
            return msg.content[0].text
        except Exception:
            pass  # fall through to modelfarm

    # 2. Replit modelfarm fallback
    try:
        client = Anthropic(
            api_key=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY"),
            base_url=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL"),
        )
        msg = client.messages.create(
            model="claude-opus-4-5",
            max_tokens=max_tokens,
            messages=[{"role": "user", "content": prompt}],
        )
        return msg.content[0].text
    except Exception:
        return None


def _call_gpt(prompt: str, max_tokens: int = 2048) -> Optional[str]:
    """
    Call GPT-4.
    Priority:
      1. Direct OPENAI_API_KEY secret (user's own key)
      2. Replit modelfarm (AI_INTEGRATIONS_OPENAI_API_KEY)
    """
    from openai import OpenAI

    # 1. Try direct key first
    direct_key = os.environ.get("OPENAI_API_KEY")
    if direct_key:
        try:
            client = OpenAI(api_key=direct_key)
            resp = client.chat.completions.create(
                model="gpt-4o",
                messages=[{"role": "user", "content": prompt}],
                max_tokens=max_tokens,
            )
            return resp.choices[0].message.content
        except Exception:
            pass  # fall through to modelfarm

    # 2. Replit modelfarm fallback
    try:
        client = OpenAI(
            api_key=os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY"),
            base_url=os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL"),
        )
        resp = client.chat.completions.create(
            model="gpt-4o",
            messages=[{"role": "user", "content": prompt}],
            max_tokens=max_tokens,
        )
        return resp.choices[0].message.content
    except Exception:
        return None


def solve_with_llm(
    task: dict,
    task_id: str = "?",
    domain_hint: str = "",
    max_retries: int = 3,
    verbose: bool = False,
) -> Optional[dict]:
    """
    Main LLM program synthesis solver.

    Tries up to `max_retries` times, alternating Claude → GPT → Claude.
    Each attempt:
      1. Build prompt (with error feedback from previous attempt)
      2. Call LLM
      3. Extract code from response
      4. Validate code on all training pairs
      5. If perfect: apply to test and return result
      6. If not: feed errors into next prompt

    Returns:
        {
            'output': list[list[int]],
            'lcc': 1.0,
            'method': 'llm_claude' or 'llm_gpt',
            'code': str,
            'attempts': int,
        }
        or None if all attempts fail.
    """
    train_pairs = task.get("train", [])
    test_pairs = task.get("test", [])

    if not train_pairs or not test_pairs:
        return None

    last_error = ""
    last_code = None
    best_accuracy = 0.0
    best_output = None
    best_method = None

    callers = [("claude", _call_claude), ("gpt", _call_gpt), ("claude", _call_claude)]

    for attempt in range(max_retries):
        model_name, caller_fn = callers[attempt % len(callers)]

        prompt = _build_prompt(task, domain_hint=domain_hint, error_feedback=last_error)

        if verbose:
            print(f"  [{task_id}] Attempt {attempt+1}/{max_retries} using {model_name}...")

        response = caller_fn(prompt)
        if response is None:
            if verbose:
                print(f"  [{task_id}] LLM call failed (no response)")
            last_error = "LLM call returned no response."
            continue

        code = _extract_code(response)
        if code is None:
            if verbose:
                print(f"  [{task_id}] Could not extract code from response")
            last_error = "Could not find a `def transform(grid):` function in your response."
            continue

        # Validate on training pairs
        validation = _validate_on_training(code, train_pairs)

        if verbose:
            print(f"  [{task_id}] Validation: perfect={validation['perfect']} "
                  f"accuracy={validation['accuracy']:.3f}")

        if validation["perfect"]:
            # Apply to test
            test_input = test_pairs[0]["input"]
            output = _execute_function_safely(code, test_input)
            if output is not None:
                if verbose:
                    print(f"  [{task_id}] SUCCESS with {model_name} on attempt {attempt+1}")
                return {
                    "output": output,
                    "lcc": 1.0,
                    "method": f"llm_{model_name}",
                    "code": code,
                    "reasoning": _extract_reasoning(response),
                    "attempts": attempt + 1,
                }

        # Save best partial result
        if validation["accuracy"] > best_accuracy:
            best_accuracy = validation["accuracy"]
            last_code = code
            best_method = model_name
            # Generate best-guess output anyway
            test_input = test_pairs[0]["input"]
            best_output = _execute_function_safely(code, test_input)

        last_error = "\n".join(validation["errors"][:5])

    # Return best partial if accuracy is high enough (>= 80%)
    if best_accuracy >= 0.80 and best_output is not None:
        if verbose:
            print(f"  [{task_id}] Partial success: accuracy={best_accuracy:.3f}")
        return {
            "output": best_output,
            "lcc": best_accuracy * 0.9,  # Discounted LCC for partial
            "method": f"llm_{best_method}_partial",
            "code": last_code,
            "attempts": max_retries,
        }

    return None


def _extract_reasoning(response: str) -> str:
    """Extract reasoning from LLM response."""
    if "<reasoning>" in response and "</reasoning>" in response:
        start = response.index("<reasoning>") + len("<reasoning>")
        end = response.index("</reasoning>")
        return response[start:end].strip()
    return ""
