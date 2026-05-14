"""T51-V1 Pass-53 viral content generator CLI.

6-pillar gpt-5 prose generator + gpt-5-as-judge scoring rubric.
Audit-first principle (Pass-52 I11): complements existing biological_virality_engine.py
and viral_meme_generator.py rather than duplicating them. Existing engine handles
template-based memes + biological/acoustic scoring; this CLI handles gpt-5-prose
6-pillar posts for Twitter/TikTok/Substack/YouTube.

Usage:
    python viral_gen_pass53.py --topic "your topic" --platform twitter --n 5
    python viral_gen_pass53.py --batch  # runs pre-reg 20-candidate test
"""

import argparse, json, os, sys, datetime, pathlib
from typing import Dict, List

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ai_integrations import OpenAIIntegration

PROMPT_DIR = pathlib.Path(__file__).parent / "analyses" / "pass53_t51_v1_viral_mvp" / "prompts"
OUTPUT_DIR = pathlib.Path(__file__).parent / "viral_outputs"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

PILLARS = ["hook", "frame", "payload", "bridge", "action", "tag"]


def load_prompt(pillar: str) -> str:
    return (PROMPT_DIR / f"pillar_{pillar}.txt").read_text()


def generate_pillar(client: OpenAIIntegration, pillar: str, context: Dict[str, str]) -> str:
    """Generate one pillar's content via gpt-5."""
    template = load_prompt(pillar)
    prompt = template.format(**{k: context.get(k, "") for k in ["topic", "platform", "hook", "frame", "payload", "bridge", "draft"]})
    return client.analyze(prompt).strip()


def generate_candidate(client: OpenAIIntegration, topic: str, platform: str) -> Dict[str, str]:
    """Generate one 6-pillar candidate post."""
    ctx = {"topic": topic, "platform": platform}
    ctx["hook"] = generate_pillar(client, "hook", ctx)
    ctx["frame"] = generate_pillar(client, "frame", ctx)
    ctx["payload"] = generate_pillar(client, "payload", ctx)
    ctx["bridge"] = generate_pillar(client, "bridge", ctx)
    ctx["action"] = generate_pillar(client, "action", ctx)
    ctx["draft"] = f"{ctx['hook']}\n\n{ctx['frame']}\n\n{ctx['payload']}\n\n{ctx['bridge']}\n\n{ctx['action']}"
    ctx["tag"] = generate_pillar(client, "tag", ctx)
    return ctx


JUDGE_PROMPT = """You are a rigorous content reviewer scoring a viral-content candidate against a 6-pillar rubric.

Score each pillar 0-3:
  0 = absent or broken
  1 = present but weak
  2 = solid
  3 = excellent

Also flag:
  factual_errors (true/false): does the payload contain any fabricated stats or false claims?
  bait_and_switch (true/false): does the hook misrepresent what the payload actually delivers?
  all_six_pillars_present (true/false): are all 6 sections substantively present?

Minimum-quality threshold (per pre-reg): the candidate PASSES if:
  - all_six_pillars_present = true
  - factual_errors = false  
  - bait_and_switch = false
  - hook_score >= 2 (non-trivial hook)
  - sum of all 6 pillar scores >= 12 (avg 2.0)

Output strict JSON:
{{
  "hook_score": int,
  "frame_score": int,
  "payload_score": int,
  "bridge_score": int,
  "action_score": int,
  "tag_score": int,
  "total_score": int,
  "factual_errors": bool,
  "bait_and_switch": bool,
  "all_six_pillars_present": bool,
  "passes_min_quality": bool,
  "rationale": "one-sentence explanation"
}}

CANDIDATE:
Topic: {topic}
Platform: {platform}
Hook: {hook}
Frame: {frame}
Payload: {payload}
Bridge: {bridge}
Action: {action}
Tag: {tag}
"""


def judge_candidate(client: OpenAIIntegration, candidate: Dict[str, str]) -> Dict:
    """Score one candidate via gpt-5-as-judge."""
    prompt = JUDGE_PROMPT.format(**candidate)
    raw = client.analyze(prompt, system_prompt="You are a strict content reviewer. Output STRICT JSON only, no prose.").strip()
    # Strip markdown fences if present
    if raw.startswith("```"):
        raw = raw.split("```")[1]
        if raw.startswith("json"):
            raw = raw[4:]
    try:
        return json.loads(raw.strip())
    except json.JSONDecodeError as e:
        return {"parse_error": str(e), "raw": raw}


def run_session(topic: str, platform: str, n: int = 5, incremental_path: pathlib.Path = None) -> List[Dict]:
    """Generate n candidates for one (topic, platform) pair and score each.
    If incremental_path provided, appends each completed candidate immediately
    so partial results survive interruption."""
    client = OpenAIIntegration()
    results = []
    for i in range(n):
        print(f"  generating candidate {i+1}/{n} for ({topic[:40]}, {platform})...", flush=True)
        cand = generate_candidate(client, topic, platform)
        print(f"  judging candidate {i+1}/{n}...", flush=True)
        score = judge_candidate(client, cand)
        rec = {"candidate": cand, "score": score, "topic": topic, "platform": platform}
        results.append(rec)
        if incremental_path is not None:
            with open(incremental_path, "a") as f:
                f.write(json.dumps(rec) + "\n")
            print(f"  -> appended candidate {i+1} to {incremental_path.name}", flush=True)
    return results


def persist(results: List[Dict], tag: str):
    date = datetime.datetime.now().strftime("%Y-%m-%d_%H%M%S")
    safe_tag = tag.replace(" ", "_").replace("/", "_")[:60]
    path = OUTPUT_DIR / f"{date}_{safe_tag}.jsonl"
    with open(path, "w") as f:
        for r in results:
            f.write(json.dumps(r) + "\n")
    print(f"Saved {len(results)} candidates to {path}")
    return path


PRE_REG_BATCH = [
    ("The metabolic case for high-protein over high-fat diets", "twitter"),
    ("Why most meditation apps don't actually reduce anxiety long-term", "substack"),
    ("The one cognitive bias that explains most investment losses", "tiktok"),
    ("Why ankle flexibility predicts squat depth more than hip mobility", "youtube"),
]


def run_pre_reg_batch():
    """Pre-reg 20-candidate test: 4 topics × 5 candidates each."""
    all_results = []
    for topic, platform in PRE_REG_BATCH:
        print(f"\n=== Topic: {topic[:60]} ({platform}) ===")
        results = run_session(topic, platform, n=5)
        for r in results:
            r["topic"] = topic
            r["platform"] = platform
        all_results.extend(results)
    persist(all_results, "pre_reg_batch")
    summary = summarize_batch(all_results)
    with open(OUTPUT_DIR / "pre_reg_summary.json", "w") as f:
        json.dump(summary, f, indent=2)
    print("\n=== PRE-REG SUMMARY ===")
    print(json.dumps(summary, indent=2))
    return summary


def summarize_batch(results: List[Dict]) -> Dict:
    n = len(results)
    n_passes = sum(1 for r in results if r.get("score", {}).get("passes_min_quality"))
    n_parse_errors = sum(1 for r in results if "parse_error" in r.get("score", {}))
    n_factual_errors = sum(1 for r in results if r.get("score", {}).get("factual_errors"))
    n_bait = sum(1 for r in results if r.get("score", {}).get("bait_and_switch"))
    n_all_pillars = sum(1 for r in results if r.get("score", {}).get("all_six_pillars_present"))
    valid_scores = [r["score"]["total_score"] for r in results if isinstance(r.get("score", {}).get("total_score"), int)]
    return {
        "n_candidates": n,
        "n_passes_min_quality": n_passes,
        "pass_rate": n_passes / n if n > 0 else 0,
        "pre_reg_threshold": 0.60,
        "verdict": "CONFIRM" if (n > 0 and n_passes / n >= 0.60) else "DISCONFIRM",
        "n_parse_errors": n_parse_errors,
        "n_factual_errors_flagged": n_factual_errors,
        "n_bait_and_switch_flagged": n_bait,
        "n_all_six_pillars_present": n_all_pillars,
        "mean_total_score": sum(valid_scores) / len(valid_scores) if valid_scores else 0,
        "max_total_score": max(valid_scores) if valid_scores else 0,
        "min_total_score": min(valid_scores) if valid_scores else 0,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--topic", help="Content topic")
    ap.add_argument("--platform", default="twitter", choices=["twitter", "tiktok", "substack", "youtube"])
    ap.add_argument("--n", type=int, default=5, help="Number of candidates")
    ap.add_argument("--batch", action="store_true", help="Run pre-reg 4-topic × 5-candidate batch")
    args = ap.parse_args()
    if args.batch:
        run_pre_reg_batch()
    elif args.topic:
        date = datetime.datetime.now().strftime("%Y-%m-%d_%H%M%S")
        safe = args.topic.replace(" ", "_").replace("/", "_")[:50]
        inc_path = OUTPUT_DIR / f"{date}_{safe}_INCREMENTAL.jsonl"
        results = run_session(args.topic, args.platform, n=args.n, incremental_path=inc_path)
        persist(results, args.topic)
        for r in results:
            print(json.dumps(r["score"], indent=2))
    else:
        ap.print_help()


if __name__ == "__main__":
    main()
