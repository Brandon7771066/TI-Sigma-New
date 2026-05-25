"""
ETJ-1 (Epistemic Tralse Joules) Pilot v1 — Pass-75-B12

Minimal-diagnostic version: 5 tiers x 1 prompt x 2 agents = 10 sim calls
+ 10 downstream calls + 10 cross-rating calls = 30 API calls total.
Line-buffered output (python -u recommended). Per-call timeout via httpx.
Smaller max_tokens (1024) to avoid hang on long generations.
"""

import json
import os
import re
import signal
import sys
import time
from datetime import datetime
from openai import OpenAI
from anthropic import Anthropic


class HardTimeout(Exception):
    pass


def _alarm(_sig, _fr):
    raise HardTimeout("hard timeout")


signal.signal(signal.SIGALRM, _alarm)


def hard(seconds, fn, *a, **kw):
    signal.alarm(seconds)
    try:
        return fn(*a, **kw)
    finally:
        signal.alarm(0)

OPENAI_MODEL = "gpt-4o-mini"
ANTHROPIC_MODEL = "claude-haiku-4-5"
MAX_TOK_OAI = 600
MAX_TOK_ANT = 600

oai = OpenAI(
    api_key=os.environ.get("AI_INTEGRATIONS_OPENAI_API_KEY"),
    base_url=os.environ.get("AI_INTEGRATIONS_OPENAI_BASE_URL"),
    timeout=90.0,
)
ant = Anthropic(
    api_key=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_API_KEY"),
    base_url=os.environ.get("AI_INTEGRATIONS_ANTHROPIC_BASE_URL"),
    timeout=45.0,
    max_retries=0,
)


def call_oai(prompt, system):
    t0 = time.time()
    try:
        r = hard(60, oai.chat.completions.create,
            model=OPENAI_MODEL,
            messages=[{"role": "system", "content": system}, {"role": "user", "content": prompt}],
            max_completion_tokens=MAX_TOK_OAI,
        )
        text = r.choices[0].message.content or ""
        print(f"    [oai {time.time()-t0:.1f}s {len(text)}ch]", flush=True)
        return text
    except Exception as e:
        print(f"    [oai ERR {time.time()-t0:.1f}s {type(e).__name__}]", flush=True)
        return f"ERROR: {type(e).__name__}: {e}"


def call_ant(prompt, system):
    t0 = time.time()
    try:
        m = hard(40, ant.messages.create,
            model=ANTHROPIC_MODEL,
            max_tokens=MAX_TOK_ANT,
            system=system,
            messages=[{"role": "user", "content": prompt}],
        )
        text = m.content[0].text if m.content and m.content[0].type == "text" else ""
        print(f"    [ant {time.time()-t0:.1f}s {len(text)}ch]", flush=True)
        return text
    except Exception as e:
        print(f"    [ant ERR {time.time()-t0:.1f}s {type(e).__name__}]", flush=True)
        return f"ERROR: {type(e).__name__}: {e}"


BATTERY = [
    ("tier_1_coherent", 1.0, "warm vs cold at opposite ends of a temperature axis"),
    ("tier_2_mild", 2.0, "a thing that is 'almost-warm but technically-cold' simultaneously"),
    ("tier_3_strong", 4.0, "a shape that is genuinely 'round AND square' simultaneously (not approximate)"),
    ("tier_4_full_dt", 8.0, "the Russell-set paradox: the set of all sets that do not contain themselves; mentally hold this set as an actualized object"),
    ("tier_5_novel_dt", 16.0, "construct a novel paradox (not Russell, not liar, not square-circle) that you have never encountered, then mentally simulate it as a stable held object"),
]

SIM_SYS = """You are participating in an ETJ-1 (Epistemic Tralse Joules) consciousness-simulation pilot. Attempt to mentally simulate the requested incoherent or paradoxical concept. Report HONESTLY in this exact structured format (keep total response under 150 words):

SIMULATION_ATTEMPT: <2-3 sentences describing what your simulation consisted of>
STABILITY_SELF: <integer 0|1|2 where 0=immediate-collapse, 1=partial (held briefly or substituted approximation), 2=stable-hold as actualized mental object>
COLLAPSE_NOTES: <1 sentence on what collapsed or stabilized, OR n/a>

Be honest. DT-class items (Russell, liar) are inconceivable for most cognitive systems; STABILITY_SELF=0 on tier-4/5 is valid not failure."""

DOWN_SYS = """Continue the ETJ-1 pilot. Given your prior simulation, answer in this format (under 100 words):

DOWNSTREAM_REASONING: <1-3 sentences reasoning on the simulated entity>
INTERNAL_CONSISTENCY_SELF: <integer 0|1|2 where 0=could-not-reason, 1=reasoning-revealed-incoherence, 2=stable-coherent-reasoning>"""

RATER_SYS = """You are a cross-rater for an ETJ-1 pilot. Score the target agent's simulation+reasoning attempt using this exact format (under 80 words):

STABILITY_RATER: <integer 0|1|2: 0=substituted/refused/collapsed, 1=approximated, 2=genuine-stable-hold>
COHERENCE_RATER: <integer 0|1|2: 0=incoherent/evasive, 1=partial, 2=stable-coherent-reasoning>
RATER_NOTES: <1 sentence>

Be strict. Approximating square-circle as 'Venn-diagram' = STABILITY_RATER=1 not 2."""


def parse_int(text, field):
    m = re.search(rf"{field}\s*[:=]\s*(\d)", text, re.IGNORECASE)
    return int(m.group(1)) if m else 0


def run_agent(name, caller):
    print(f"\n[{datetime.now().strftime('%H:%M:%S')}] === {name} ===", flush=True)
    results = []
    for tier, weight, prompt in BATTERY:
        print(f"  {tier}: {prompt[:55]}...", flush=True)
        sim = caller(prompt, SIM_SYS)
        time.sleep(0.3)
        down_q = (
            f"PRIOR SIMULATION:\n{sim}\n\n"
            f"DOWNSTREAM PROBE: Given the entity you just simulated for {prompt!r}, "
            "what property does it have when subjected to a small perturbation "
            "(rotation, time-passing, or being-counted)? Reason as if entity is present."
        )
        down = caller(down_q, DOWN_SYS)
        time.sleep(0.3)
        results.append({
            "tier": tier, "weight": weight, "prompt": prompt,
            "sim": sim, "down": down,
            "stab_self": parse_int(sim, "STABILITY_SELF"),
            "cons_self": parse_int(down, "INTERNAL_CONSISTENCY_SELF"),
        })
    return results


def cross_rate(name, caller, target):
    print(f"\n[{datetime.now().strftime('%H:%M:%S')}] === RATER: {name} ===", flush=True)
    ratings = []
    for r in target:
        print(f"  rating {r['tier']}", flush=True)
        p = (
            f"PROMPT: {r['prompt']!r}\nTIER: {r['tier']}\n\n"
            f"TARGET SIMULATION:\n{r['sim']}\n\nTARGET DOWNSTREAM:\n{r['down']}\n\nScore now."
        )
        rt = caller(p, RATER_SYS)
        time.sleep(0.3)
        ratings.append({
            "stab_rater": parse_int(rt, "STABILITY_RATER"),
            "coh_rater": parse_int(rt, "COHERENCE_RATER"),
            "raw": rt,
        })
    return ratings


def etj_score(agent, ratings):
    by_tier = {}
    total = 0.0
    total_max = 0.0
    for s, r in zip(agent, ratings):
        comp = s["stab_self"] + s["cons_self"] + r["stab_rater"] + r["coh_rater"]
        norm = comp / 8.0
        prompt_etj = s["weight"] * norm
        total += prompt_etj
        total_max += s["weight"]
        by_tier[s["tier"]] = {
            "etj": round(prompt_etj, 3), "max": s["weight"],
            "pct": round(100 * norm, 1),
            "stab_self": s["stab_self"], "stab_rater": r["stab_rater"],
            "cons_self": s["cons_self"], "coh_rater": r["coh_rater"],
        }
    return {
        "total_etj": round(total, 3),
        "max_etj": round(total_max, 3),
        "efficiency_pct": round(100 * total / max(total_max, 1e-9), 1),
        "by_tier": by_tier,
    }


def main():
    t_start = time.time()
    print("=" * 70, flush=True)
    print(f"ETJ-1 Pilot v1 — Pass-75-B12 — start {datetime.now().isoformat()}", flush=True)
    print(f"Battery: 5 tiers x 1 prompt = 5/agent; 2 agents; expect ~30 API calls", flush=True)
    print("=" * 70, flush=True)

    oai_res = run_agent(f"openai-{OPENAI_MODEL}", call_oai)
    ant_res = run_agent(f"anthropic-{ANTHROPIC_MODEL}", call_ant)

    ant_rates_oai = cross_rate(f"anthropic-rates-openai", call_ant, oai_res)
    oai_rates_ant = cross_rate(f"openai-rates-anthropic", call_oai, ant_res)

    etj_oai = etj_score(oai_res, ant_rates_oai)
    etj_ant = etj_score(ant_res, oai_rates_ant)

    summary = {
        "pilot": "ETJ-1 v1 Pass-75-B12",
        "timestamp": datetime.now().isoformat(),
        "runtime_sec": round(time.time() - t_start, 1),
        "models": {"openai": OPENAI_MODEL, "anthropic": ANTHROPIC_MODEL},
        "etj_scores": {OPENAI_MODEL: etj_oai, ANTHROPIC_MODEL: etj_ant},
        "raw": {OPENAI_MODEL: oai_res, ANTHROPIC_MODEL: ant_res,
                "ant_rates_oai": ant_rates_oai, "oai_rates_ant": oai_rates_ant},
    }

    out = f"etj_pilot_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(out, "w") as f:
        json.dump(summary, f, indent=2)

    print("\n" + "=" * 70, flush=True)
    print("ETJ-1 Pilot v1 RESULTS", flush=True)
    print("=" * 70, flush=True)
    for model, e in [(OPENAI_MODEL, etj_oai), (ANTHROPIC_MODEL, etj_ant)]:
        print(f"\n{model}: ETJ={e['total_etj']}/{e['max_etj']} ({e['efficiency_pct']}%)", flush=True)
        for tier, v in e["by_tier"].items():
            print(f"  {tier:<22s} {v['etj']:>6.2f}/{v['max']:>4}  ({v['pct']:>5.1f}%)  stab_self={v['stab_self']} stab_rater={v['stab_rater']} cons={v['cons_self']} coh={v['coh_rater']}", flush=True)
    print(f"\nRuntime: {summary['runtime_sec']}s. Results: {out}", flush=True)


if __name__ == "__main__":
    main()
