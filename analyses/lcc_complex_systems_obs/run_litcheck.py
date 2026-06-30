"""Verify REAL observational complex-systems literature for the LCC threshold-ladder paper.
Real cites only; explicitly flag where NO quantitative regime value exists at the LCC numbers."""
import json, os, requests

SYS = ("You are a rigorous complex-systems / network-neuroscience literature checker. "
       "Return ONLY real peer-reviewed sources with author-year and DOI/journal. "
       "Give concrete equations and numeric regime values WHERE THEY ACTUALLY EXIST. "
       "If a specific numeric coupling threshold or universal [0,1] value is NOT reported in the literature, "
       "say so EXPLICITLY ('no universal numeric threshold reported') rather than inventing one. "
       "Do not fabricate citations or DOIs.")

QUERIES = {
 "sync": (
  "Synchronization in coupled-oscillator / complex-systems theory. "
  "(1) Kuramoto model: define the order parameter r in [0,1] and the critical coupling K_c; partial vs global synchronization regimes. "
  "(2) Continuous (second-order) vs explosive (first-order / discontinuous / abrupt) synchronization transitions in networks — canonical refs and what causes the discontinuous jump. "
  "(3) Master stability function for synchronization stability. "
  "For each give author-year + DOI/journal. Is there any universal [0,1] coupling value at which sync onset/partial/near-complete happens, or is it system-specific?"
 ),
 "causality": (
  "Inferring DIRECTIONAL causality from observational time series, and how synchrony affects it. "
  "(1) Granger causality (Granger 1969); transfer entropy (Schreiber 2000); equivalence of Granger and transfer entropy for Gaussian variables (Barnett Barrett Seth 2009); phase slope index; convergent cross mapping (Sugihara 2012); dynamic causal modeling (Friston 2003). "
  "(2) The phenomenon that STRONG synchronization / generalized synchrony DEGRADES or BREAKS directional-causality detection (Granger and CCM failing as coupling -> full sync). Canonical refs and the precise statement. "
  "For each give author-year + DOI/journal. Is the breakdown of causal inference under strong synchrony an established result?"
 ),
 "brainnet": (
  "Brain network integration vs segregation and competition between networks (observational fMRI/EEG). "
  "(1) Anticorrelation between default-mode network and task-positive/dorsal-attention network (Fox 2005). "
  "(2) Metastability in brain dynamics (Tognoli & Kelso 2014; Deco/Jirsa; Shanahan chimera/metastable communities; Hellyer). "
  "(3) Structure-function coupling (Honey 2009); integration/segregation, modularity, network neuroscience (Bassett & Sporns 2017). "
  "For each give author-year + DOI/journal. Are there reported numeric coupling/correlation regime boundaries (e.g. on a [0,1] scale) for when networks integrate vs segregate, or are values system/method-specific?"
 ),
}

def ask(q):
    key = os.environ["PERPLEXITY_API_KEY"]
    payload = {"model": "sonar-pro",
               "messages": [{"role": "system", "content": SYS}, {"role": "user", "content": q}],
               "max_tokens": 2200, "temperature": 0.2}
    r = requests.post("https://api.perplexity.ai/chat/completions", json=payload,
                      headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"}, timeout=120)
    r.raise_for_status()
    j = r.json()
    return {"content": j["choices"][0]["message"]["content"],
            "citations": j.get("citations", []) or j.get("search_results", [])}

if __name__ == "__main__":
    out = {}
    for name, q in QUERIES.items():
        print(f"\n{'='*70}\n### {name}\n{'='*70}")
        try:
            res = ask(q)
            out[name] = res
            print(res["content"])
            print("\n--CITES--")
            for c in res["citations"][:20]:
                print(c if isinstance(c, str) else c.get("url", c))
        except Exception as e:
            out[name] = {"error": str(e)}
            print("ERROR", e)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "litcheck_raw.json"), "w") as f:
        json.dump(out, f, indent=2)
    print("\nSAVED litcheck_raw.json")
