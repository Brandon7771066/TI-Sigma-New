"""
Pass-77 B68: Meijer's octahedral / scale-invariant-acoustic framework vs the TI Sigma
Crystal (TIC) and TI Sigma Graph (TIG).

PART A (geometry/topology, exact): octahedron graph vs TIG (15-edge spec, URB #735) vs
  TSC-E8 (57-vertex). Compute clique number, EXACT chromatic number, diameter, adjacency
  spectrum. Direct #69 check of URB #735's claim chromatic(TIG)=3.
PART B (Meijer's scale-invariant acoustic power spectrum, real data): fit P(f) ~ 1/f^beta
  on real Mendi fNIRS (local) and real rodent hippocampal LFP (DANDI stream). Pink noise
  beta~1, Brownian beta~2; neural aperiodic slope typically 1-3. Tests whether the TI
  substrate data exhibits the scale-invariant (power-law) spectrum Meijer claims is universal.
"""
import json, time, itertools
import numpy as np
OUT = "analyses/pass77_b68_meijer_octahedron_vs_ti"
t0 = time.time()
out = {"pass": "77-B68"}

# ---------- PART A: geometry ----------
def adj_from_edges(nodes, edges):
    idx = {n: k for k, n in enumerate(nodes)}; n = len(nodes)
    A = np.zeros((n, n))
    for a, b in edges:
        A[idx[a], idx[b]] = A[idx[b], idx[a]] = 1
    return A

def clique_number(A):
    n = len(A); best = 1
    nodes = list(range(n))
    # brute small-graph max clique
    for r in range(n, 1, -1):
        if r <= best: break
        for comb in itertools.combinations(nodes, r):
            if all(A[i, j] for i, j in itertools.combinations(comb, 2)):
                return r
    return best

def chromatic_number(A):
    n = len(A)
    adj = [set(np.where(A[i])[0]) for i in range(n)]
    def colorable(k):
        color = [-1]*n
        def bt(v):
            if v == n: return True
            for c in range(k):
                if all(color[u] != c for u in adj[v]):
                    color[v] = c
                    if bt(v+1): return True
                    color[v] = -1
            return False
        return bt(0)
    lo = clique_number(A)
    for k in range(lo, n+1):
        if colorable(k): return k
    return n

def diameter(A):
    n = len(A); INF = 10**9
    D = np.where(A > 0, 1, INF); np.fill_diagonal(D, 0)
    for k in range(n):
        D = np.minimum(D, D[:, [k]] + D[[k], :])
    return int(D[D < INF].max())

# octahedron = K_{2,2,2}: antipodal pairs (0,3),(1,4),(2,5) non-adjacent, all else adjacent
oct_nodes = list(range(6)); anti = {(0, 3), (1, 4), (2, 5)}
oct_edges = [(a, b) for a, b in itertools.combinations(oct_nodes, 2)
             if (a, b) not in anti and (b, a) not in anti]
Aoct = adj_from_edges(oct_nodes, oct_edges)

# TIG: 9 vertices, 15 edges (URB #735 sec.2)
tig_nodes = ["0", "1", "i", "r2", "e", "phi", "pi", "C", "T"]
tig_edges = [("0", "1"), ("0", "i"), ("1", "i"),                       # Boolean (3)
             ("1", "r2"), ("i", "r2"), ("0", "r2"),                    # Pythagoras (3)
             ("0", "e"), ("0", "phi"), ("0", "pi"), ("1", "phi"), ("e", "pi"),  # growth (5)
             ("0", "C"), ("0", "T"), ("1", "C"), ("i", "T")]           # non-classical (4)
Atig = adj_from_edges(tig_nodes, tig_edges)

def summarize(name, A, V, E, F, symorder, dim, extra=""):
    spec = sorted(np.round(np.linalg.eigvalsh(A), 3).tolist(), reverse=True)
    deg = A.sum(1).astype(int).tolist()
    return {"name": name, "V": V, "E": E, "F": F, "symmetry_group_order": symorder,
            "dimension": dim, "clique_number": clique_number(A),
            "chromatic_number": chromatic_number(A), "diameter": diameter(A),
            "degree_sequence": sorted(deg, reverse=True),
            "adjacency_spectrum": spec, "note": extra}

geo = {}
geo["octahedron"] = summarize("Octahedron (Meijer)", Aoct, 6, 12, 8, 48, 3,
                              "Platonic solid; group O_h order 48; self-dual to cube; graph=K_{2,2,2}")
geo["TIG"] = summarize("TI Sigma Graph (URB #735)", Atig, 9, 15, None, 1, 2,
                       "vertex '0' adjacent to all 8 others; {0,1,i,r2} induce K4")
geo["TSC_E8"] = {"name": "TSC-E8 (URB #627-630)", "V": 57, "E": "E8 root adjacency",
                 "F": None, "symmetry_group_order": 696729600, "dimension": 8,
                 "note": "origin + 56 E8 roots; Weyl(E8)=696,729,600; optimal 8D sphere packing (Viazovska)"}
out["geometry"] = geo
# URB #735 F2 check
out["urb735_F2_chromatic_check"] = {
    "claimed_chromatic": 3, "computed_chromatic": geo["TIG"]["chromatic_number"],
    "computed_clique": geo["TIG"]["clique_number"],
    "verdict": "CLAIM HOLDS" if geo["TIG"]["chromatic_number"] == 3 else
               "CLAIM REFUTED (#69) — TIG contains K4 => chromatic >= 4, not 3"}

# ---------- PART B: 1/f scale-invariance on real data ----------
def loglog_slope(x, fs, fmin, fmax):
    x = np.asarray(x, float); x = x - x.mean()
    f = np.fft.rfftfreq(len(x), 1/fs); P = (np.abs(np.fft.rfft(x))**2)
    m = (f >= fmin) & (f <= fmax) & (P > 0)
    if m.sum() < 8: return None
    lf, lp = np.log10(f[m]), np.log10(P[m])
    A = np.vstack([lf, np.ones_like(lf)]).T
    coef, *_ = np.linalg.lstsq(A, lp, rcond=None)
    beta = -coef[0]
    pred = A @ coef; ss = 1 - np.sum((lp-pred)**2)/np.sum((lp-lp.mean())**2)
    return {"beta": float(beta), "R2": float(ss), "n_freqs": int(m.sum()),
            "band_hz": [fmin, fmax]}

sca = {}
# Mendi fNIRS (local)
try:
    import csv
    vals, ts = [], []
    with open("data/mendi/sessions/session_2026-05-11T12-22-50_decoded.csv") as fh:
        for r in csv.DictReader(fh):
            try: vals.append(float(r["raw_value"])); ts.append(float(r["t_elapsed_s"]))
            except: pass
    fs_m = 1.0/np.median(np.diff(ts))
    sca["mendi_fnirs"] = {"fs_hz": round(fs_m, 3), "n": len(vals),
                          "fit": loglog_slope(vals, fs_m, 0.01, fs_m/2*0.9)}
except Exception as e:
    sca["mendi_fnirs"] = {"error": repr(e)}

# Rodent LFP (DANDI stream, reuse proven workaround)
try:
    import h5py, remfile, warnings; warnings.filterwarnings("ignore")
    from dandi.dandiapi import DandiAPIClient
    A_ = "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb"
    with DandiAPIClient() as c:
        s3 = c.get_dandiset("000003", "draft").get_asset_by_path(A_).get_content_url(follow_redirects=1, strip_query=True)
    h = h5py.File(remfile.File(url=s3), "r")
    d = h["processing/ecephys/LFP/LFP/data"]
    fs_r = 1250.0
    seg = np.asarray(d[int(4500*fs_r):int(4560*fs_r), 0], float)  # 60s, 1 channel, awake
    sca["rodent_lfp"] = {"fs_hz": fs_r, "n": len(seg), "fit": loglog_slope(seg, fs_r, 1, 300)}
except Exception as e:
    sca["rodent_lfp"] = {"error": repr(e)}

# pink/brown reference sanity
rng = np.random.default_rng(0)
white = rng.standard_normal(20000)
brown = np.cumsum(white)
sca["_ref_brown_noise"] = loglog_slope(brown, 100, 0.1, 40)
out["scale_invariance"] = sca

json.dump(out, open(f"{OUT}/results.json", "w"), indent=2)
print(json.dumps({"geometry": {k: {kk: v[kk] for kk in ("V", "E", "symmetry_group_order",
       "dimension", "clique_number", "chromatic_number", "diameter") if kk in v}
       for k, v in geo.items()},
       "urb735_F2": out["urb735_F2_chromatic_check"],
       "scale_invariance": {k: (v.get("fit") if isinstance(v, dict) else v) for k, v in sca.items()}},
      indent=2))
print(f"[{time.time()-t0:.0f}s] done")
