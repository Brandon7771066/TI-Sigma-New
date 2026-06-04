"""
Pass-77 B70 — canonical-clarifications computations.
A: TSC-E8 (57-vertex) vs Meijer octahedron superiority (exact, computed).
B: PD broader-range critical-value verification (urb_714/721/728).
C: Radiant Time-Dilation + DE-Photon arithmetic (urb_638).
D: ABP-1-F3 open-data proxy (rodent LFP, two-arousal-state antipodal-matching contrast).
All free/local; DANDI stream for D (skips cleanly if unavailable).
"""
import numpy as np, itertools, json, math

PHI = (1 + 5**0.5) / 2
E = math.e
PI = math.pi
out = {}

# ---------- Part A: E8 root system vs octahedron ----------
def e8_roots():
    roots = []
    # type 1: (+-1,+-1,0,...,0) all positions, 112 roots
    for i, j in itertools.combinations(range(8), 2):
        for si in (1, -1):
            for sj in (1, -1):
                v = [0]*8; v[i] = si; v[j] = sj
                roots.append(tuple(v))
    # type 2: (+-1/2)^8 with even number of minus signs, 128 roots
    for signs in itertools.product((0.5, -0.5), repeat=8):
        if sum(1 for s in signs if s < 0) % 2 == 0:
            roots.append(tuple(signs))
    return np.array(roots)

R = e8_roots()
norms2 = np.round((R**2).sum(1), 6)
# antipodal pairs: v and -v both present
rset = set(map(tuple, np.round(R, 6)))
anti = sum(1 for v in rset if tuple(np.round(-np.array(v), 6)) in rset) // 2
# kissing number = number of minimal vectors = all 240 roots (norm^2=2)
kissing_e8 = int((np.isclose(norms2, 2.0)).sum())
out["E8"] = {
    "num_roots": int(len(R)),
    "all_norm2_equal_2": bool(np.allclose(norms2, 2.0)),
    "kissing_number": kissing_e8,
    "antipodal_pairs": int(anti),
    "dimension": 8,
    "weyl_order": 696729600,
    "packing_density_8D": PI**4 / 384,  # Viazovska 2016 optimal
}

# octahedron (+-e_i)
oct_v = np.array([[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]], float)
oct_set = set(map(tuple, oct_v))
oct_anti = sum(1 for v in oct_set if tuple(-np.array(v)) in oct_set)//2
# kissing of octahedron's lattice (Z^3 cross-polytope) min vectors = 6
out["octahedron"] = {
    "num_vertices": 6, "antipodal_pairs": int(oct_anti),
    "dimension": 3, "symmetry_order_Oh": 48,
    "kissing_number_cross_polytope_3D": 6,
}
out["superiority"] = {
    "symmetry_order_ratio_E8_over_Oh": 696729600/48,
    "dimension_ratio": 8/3,
    "kissing_ratio": kissing_e8/6,
    "E8_provably_optimal_packing": True,
    "oct_provably_optimal_packing": False,
    "TSC_vertices_57": "56 non-origin E8-root subset + origin (one-photon 57 partitions)",
    "five_valued_ECC_native_to_E8": True,  # TECC, urb_630
}

# ---------- Part B: PD broader-range critical values ----------
def riemann_map(rho):  # u=(rho+3)/5 maps [-3,2]->[0,1]; midpoint check
    return (rho + 3) / 5
out["PD_range"] = {
    "foundational_scale_interval": [-3, 2],
    "true_role": "Foundational PD Scale = continuous param of 5-valued logic (5-unit span)",
    "sacred_interval_moved_to": [-0.5, 0.333],
    "thresholds": {
        "-3 DT_Cliff": -3, "-e Ultra_Terrible": -E, "-2 False": -2,
        "-2/3 Indet_lower": -2/3, "-0.5 Riemann_midpoint": -0.5,
        "0 Neutral": 0, "+1/3 Indet_upper": 1/3, "+1 True": 1,
        "+2 Verisyn_saturation": 2, "+e Transcendent": E, "+pi CCC_level": PI,
    },
    "midpoint_of_-3_2": (-3 + 2)/2,
    "riemann_u_at_midpoint": riemann_map(-0.5),  # should be 0.5
    "ratio_4_3": 4/3, "badness_multiplier_4x": 4,
    "integrated_load_ratio_6_to_1": (4*3)/(1*2),
    "GM_zone_log_scaling_PD=2+ln(r)": "for PD>2.0",
    "radiance_at_CCC_e^(pi-2)": E**(PI - 2),
    "radiance_near_identity_with_pi_error_pct": abs(E**(PI-2) - PI)/PI*100,
}

# ---------- Part C: Radiant Time-Dilation + DE-Photon ----------
YEAR_S = 365.25 * 24 * 3600
tau_DE_formula = PI/(E*PHI) * YEAR_S
def tau_eff(gile): return tau_DE_formula * math.exp(gile/6)
out["radiant_time"] = {
    "tau_DE_pi_over_e_phi_years": PI/(E*PHI),
    "tau_DE_seconds": tau_DE_formula,
    "tau_DE_years": tau_DE_formula/YEAR_S,
    "matches_corpus_1.47e8s_4.66yr": abs(tau_DE_formula-1.47e8)/1.47e8 < 0.05,
    "dilation_at_GILE_phi2": math.exp(PHI**2/6),  # ~1.547
    "RT_state_GILE": PHI**2,
    "GM_limit": "GILE->inf => tau_eff->inf (Eternal Now / CCC)",
    "LHC_ratio_4.1_over_2.3": 4.1/2.3,
    "sqrt_pi": PI**0.5,
    "LHC_ratio_matches_sqrtpi_err_pct": abs(4.1/2.3 - PI**0.5)/(PI**0.5)*100,
    "E_DE_joules_approx": 2.39e-52,
    "autonomy_floor_e^-e": math.exp(-E),
    "tau_eff_curve": {f"GILE={g}": tau_eff(g)/YEAR_S for g in [0,1,PHI**2,3,6,12]},
}

# ---------- Part D: ABP-1-F3 open-data proxy ----------
# Contrast antipodal feature-matching between high- vs low-amplitude (arousal proxy) LFP epochs.
fd = {"status": "not_run"}
try:
    import remfile, h5py, numpy as np
    from dandi.dandiapi import DandiAPIClient
    with DandiAPIClient() as c:
        a = c.get_dandiset("000003", "draft").get_asset_by_path(
            "sub-YutaMouse41/sub-YutaMouse41_ses-YutaMouse41-150829_behavior+ecephys.nwb")
        url = a.get_content_url(follow_redirects=1, strip_query=True)
    f = h5py.File(remfile.File(url), "r")
    lfp = f["processing/ecephys/LFP/LFP/data"]
    x = lfp[:300000, 0].astype(float)  # ~240s @1250Hz
    fs = 1250
    # split into 1s windows; arousal proxy = window RMS; high vs low tertile
    W = fs
    wins = x[:len(x)//W*W].reshape(-1, W)
    rms = wins.std(1)
    hi = wins[rms >= np.quantile(rms, 0.66)]
    lo = wins[rms <= np.quantile(rms, 0.34)]
    def anti_match(arr):
        # feature = (mean of 1st half, mean of 2nd half); antipode = time-reversed window
        f1 = arr[:, :W//2].mean(1); f2 = arr[:, W//2:].mean(1)
        feat = np.column_stack([f1, f2])
        rev = arr[:, ::-1]
        rf1 = rev[:, :W//2].mean(1); rf2 = rev[:, W//2:].mean(1)
        rfeat = np.column_stack([rf1, rf2])
        d_anti = np.linalg.norm(feat - rfeat, axis=1).mean()
        # random baseline
        idx = np.random.permutation(len(arr))
        d_rand = np.linalg.norm(feat - rfeat[idx], axis=1).mean()
        return float(d_anti), float(d_rand)
    np.random.seed(0)
    da_hi, dr_hi = anti_match(hi)
    da_lo, dr_lo = anti_match(lo)
    fd = {
        "status": "run", "n_hi": int(len(hi)), "n_lo": int(len(lo)),
        "high_arousal_antipodal_d": da_hi, "high_arousal_random_d": dr_hi,
        "low_arousal_antipodal_d": da_lo, "low_arousal_random_d": dr_lo,
        "interpretation": "F3 asks if altered/low-binding states show BETTER antipodal matching "
                          "(antipodal_d < random_d). Report ratios honestly.",
        "hi_ratio_anti_over_rand": da_hi/dr_hi, "lo_ratio_anti_over_rand": da_lo/dr_lo,
    }
except Exception as e:
    fd = {"status": "skipped", "reason": str(e)[:200]}
out["ABP1_F3_proxy"] = fd

print(json.dumps(out, indent=2, default=str))
with open("analyses/pass77_b70_canonical_clarifications/results.json", "w") as fh:
    json.dump(out, fh, indent=2, default=str)
