"""TI-Sigma Crystal (TSC) Consciousness Hamiltonian — self-contained port.

Faithful to the corpus implementation:
  - 57-vertex crystal (origin + 7 rings x 8 layers), radii = PRIMARY CONSTANTS,
    angle = l*pi/4 + (r-1)*pi/PHI       (hypercomputer/tsc.py)
  - H_TSC = H_hop + H_onsite + H_gile    (hypercomputer/hamiltonian.py)
        H_hop    = -J * A
        H_onsite =  U * diag(|alpha|^2)
        H_gile   =  mu * diag(ring_weights), ring_weights =
                    [G, I, L, E, (G+I)/2, (L+E)/2, (G+I+L+E)/4], origin = 0
  - FULL PD: pd_real (degree, principal axis) + pd_imag (MI / Tralse axis) with
    canonical zone thresholds (analyses/pass77_b108 zone()).
  - TI-Sigma Graph: GILE-weighted attachment p(i,j)=min(1, kappa*g_i*g_j)
    (urb_735); we return algebraic connectivity (Fiedler) of its Laplacian.

Canonical GILE composite weights GILE_W = {G:ET, I:.25, L:.18, E:.15}
(lcc_virus_gile_inference.py, URB #576).
"""
import numpy as np

PHI   = (1.0 + np.sqrt(5.0)) / 2.0       # ~1.6180
C_TI  = 1.0 / (PHI * np.sqrt(2.0))       # Emerick constant ~0.4370
T_TI  = 1.0 - np.exp(-np.e)              # BEC threshold ~0.9340
ET    = np.sqrt(2.0) - 1.0              # Emerick threshold ~0.4142
E_TI  = np.e
PI_TI = np.pi
SQRT2 = np.sqrt(2.0)

RING_RADII = np.array([C_TI, T_TI, 1.0, SQRT2, PHI, E_TI, PI_TI])
N_RINGS, N_LAYERS = 7, 8
N_VERTICES = N_RINGS * N_LAYERS + 1       # 57

# canonical GILE composite weights (URB #576).
# E = Elegance (label updated from "Environment" 2026-06-16; the weight and its
# operationalization as aesthetic spectral purity are UNCHANGED — only the name is
# aligned to what E measures; "Environment" kept as a concise most-sacred-values gloss).
GILE_W = {"G": ET, "I": 0.25, "L": 0.18, "E": 0.15}

# PD zone thresholds (canonical; pass77_b108)
MI_CLIFF, LO_I, HI_I = -2.5, -2.0 / 3.0, 1.0 / 3.0


def _build_vertices():
    """Return (ring_of_vertex[57], radius_of_vertex[57], angle[57])."""
    ring = np.zeros(N_VERTICES, dtype=int)
    radius = np.zeros(N_VERTICES)
    angle = np.zeros(N_VERTICES)
    # origin = index 0 (ring 0, radius 0)
    for r in range(1, N_RINGS + 1):
        for l in range(N_LAYERS):
            idx = (r - 1) * N_LAYERS + l + 1
            ring[idx] = r
            radius[idx] = RING_RADII[r - 1]
            angle[idx] = (l * np.pi / 4.0 + (r - 1) * np.pi / PHI) % (2 * np.pi)
    return ring, radius, angle


def _build_adjacency(ring):
    """origin<->ring1; same ring adjacent layers (mod 8); adjacent rings same layer."""
    A = np.zeros((N_VERTICES, N_VERTICES))

    def rl(idx):
        if idx == 0:
            return 0, -1
        r = (idx - 1) // N_LAYERS + 1
        l = (idx - 1) % N_LAYERS
        return r, l

    for i in range(N_VERTICES):
        ri, li = rl(i)
        for j in range(i + 1, N_VERTICES):
            rj, lj = rl(j)
            edge = False
            if (ri == 0 and rj == 1) or (rj == 0 and ri == 1):
                edge = True
            elif ri == rj and ri > 0:
                dl = abs(li - lj)
                if dl == 1 or dl == N_LAYERS - 1:
                    edge = True
            elif li == lj and abs(ri - rj) == 1 and ri > 0 and rj > 0:
                edge = True
            if edge:
                A[i, j] = A[j, i] = 1.0
    return A

RING = None
RADIUS = None
ANGLE = None
ADJ = None


def _ensure_crystal():
    global RING, RADIUS, ANGLE, ADJ
    if ADJ is None:
        RING, RADIUS, ANGLE = _build_vertices()
        ADJ = _build_adjacency(RING)


def gile_ring_weights(G, I, L, E):
    """Per-vertex GILE chemical potential (ring_weights expanded to 57, origin=0)."""
    _ensure_crystal()
    rw = [G, I, L, E, (G + I) / 2.0, (L + E) / 2.0, (G + I + L + E) / 4.0]
    mu = np.zeros(N_VERTICES)
    for v in range(1, N_VERTICES):
        mu[v] = rw[RING[v] - 1]
    return mu


def gile_composite(G, I, L, E):
    return (GILE_W["G"] * G + GILE_W["I"] * I + GILE_W["L"] * L + GILE_W["E"] * E)


def pd_full(gile_comp, hem_d2):
    """FULL PD = (pd_real, pd_imag).
       pd_real (degree) = affine map 5*(comp-0.5) into the PD principal axis
                          (mirrors the canonical Riemann affine 5*(sigma-0.5));
       pd_imag (modality / MI-Tralse axis) = HEM-D2 contradiction/Tralse ratio.
    """
    pd_real = 5.0 * (float(gile_comp) - 0.5)
    pd_imag = float(hem_d2)
    return pd_real, pd_imag


def pd_zone(v):
    """Canonical MR truth-label zone of a scalar PD-real value -> int code."""
    if v <= MI_CLIFF:
        return 0   # MI
    if v <= LO_I:
        return 1   # F
    if v <= HI_I:
        return 2   # I
    return 3       # T


def hamiltonian_spectrum_features(alpha, G, I, L, E, J=1.0, U=0.5, mu=1.0):
    """Build H_TSC for this window's quantum state and return spectral descriptors.

    alpha : length-57 nonneg amplitudes (the window projected onto crystal vertices).
            The signal enters H_onsite (window-specific localization); GILE enters
            H_gile (window-specific chemical potential). H_hop is the fixed crystal.

    Returns a dict of principled, deterministic scalar features.
    """
    _ensure_crystal()
    a = np.asarray(alpha, dtype=float).reshape(-1)
    if a.shape[0] != N_VERTICES:
        # tile / trim to 57
        rep = int(np.ceil(N_VERTICES / max(1, a.shape[0])))
        a = np.tile(a, rep)[:N_VERTICES]
    H = (-J * ADJ
         + np.diag(U * a ** 2)
         + np.diag(mu * gile_ring_weights(G, I, L, E)))
    w, V = np.linalg.eigh(H)               # ascending eigenvalues
    ground = V[:, 0]
    p = ground ** 2
    p = p / (p.sum() + 1e-12)
    ipr = float((p ** 2).sum())            # inverse participation ratio (localization)
    # ring-energy of the ground state (which crystal ring the state localizes in)
    ring_energy = np.zeros(N_RINGS)
    for v in range(1, N_VERTICES):
        ring_energy[RING[v] - 1] += p[v]
    re = ring_energy / (ring_energy.sum() + 1e-12)
    ring_entropy = float(-(re * np.log(re + 1e-12)).sum())
    dom_ring = float(np.argmax(re))
    return {
        "lambda0": float(w[0]),
        "gap": float(w[1] - w[0]),
        "lam_mean": float(w.mean()),
        "lam_std": float(w.std()),
        "bandwidth": float(w[-1] - w[0]),
        "ground_ipr": ipr,
        "ring_entropy": ring_entropy,
        "dom_ring": dom_ring,
    }


def gile_graph_fiedler(G, I, L, E, kappa=1.0):
    """TI-Sigma Graph: GILE-weighted attachment on the crystal edges; return the
    algebraic connectivity (Fiedler value) and weighted edge density."""
    _ensure_crystal()
    g = gile_ring_weights(G, I, L, E)
    g = np.clip(g, 0.0, None)
    W = np.minimum(1.0, kappa * np.outer(g, g)) * ADJ
    d = W.sum(1)
    Lap = np.diag(d) - W
    ev = np.linalg.eigvalsh(Lap)
    fiedler = float(ev[1]) if ev.shape[0] > 1 else 0.0
    return fiedler, float(W.sum() / 2.0)
