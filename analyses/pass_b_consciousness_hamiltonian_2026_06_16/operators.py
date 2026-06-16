"""Retrieval operators compared in the Retrieval-Gap benchmark.

All operators share the SAME at-threshold resonance front-end and expose:
    fit(X, H, r)      X:(n,d) standardized features, H:(n,) labels, r:(n,1) resonance
    predict(X, r) -> (n,) predicted labels

P0  Passive resonance (baseline)        -- uses only the scalar resonance r
O1  Transformer cross-attention         -- numpy Q-K-V softmax readout
O2  Hopfield energy-descent             -- modern continuous Hopfield -> nearest attractor
O3  Reverse-osmosis (i-boundary)        -- conscious-pressure gated belief flux
O4  TI-Sigma Active Inference (UOP+i-Cell)
        GILE-weighted prior + LCC precision-weighting + Myrion-Resolution collapse
        + GTFE gap-closure (iterated free-energy / precision update)
Combos: ENSEMBLE (vote), O4XA (cross-attention prior feeding O4).
"""
import numpy as np

from features import C_EMERICK


def _softmax(z, axis=-1):
    z = z - np.max(z, axis=axis, keepdims=True)
    e = np.exp(z)
    return e / (np.sum(e, axis=axis, keepdims=True) + 1e-12)


def _onehot(H, K):
    Y = np.zeros((len(H), K))
    Y[np.arange(len(H)), H] = 1.0
    return Y


class _Base:
    name = "base"

    def __init__(self, n_states):
        self.K = n_states

    def fit(self, X, H, r):
        return self

    def predict(self, X, r):
        raise NotImplementedError


class Passive(_Base):
    name = "P0_passive_resonance"

    def fit(self, X, H, r):
        r = r.ravel()
        self.proto = np.array([r[H == c].mean() if np.any(H == c) else 0.0
                               for c in range(self.K)])
        return self

    def predict(self, X, r):
        r = r.ravel()
        d = np.abs(r[:, None] - self.proto[None, :])
        return np.argmin(d, axis=1)


class NearestCentroidMatched(_Base):
    """Matched-feature passive baseline: nearest class-centroid on the SAME rich
    feature vector the active operators see, but with NO active update / retrieval
    mechanism. Isolates 'active mechanism' from 'more features' (fairness control)."""
    name = "P0b_nearest_centroid_matched"

    def fit(self, X, H, r):
        self.means = np.array([X[H == c].mean(0) if np.any(H == c)
                               else np.zeros(X.shape[1]) for c in range(self.K)])
        return self

    def predict(self, X, r):
        d = np.linalg.norm(X[:, None, :] - self.means[None, :, :], axis=2)
        return np.argmin(d, axis=1)


class CrossAttention(_Base):
    name = "O1_cross_attention"

    def __init__(self, n_states, beta=4.0):
        super().__init__(n_states)
        self.beta = beta

    def fit(self, X, H, r):
        self.K_mem = X
        self.V_mem = _onehot(H, self.K)
        self.scale = self.beta / np.sqrt(X.shape[1] + 1e-12)
        return self

    def predict(self, X, r):
        scores = X @ self.K_mem.T * self.scale          # (nte, ntr)
        A = _softmax(scores, axis=1)
        post = A @ self.V_mem                             # (nte, K)
        return np.argmax(post, axis=1)

    def posterior(self, X):
        scores = X @ self.K_mem.T * self.scale
        return _softmax(scores, axis=1) @ self.V_mem


class Hopfield(_Base):
    name = "O2_hopfield_descent"

    def __init__(self, n_states, beta=2.0, iters=5):
        super().__init__(n_states)
        self.beta = beta
        self.iters = iters

    def fit(self, X, H, r):
        self.patterns = X                                 # stored memories
        self.H = H
        self.means = np.array([X[H == c].mean(0) if np.any(H == c)
                               else np.zeros(X.shape[1]) for c in range(self.K)])
        return self

    def predict(self, X, r):
        out = np.empty(len(X), dtype=int)
        Xp = self.patterns
        for i in range(len(X)):
            xi = X[i].copy()
            for _ in range(self.iters):            # modern Hopfield energy descent
                w = _softmax(self.beta * (Xp @ xi))
                xi = Xp.T @ w
            d = np.linalg.norm(self.means - xi[None, :], axis=1)
            out[i] = int(np.argmin(d))
        return out


class ReverseOsmosis(_Base):
    """i-boundary z = s + i*a : the imaginary channel a (active belief / 'conscious
    pressure') gates membrane permeability, pulling belief-consistent flux across
    while suppressing noise. Iterated until the boundary settles."""
    name = "O3_reverse_osmosis"

    def __init__(self, n_states, iters=6, pressure=1.5):
        super().__init__(n_states)
        self.iters = iters
        self.pressure = pressure

    def fit(self, X, H, r):
        self.means = np.array([X[H == c].mean(0) if np.any(H == c)
                               else np.zeros(X.shape[1]) for c in range(self.K)])
        self.var = np.array([X[H == c].var(0) + 1e-3 if np.any(H == c)
                             else np.ones(X.shape[1]) for c in range(self.K)])
        # base discriminability of each feature (separation / within-class scatter)
        between = self.means.var(0)
        within = self.var.mean(0)
        self.disc = between / (within + 1e-9)
        return self

    def predict(self, X, r):
        out = np.empty(len(X), dtype=int)
        for i in range(len(X)):
            b = np.ones(self.K) / self.K                  # belief
            for _ in range(self.iters):
                # pressure raises permeability for features that separate the
                # currently-leading class from the rest (active gating)
                lead = int(np.argmax(b))
                sep = (self.means[lead] - self.means.mean(0)) ** 2
                gate = self.disc * (1.0 + self.pressure * b[lead] * sep / (sep.max() + 1e-9))
                score = -np.array([
                    np.sum(gate * (X[i] - self.means[c]) ** 2 / self.var[c])
                    for c in range(self.K)
                ])
                b = _softmax(score)
            out[i] = int(np.argmax(b))
        return out


class TISigmaActiveInference(_Base):
    """UOP + i-Cell upgraded Active Inference.

    - Tralse generative model: class-conditional Gaussians (the 'preferred states').
    - GILE-weighted prior: train base-rate prior (the i-cell's preferred-state bias).
    - LCC precision-weighting: per-window precision scaled by resonance r / C_EMERICK
      (high coherence -> trust the observation; low -> stay Tralse / lean on prior).
    - GTFE gap-closure: iterate a feature-precision (attention) vector to minimize
      free energy (sharpen evidence) over a few active-inference steps.
    - Myrion-Resolution collapse: collapse to MAP only when coherent
      (max posterior prob > tau OR r > C_EMERICK); else resolve toward GILE prior.
    """
    name = "O4_tisigma_active_inference"

    def __init__(self, n_states, ai_iters=3, tau_collapse=0.55):
        super().__init__(n_states)
        self.ai_iters = ai_iters
        self.tau = tau_collapse
        self.prior_override = None  # optional external prior (used by O4XA)

    def fit(self, X, H, r):
        self.means = np.array([X[H == c].mean(0) if np.any(H == c)
                               else np.zeros(X.shape[1]) for c in range(self.K)])
        self.var = np.array([X[H == c].var(0) + 1e-3 if np.any(H == c)
                             else np.ones(X.shape[1]) for c in range(self.K)])
        rate = np.array([(H == c).mean() for c in range(self.K)]) + 1e-6
        self.gile_prior = rate / rate.sum()
        between = self.means.var(0)
        within = self.var.mean(0)
        self.pi0 = between / (within + 1e-9)              # initial feature precision
        return self

    def _posterior(self, x, prec_scale, prior):
        pi = self.pi0.copy()
        logp = None
        for _ in range(self.ai_iters):                   # GTFE gap-closure
            ll = np.array([
                -0.5 * np.sum(pi * (x - self.means[c]) ** 2 / self.var[c])
                for c in range(self.K)
            ])
            logp = np.log(prior + 1e-12) + prec_scale * ll
            post = _softmax(logp)
            # active step: upweight features where the MAP class is most distinctive
            lead = int(np.argmax(post))
            contrib = (x - self.means.mean(0)) ** 2 - (x - self.means[lead]) ** 2
            pi = np.clip(self.pi0 * (1.0 + 0.5 * np.tanh(contrib)), 0.0, None)
        return _softmax(logp)

    def predict(self, X, r):
        r = r.ravel()
        out = np.empty(len(X), dtype=int)
        for i in range(len(X)):
            prec_scale = float(np.clip(r[i] / C_EMERICK, 0.2, 3.0))
            prior = self.prior_override[i] if self.prior_override is not None else self.gile_prior
            post = self._posterior(X[i], prec_scale, prior)
            coherent = (post.max() > self.tau) or (r[i] > C_EMERICK)
            out[i] = int(np.argmax(post)) if coherent else int(np.argmax(prior))
        return out


class Ensemble(_Base):
    name = "C1_ensemble_vote"

    def fit(self, X, H, r):
        self.ops = [CrossAttention(self.K), Hopfield(self.K),
                    ReverseOsmosis(self.K), TISigmaActiveInference(self.K)]
        for op in self.ops:
            op.fit(X, H, r)
        return self

    def predict(self, X, r):
        preds = np.stack([op.predict(X, r) for op in self.ops], axis=1)
        out = np.empty(len(X), dtype=int)
        for i in range(len(X)):
            vals, cnts = np.unique(preds[i], return_counts=True)
            mx = cnts.max()
            tied = vals[cnts == mx]
            out[i] = preds[i, -1] if len(tied) > 1 else int(tied[0])  # tie -> O4
        return out


class O4_with_XA_prior(_Base):
    """Cross-attention posterior supplies the per-window prior for O4 (stacking)."""
    name = "C2_O4_xattn_prior"

    def fit(self, X, H, r):
        self.xa = CrossAttention(self.K).fit(X, H, r)
        self.o4 = TISigmaActiveInference(self.K).fit(X, H, r)
        return self

    def predict(self, X, r):
        self.o4.prior_override = np.clip(self.xa.posterior(X), 1e-6, None)
        self.o4.prior_override /= self.o4.prior_override.sum(1, keepdims=True)
        pred = self.o4.predict(X, r)
        self.o4.prior_override = None
        return pred


def all_operators(n_states):
    return [
        Passive(n_states),
        NearestCentroidMatched(n_states),
        CrossAttention(n_states),
        Hopfield(n_states),
        ReverseOsmosis(n_states),
        TISigmaActiveInference(n_states),
        Ensemble(n_states),
        O4_with_XA_prior(n_states),
    ]
