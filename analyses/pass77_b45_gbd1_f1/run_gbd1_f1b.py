"""
GBD-1-F1b: the diagnostic variant. Same world as F1a, but slack is "CHEAP" --
covert discretion / framing / timing that captures extra surplus WITHOUT being
observed as defection (no reputation hit, partner not harmed).

This isolates the hidden assumption exposed by F1a's sign-reversal:
  - F1a slack = OBSERVABLE betrayal -> erodes the base -> substitute for base
    -> interaction NEGATIVE (REFUTES unconditioned GBD-1).
  - F1b slack = CHEAP discretion -> rides on engagement volume -> complement to
    base -> interaction POSITIVE (CONFIRMS GBD-1 under the charitable reading).

If F1b shows a POSITIVE interaction while F1a showed NEGATIVE, the honest verdict
is: GBD-1 holds IFF slack is base-non-eroding ("cheap"); the principle needs that
scope condition (proposed GBD-1-R1). ASYMMETRIC #69: report whatever the numbers say.
"""
import numpy as np

SEED = 20260527
rng = np.random.default_rng(SEED)

N = 4000
T = 400
EMA = 0.08
K = 6.0
R0 = 0.5
COOP_GAIN = 1.0
DISCRETION_GAIN = 0.6   # extra surplus captured via cheap discretion when it fires

base = rng.uniform(0.0, 1.0, N)
slack = rng.uniform(0.0, 1.0, N)
rep = np.full(N, 0.5)
payoff = np.zeros(N)

for t in range(T):
    perm = rng.permutation(N)
    a = perm[: N // 2]
    b = perm[N // 2 :]
    for focal, partner in ((a, b), (b, a)):
        p_engage = 1.0 / (1.0 + np.exp(-K * (rep[focal] - R0)))
        engaged = rng.random(focal.size) < p_engage

        # focal cooperates (no strategic betrayal channel here)
        coop_success = engaged & (rng.random(focal.size) < base[focal])

        # CHEAP slack: on a successful, engaged cooperation, with prob s the focal
        # captures extra surplus via discretion -- invisible, partner unharmed.
        discretion = coop_success & (rng.random(focal.size) < slack[focal])

        payoff[focal] += np.where(coop_success, COOP_GAIN, 0.0)
        payoff[partner] += np.where(coop_success, COOP_GAIN, 0.0)
        payoff[focal] += np.where(discretion, DISCRETION_GAIN, 0.0)

        obs = np.where(coop_success, 1.0, 0.0)   # discretion does NOT hit reputation
        upd = engaged
        rep[focal] = np.where(upd, (1 - EMA) * rep[focal] + EMA * obs, rep[focal])


def ols(X, y):
    XtXinv = np.linalg.inv(X.T @ X)
    beta = XtXinv @ (X.T @ y)
    resid = y - X @ beta
    dof = X.shape[0] - X.shape[1]
    sigma2 = (resid @ resid) / dof
    se = np.sqrt(np.diag(sigma2 * XtXinv))
    return beta, se, beta / se


bz = (base - base.mean()) / base.std()
sz = (slack - slack.mean()) / slack.std()
X = np.column_stack([np.ones(N), bz, sz, bz * sz])
beta, se, tvals = ols(X, payoff)
names = ["intercept", "base", "slack", "base*slack"]

print("=== GBD-1-F1b (CHEAP slack): payoff ~ base + slack + base*slack (standardized) ===")
print(f"N={N} agents, T={T} rounds, seed={SEED}")
for nm, b_, s_, tt in zip(names, beta, se, tvals):
    print(f"  {nm:<12} coef={b_:+8.3f}  se={s_:6.3f}  t={tt:+8.2f}")

bmed, smed = np.median(base), np.median(slack)
hi_b, hi_s = base >= bmed, slack >= smed
cells = {
    "low-base  low-slack ": payoff[~hi_b & ~hi_s].mean(),
    "low-base  high-slack": payoff[~hi_b &  hi_s].mean(),
    "high-base low-slack ": payoff[ hi_b & ~hi_s].mean(),
    "high-base high-slack": payoff[ hi_b &  hi_s].mean(),
}
print("\n=== 2x2 cell mean payoffs ===")
for k, v in cells.items():
    print(f"  {k}: {v:8.2f}")
print("\n=== marginal effect of slack within base stratum ===")
print(f"  slack effect | LOW  base = {cells['low-base  high-slack'] - cells['low-base  low-slack ']:+8.2f}")
print(f"  slack effect | HIGH base = {cells['high-base high-slack'] - cells['high-base low-slack ']:+8.2f}")

verdict = ("CONFIRMS GBD-1 under cheap-slack (interaction>0, significant)"
           if (beta[3] > 0 and tvals[3] > 2.0) else "does NOT confirm")
print(f"\n=== VERDICT: GBD-1-F1b {verdict} ===")
print(f"    interaction coef={beta[3]:+.3f}, t={tvals[3]:+.2f}")
