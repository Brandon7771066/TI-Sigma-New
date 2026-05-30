"""
GBD-1-F1 falsifier: does sub-maximal-GILE slack pay ONLY on a high-G base?

Prediction (GBD-1, GILE-Backdrop Discriminator):
  In a repeated reputation game, the marginal payoff of "slack" (strategic
  defection/ambiguity budget) is POSITIVE-sloped in an agent's competence/honesty
  base and NEGATIVE-or-flat for low-base agents. Operationally: regressing total
  payoff on [base, slack, base*slack], the INTERACTION coefficient (base*slack)
  is POSITIVE and significant.
REFUTED if slack helps low-base agents as much as high-base agents (interaction
  term ~0 or negative).

Design ($0, deterministic seed):
  N agents, each with two fixed traits:
    base b in [0,1]   = probability they actually honor a cooperative commitment
                        (reliability / the compounding "high-G backdrop")
    slack s in [0,1]  = propensity to STRATEGICALLY defect when it looks profitable
                        (the 1 - G* slack budget)
  T rounds of random pairwise interactions. Each agent carries a public reputation
  r (EMA of observed cooperation). A partner ENGAGES (creating surplus = "existence"
  / H) with probability sigmoid(k*(r - r0)) -- high reputation buys engagement volume.
  When engaged, the focal agent either:
     - strategically exploits (prob s): gains EXPLOIT_GAIN, partner loses, observed
       cooperation = 0 (reputation hit),
     - else attempts to cooperate: succeeds w.p. b (mutual COOP_GAIN, obs coop = 1)
       or fails w.p. 1-b (no gain, obs coop = 0, reputation hit).
  Intuition under test: a high-base agent has (a) large engagement volume to apply
  slack to and (b) a reputation buffer to absorb the hit, so slack nets positive;
  a low-base agent has neither, so the same slack nets flat/negative.

No claim is true until the numbers say so (ASYMMETRIC #69).
"""
import numpy as np

SEED = 20260527
rng = np.random.default_rng(SEED)

N = 4000          # agents
T = 400           # rounds
EMA = 0.08        # reputation update rate
K = 6.0           # engagement sharpness
R0 = 0.5          # engagement reputation midpoint
COOP_GAIN = 1.0   # mutual cooperation surplus (per engaged round)
EXPLOIT_GAIN = 1.6  # short-term exploit gain (> coop, else slack never tempts)
EXPLOIT_COST = 1.0  # partner's loss when exploited (paid by the partner)

base = rng.uniform(0.0, 1.0, N)
slack = rng.uniform(0.0, 1.0, N)
rep = np.full(N, 0.5)        # start neutral
payoff = np.zeros(N)

for t in range(T):
    perm = rng.permutation(N)
    a = perm[: N // 2]
    b = perm[N // 2 :]
    for focal, partner in ((a, b), (b, a)):
        # partner decides to engage with focal based on focal's reputation
        p_engage = 1.0 / (1.0 + np.exp(-K * (rep[focal] - R0)))
        engaged = rng.random(focal.size) < p_engage

        # focal's action when engaged
        exploit = (rng.random(focal.size) < slack[focal]) & engaged
        coop_attempt = engaged & ~exploit
        coop_success = coop_attempt & (rng.random(focal.size) < base[focal])

        # payoffs
        payoff[focal] += np.where(exploit, EXPLOIT_GAIN, 0.0)
        payoff[focal] += np.where(coop_success, COOP_GAIN, 0.0)
        payoff[partner] += np.where(coop_success, COOP_GAIN, 0.0)   # mutual
        payoff[partner] -= np.where(exploit, EXPLOIT_COST, 0.0)     # victim loss

        # observed cooperation this round (only meaningful if engaged)
        obs = np.where(coop_success, 1.0, 0.0)
        # reputation EMA updates only for engaged interactions
        upd = engaged
        rep[focal] = np.where(upd, (1 - EMA) * rep[focal] + EMA * obs, rep[focal])

# ---- analysis ----
def ols(X, y):
    XtX = X.T @ X
    XtXinv = np.linalg.inv(XtX)
    beta = XtXinv @ (X.T @ y)
    resid = y - X @ beta
    dof = X.shape[0] - X.shape[1]
    sigma2 = (resid @ resid) / dof
    se = np.sqrt(np.diag(sigma2 * XtXinv))
    tvals = beta / se
    return beta, se, tvals

# standardize predictors so the interaction is interpretable
bz = (base - base.mean()) / base.std()
sz = (slack - slack.mean()) / slack.std()
X = np.column_stack([np.ones(N), bz, sz, bz * sz])
beta, se, tvals = ols(X, payoff)
names = ["intercept", "base", "slack", "base*slack"]

print("=== GBD-1-F1: payoff ~ base + slack + base*slack (standardized) ===")
print(f"N={N} agents, T={T} rounds, seed={SEED}")
for nm, b_, s_, tt in zip(names, beta, se, tvals):
    print(f"  {nm:<12} coef={b_:+8.3f}  se={s_:6.3f}  t={tt:+8.2f}")

# 2x2 cell means: low/high base x low/high slack (median split)
bmed, smed = np.median(base), np.median(slack)
hi_b, hi_s = base >= bmed, slack >= smed
cells = {
    "low-base  low-slack ": payoff[~hi_b & ~hi_s].mean(),
    "low-base  high-slack": payoff[~hi_b &  hi_s].mean(),
    "high-base low-slack ": payoff[ hi_b & ~hi_s].mean(),
    "high-base high-slack": payoff[ hi_b &  hi_s].mean(),
}
print("\n=== 2x2 cell mean payoffs (median split) ===")
for k, v in cells.items():
    print(f"  {k}: {v:8.2f}")

slack_effect_low_base = cells["low-base  high-slack"] - cells["low-base  low-slack "]
slack_effect_high_base = cells["high-base high-slack"] - cells["high-base low-slack "]
print("\n=== marginal effect of slack within base stratum ===")
print(f"  slack effect | LOW  base = {slack_effect_low_base:+8.2f}")
print(f"  slack effect | HIGH base = {slack_effect_high_base:+8.2f}")

# slope of slack-effect: regress payoff on slack within base terciles
print("\n=== slack slope within base terciles (sign should rise low->high) ===")
q1, q2 = np.quantile(base, [1/3, 2/3])
for label, mask in [("low-base   ", base < q1),
                    ("mid-base   ", (base >= q1) & (base < q2)),
                    ("high-base  ", base >= q2)]:
    bb, yy = slack[mask], payoff[mask]
    A = np.column_stack([np.ones(bb.size), (bb - bb.mean())])
    bet, _, tv = ols(A, yy)
    print(f"  {label} d(payoff)/d(slack): coef={bet[1]:+8.2f}  t={tv[1]:+7.2f}")

interaction_t = tvals[3]
verdict = ("NOT REFUTED (interaction>0, significant)"
           if (beta[3] > 0 and interaction_t > 2.0)
           else "REFUTED or inconclusive")
print(f"\n=== VERDICT: GBD-1-F1 {verdict} ===")
print(f"    interaction coef={beta[3]:+.3f}, t={interaction_t:+.2f}")
