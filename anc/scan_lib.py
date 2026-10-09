#!/usr/bin/env python3
"""Shared row library for the round-3 energy-cut closure (r3/lp).

Candidate space (per cut): sigma in {a,b,c} (modulus side); s1,s2 = the two
counted sides (alphabetical); T = nonempty subset of {1..6,TAIL} on sigma;
R1 subset of {1..6,TAIL} on s1, R2 on s2, (R1,R2) != (empty,empty);
q = gcd of the freed numeric exponents, forced to 1 whenever a TAIL block is
freed (the 7-full tail part is not a perfect power); q>=1 always.

Masks: bit i (i=0..5) = exponent i+1 freed/selected; bit 6 = TAIL.

Profile P: dict with keys s in {'a','b','c'} (rad_s), f'{s}{i}' (i=1..6,
block root masses), f'v{s}' (tail value mass). Derived: tau_s = rad_s - sum
s_i; val_s = sum_i i*s_i + v_s.

Per (sigma,T,R1,R2), at the profile:
  cost = root mass of T on sigma (TAIL -> tau_sig);  W = value mass of T
         (TAIL -> v_sig)
  f1,w1 = freed root/value mass on s1 (TAIL -> tau_1, v_1); f2,w2 on s2
  P1'' = rad_1 - f1;  P2'' = rad_2 - f2;  P'' = P1''+P2''
  val1f = val_1 - w1; val2f = val_2 - w2; F = (w1+w2)/q
  Eb   = f1+f2+max(0,F-W)            [E_box, PROVEN]
  Ec1  = P''+max(0,val1f+val2f-W)    [diag/k-shift, PROVEN]
  Ec2a = P''+P2''+max(0,val1f-W)     [orientation r_max, PROVEN]
  Ec2b = P''+P1''+max(0,val2f-W)
  Ec3  = 2P''                        [trivial]
  EcH  = P''+max(0,P''-W)            [conjectural (H)]
Cut forms (LP variants; EACH is a valid bound D <= G because each replaces a
min(...) by one of its arguments):
  UN   = P''+cost+max(0,F-W)
  CS1  = cost+Ec1/2+Eb/2    CS2A = cost+Ec2a/2+Eb/2    CS2B, CS3 alike
  RMA  = cost+P2''+max(0,val1f-W)+f1+f2     RMB symmetric
  HYP  = cost+EcH/2+Eb/2                     [needs (H)]
  HYPK(kappa) = cost+(P''+max(0,P''-W)+kappa*max(0,val1f+val2f-W))/2+Eb/2
  HMAX = cost+f1+f2+max(0,P''-W)             [needs (Hmax), STRICTLY STRONGER
         than (H): r_max <= X^eps (1+|S|/M) pointwise equidistribution;
         scenario C only -- maps the ceiling of the congruence paradigm]
Family aggregation (reference semantics = witness_scan_energy.py):
  G_union = UN;  G_CSprov = min(CS1,CS2A,CS2B,CS3);  G_rmax = min(RMA,RMB);
  G_hyp   = min(HYP,CS1,CS2A,CS2B,CS3).

POWERFUL-MODULUS SCOPE (hostile-audit fix, 20260710): the hypotheses (H)
and (Hmax) are stated only for POWERFUL moduli M.  1 in T makes M contain a
squarefree factor, outside scope.  Hence the CONDITIONAL forms HYP / HYPK /
HMAX are ADMISSIBLE ONLY for T subset of {2..6, TAIL} (restrict_hyp_T=True,
the default, enforces this: conditional forms are dropped / masked to +inf
at T-sets containing 1).  The PROVEN forms (UN, CS*, RM*) stay unrestricted.
Set restrict_hyp_T=False only for regression against the pre-audit
reference numbers (witness_scan_energy.py).
THUE family (round-3 addition; unconditional, linear, 15 rows; REVISED
radical-mass form -- root enumeration, values recovered in X^eps):
  THUE(e,k) = rad_e + (rad_y - s_k(y)) + (rad_z - s_k(z)),
  e in {a,b,c}, k in 2..6, {y,z} = the other two sides.
  (Enumerate roots of side e and of the non-k parts of y,z; the remaining
  equation w*C^k - u*B^k = +-e_value has X^{o(1)} solutions per fixed
  coefficients: Pell/ideal-divisor for k=2, Bombieri-Schmidt Thue + a
  reducible-case divisor argument for k>=3.)

SPACING family (PROVEN, archimedean; 30 rows):
  G_spac(e; y,z; k) = rad_y + (rad_z - s_k(z))
                      + max(0, val_e - (val_z - k*s_k(z)) - (k-1)*s_k(z))
  for e in {a,b,c}, (y,z) BOTH orderings of the other two sides, k in 2..6.
  The max argument simplifies to  val_e - val_z + s_k(z).
  (Enumerate y fully by roots and z's non-k blocks by roots; z's k-block
  C^k is then confined to an interval of length X^{val_e - (val_z-k*s_k)}
  while consecutive k-th powers near X^{k*s_k} are spaced X^{(k-1)*s_k};
  count 1 + ratio; e is determined by (y,z).)

MOM family (PROVEN powered-box character
moments: orthogonality + Hoelder + q-power kernel X^{o(1)} + integer-pair
counting; valid for ARBITRARY M -- no powerful-T restriction):
  candidate = (sigma,T,R1,R2) + integer vector r_j >= 1 over the FIXED
  blocks j of the two counted sides, budget sum_j 1/r_j <= 1 (slots may
  take r_j = infinity: Hoelder sup-norm factor, budget 0):
    regular fixed block j (root mass s_j):
        term_j(r)   = s_j + max(0, s_j - W/r)  [= s_j + (1/r)max(0,r*s_j-W)]
        term_j(inf) = 2*s_j
    fixed tail (root tau, value v):
        term_t(r)   = tau + (1/r)*min(r*tau, max(0, r*v - W))
        term_t(inf) = 2*tau
    E_mom(r) = sum_j term_j;   G_mom = cost + E_mom(r)/2 + Eb/2.
  KEY BOUND (continuous relaxation; basis of verify + separation): with
  x_j = 1/r_j each penalty >= max(0, m_j - W*x_j)  (m_j = s_j resp. tau;
  for tails min(tau, max(0,v-Wx)) >= max(0, tau-Wx) since tau <= v), so
    E_mom(r) >= P'' + max(0, P'' - W) = EcH   for EVERY admissible r,
  i.e. G_mom >= the EcH-form on the SAME tuple with NO T restriction; and
  E_mom = P'' exactly when the zero-penalty budget sum_j 1/floor(W/m_j)
  <= 1 (using v for tails).  Mom PROVES EcH up to integer rounding, on
  arbitrary moduli.
"""
import itertools
import numpy as np
from math import gcd, floor
from fractions import Fraction as Fr

RNG = list(range(1, 7))
TAIL = 7
SIDES = {"a": ("b", "c"), "b": ("a", "c"), "c": ("a", "b")}
NM = 128  # masks over {1..6, TAIL}

FORMS = ("UN", "CS1", "CS2A", "CS2B", "CS3", "RMA", "RMB", "HYP")


def mask_elems(m):
    """Mask -> sorted tuple of elements (1..6, TAIL=7)."""
    return tuple([i + 1 for i in range(6) if (m >> i) & 1]
                 + ([TAIL] if (m >> 6) & 1 else []))


def elems_mask(elems):
    m = 0
    for e in elems:
        m |= 1 << (6 if e == TAIL else e - 1)
    return m


# gcd basis per mask: 0 if empty, 1 if TAIL freed, else gcd of numeric elems
GBASIS = []
for m in range(NM):
    if (m >> 6) & 1:
        g = 1
    else:
        g = 0
        for i in range(6):
            if (m >> i) & 1:
                g = gcd(g, i + 1)
    GBASIS.append(g)

# QMAT[i,j] = q for (R1,R2) = (mask i, mask j): gcd of bases, 0 -> 1
QMAT = np.ones((NM, NM), dtype=np.int64)
for i in range(NM):
    for j in range(NM):
        q = gcd(GBASIS[i], GBASIS[j])
        QMAT[i, j] = q if q else 1


def q_of(m1, m2):
    q = gcd(GBASIS[m1], GBASIS[m2])
    return q if q else 1


def side_scalars(P, s):
    """(rad, tau, v, val) of side s -- exact if P holds Fractions."""
    rad = P[s]
    ssum = sum(P[f"{s}{i}"] for i in RNG)
    tau = rad - ssum
    v = P[f"v{s}"]
    val = sum(i * P[f"{s}{i}"] for i in RNG) + v
    return rad, tau, v, val


def side_tables(P, s, numeric=float):
    """Per-mask tables for side s: f (root mass), w (value mass),
    Pf = rad - f, valf = val - w.  numeric=float -> numpy arrays;
    numeric=Fr -> lists of Fractions (exact)."""
    rad, tau, v, val = side_scalars(P, s)
    f = [None] * NM
    w = [None] * NM
    for m in range(NM):
        ff = sum(P[f"{s}{i + 1}"] for i in range(6) if (m >> i) & 1)
        ww = sum((i + 1) * P[f"{s}{i + 1}"] for i in range(6) if (m >> i) & 1)
        if (m >> 6) & 1:
            ff = ff + tau
            ww = ww + v
        f[m] = ff
        w[m] = ww
    if numeric is float:
        f = np.array([float(x) for x in f])
        w = np.array([float(x) for x in w])
        return f, w, float(rad) - f, float(val) - w
    return f, w, [rad - x for x in f], [val - x for x in w]


def thue_rows(P):
    """15 unconditional THUE rows (radical-mass form): {(e,k): G value}
    (exact if P exact).  THUE(e,k) = rad_e + (rad_y - s_k(y)) + (rad_z - s_k(z))."""
    out = {}
    for e in "abc":
        y, z = SIDES[e]
        for k in range(2, 7):
            out[(e, k)] = (P[e] + (P[y] - P[f"{y}{k}"])
                           + (P[z] - P[f"{z}{k}"]))
    return out


def spacing_rows(P):
    """30 unconditional SPACING rows: {(e,y,z,k): G value} (exact if P
    exact).  G = rad_y + (rad_z - s_k(z)) + max(0, val_e - val_z + s_k(z))."""
    val = {s: side_scalars(P, s)[3] for s in "abc"}
    out = {}
    for e in "abc":
        o1, o2 = SIDES[e]
        for (y, z) in ((o1, o2), (o2, o1)):
            for k in range(2, 7):
                B = val[e] - val[z] + P[f"{z}{k}"]
                zero = B - B  # typed zero (Fraction or float)
                out[(e, y, z, k)] = (P[y] + (P[z] - P[f"{z}{k}"])
                                     + max(zero, B))
    return out


def mom_fixed_slots(P, sig, m1, m2):
    """The fixed slots of a Mom candidate, with their (kind, mass data).
    Returns list of (slotkey, kind, m, v): slotkey = (sideno, blk);
    kind 'reg' -> m = s_j (v unused); kind 'tail' -> m = tau, v = tail value.
    Zero-mass slots ARE included (mass 0; any r gives term 0)."""
    out = []
    for sideno, (s, mask) in enumerate(((SIDES[sig][0], m1),
                                        (SIDES[sig][1], m2)), start=1):
        rad, tau, v, _ = side_scalars(P, s)
        for j in RNG:
            if not (mask >> (j - 1)) & 1:
                out.append(((sideno, j), "reg", P[f"{s}{j}"], None))
        if not (mask >> 6) & 1:
            out.append(((sideno, TAIL), "tail", tau, v))
    return out


def eval_mom_exact(P, sig, m1, m2, mT, rvec):
    """Exact G_mom for one Mom candidate. rvec: dict slotkey -> integer
    r >= 1; fixed slots NOT in rvec take r = infinity (term 2*mass).
    Asserts budget sum 1/r <= 1. Returns Fraction (P exact)."""
    s1, s2 = SIDES[sig]
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    cost, W = ct[mT], wt[mT]
    f1t, w1t, _, _ = side_tables(P, s1, numeric=Fr)
    f2t, w2t, _, _ = side_tables(P, s2, numeric=Fr)
    q = q_of(m1, m2)
    F = Fr(w1t[m1] + w2t[m2], 1) / q
    Eb = f1t[m1] + f2t[m2] + max(Fr(0), F - W)
    assert sum(Fr(1, r) for r in rvec.values()) <= 1, "Mom budget exceeded"
    E = Fr(0)
    for slotkey, kind, m, v in mom_fixed_slots(P, sig, m1, m2):
        r = rvec.get(slotkey)
        if kind == "reg":
            if r is None:
                E += 2 * m
            else:
                E += m + max(Fr(0), m - Fr(W, r))
        else:
            if r is None:
                E += 2 * m
            else:
                E += m + Fr(1, r) * min(r * m, max(Fr(0), r * v - W))
    return cost + (E + Eb) / 2


def mom_inf_exact(P, sig, m1, m2, mT):
    """EXACT infimum over ALL admissible integer r-vectors of E_mom at one
    tuple (P exact Fractions), in closed form ("MOME envelope").

    Derivation (exact, no heuristics):  write x_j = 1/r_j in [0,1].  The
    reduction of E_mom below the all-infinity level 2*P'' is
      reg slot j:  2s_j - term_j = s_j - max(0, s_j - W x_j) = min(s_j, W x_j)
      tail slot t: 2tau - term_t = tau - min(tau, max(0, v - W x))
                                 = clamp(W x - (v - tau), 0, tau)
    (concave rate-W pieces; tails have a dead zone x <= (v-tau)/W).  The sup
    of the total reduction over real x with sum x <= 1 equals
      maxRed = max over TZ subset of FIXED tails of
               max(0, min(W - sum_{t in TZ}(v_t - tau_t),
                          sum_{fixed reg} s_j + sum_{t in TZ} tau_t)),
    and integer vectors r approach it arbitrarily closely (monotone
    continuity of the reductions + density of reciprocal sums), so
      inf_r E_mom = 2 P'' - maxRed,
    and D <= G_mom(r) for all r  <=>  D <= cost + (inf E_mom + Eb)/2.
    Also inf E_mom >= EcH always, with equality iff no positive fixed tail.
    Returns (E_inf, argmax TZ as tuple of side numbers)."""
    s1, s2 = SIDES[sig]
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    W = wt[mT]
    slots = mom_fixed_slots(P, sig, m1, m2)
    Mreg = sum(m for _, kind, m, _ in slots if kind == "reg")
    tails = [(key, m, v) for key, kind, m, v in slots if kind == "tail"]
    Pp = Mreg + sum(m for _, m, _ in tails)
    best = Fr(0)
    bestTZ = ()
    for r in range(len(tails) + 1):
        for TZ in itertools.combinations(tails, r):
            red = min(W - sum(v - m for _, m, v in TZ),
                      Mreg + sum(m for _, m, _ in TZ))
            if red < 0:
                red = Fr(0)
            if red > best:
                best = red
                bestTZ = tuple(key[0] for key, _, _ in TZ)
    return 2 * Pp - best, bestTZ


CONDITIONAL_FORMS = ("HYP", "HYPK", "HMAX")


def t_admissible(mT):
    """True iff T (mask) has no 1-block, i.e. M is powerful."""
    return not (mT & 1)


def eval_forms_exact(P, sig, m1, m2, mT, kappa=None, restrict_hyp_T=True):
    """Exact Fraction evaluation of all cut forms at one candidate tuple.
    Returns dict form -> G (Fractions). kappa (Fraction) adds 'HYPK'.
    restrict_hyp_T (default): conditional forms are OMITTED when 1 in T
    (powerful-modulus scope of (H)/(Hmax))."""
    s1, s2 = SIDES[sig]
    f1t, w1t, P1t, v1t = side_tables(P, s1, numeric=Fr)
    f2t, w2t, P2t, v2t = side_tables(P, s2, numeric=Fr)
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    q = q_of(m1, m2)
    f1, w1, P1f, val1f = f1t[m1], w1t[m1], P1t[m1], v1t[m1]
    f2, w2, P2f, val2f = f2t[m2], w2t[m2], P2t[m2], v2t[m2]
    cost, W = ct[mT], wt[mT]
    Pp = P1f + P2f
    F = Fr(w1 + w2, 1) / q
    mFW = max(Fr(0), F - W)
    Eb = f1 + f2 + mFW
    Ec1 = Pp + max(Fr(0), val1f + val2f - W)
    Ec2a = Pp + P2f + max(Fr(0), val1f - W)
    Ec2b = Pp + P1f + max(Fr(0), val2f - W)
    Ec3 = 2 * Pp
    EcH = Pp + max(Fr(0), Pp - W)
    out = {
        "UN": Pp + cost + mFW,
        "CS1": cost + Fr(Ec1 + Eb, 2),
        "CS2A": cost + Fr(Ec2a + Eb, 2),
        "CS2B": cost + Fr(Ec2b + Eb, 2),
        "CS3": cost + Fr(Ec3 + Eb, 2),
        "RMA": cost + P2f + max(Fr(0), val1f - W) + f1 + f2,
        "RMB": cost + P1f + max(Fr(0), val2f - W) + f1 + f2,
        "HYP": cost + Fr(EcH + Eb, 2),
        "HMAX": cost + f1 + f2 + max(Fr(0), Pp - W),
    }
    if kappa is not None:
        EcHk = EcH + kappa * max(Fr(0), val1f + val2f - W)
        out["HYPK"] = cost + (EcHk + Eb) / 2
    if restrict_hyp_T and not t_admissible(mT):
        for f in CONDITIONAL_FORMS:
            out.pop(f, None)
    return out


def scan_forms_np(P, kappa=None, use_hyp=True, use_hmax=False,
                  use_mome=False, restrict_hyp_T=True):
    """Vectorized scan. Yields (sig, Gdict) per sigma, where Gdict maps
    form -> float array of shape (128, 128, 127) over (m1, m2, mT-1).
    Entry (0,0,:) is masked to +inf (R1=R2=empty excluded).
    kappa: float -> also yields 'HYPK'. use_hyp=False drops 'HYP'.
    use_hmax=True adds the scenario-C 'HMAX' family.
    use_mome=True adds 'MOME' = the PROVEN Mom-envelope family
    (mom_inf_exact vectorized; NO T restriction; argmax TZ recomputed
    per-tuple at emission time by the separation loop).
    restrict_hyp_T (default): conditional forms (HYP/HYPK/HMAX) masked to
    +inf at T-sets containing 1 (powerful-modulus scope)."""
    t_bad = np.array([bool((mT & 1)) for mT in range(1, NM)])  # 1 in T
    tailfree = np.array([bool((m >> 6) & 1) for m in range(NM)])
    tabs = {s: side_tables(P, s, numeric=float) for s in "abc"}
    for sig in "abc":
        s1, s2 = SIDES[sig]
        f1, w1, P1f, v1f = tabs[s1]
        f2, w2, P2f, v2f = tabs[s2]
        ct, wt, _, _ = tabs[sig]
        cost = ct[1:][None, None, :]
        W = wt[1:][None, None, :]
        F = (w1[:, None] + w2[None, :]) / QMAT
        mFW = np.maximum(0.0, F[:, :, None] - W)
        Pp = P1f[:, None, None] + P2f[None, :, None]
        Eb = f1[:, None, None] + f2[None, :, None] + mFW
        mV12 = np.maximum(0.0, v1f[:, None, None] + v2f[None, :, None] - W)
        mV1 = np.maximum(0.0, v1f[:, None, None] - W)   # (128,1,127)
        mV2 = np.maximum(0.0, v2f[None, :, None] - W)   # (1,128,127)
        G = {}
        G["UN"] = Pp + cost + mFW
        G["CS1"] = cost + (Pp + mV12 + Eb) / 2
        G["CS2A"] = cost + (Pp + P2f[None, :, None] + mV1 + Eb) / 2
        G["CS2B"] = cost + (Pp + P1f[:, None, None] + mV2 + Eb) / 2
        G["CS3"] = cost + Pp + Eb / 2
        G["RMA"] = (cost + P2f[None, :, None] + mV1
                    + f1[:, None, None] + f2[None, :, None])
        G["RMB"] = (cost + P1f[:, None, None] + mV2
                    + f1[:, None, None] + f2[None, :, None])
        if use_hyp:
            G["HYP"] = cost + (Pp + np.maximum(0.0, Pp - W) + Eb) / 2
        if kappa is not None:
            G["HYPK"] = cost + (Pp + np.maximum(0.0, Pp - W)
                                + kappa * mV12 + Eb) / 2
        if use_hmax:
            G["HMAX"] = (cost + f1[:, None, None] + f2[None, :, None]
                         + np.maximum(0.0, Pp - W))
        if use_mome:
            # Mom envelope: E_inf = 2P'' - max over TZ of
            #   max(0, min(W - A(TZ), B(TZ))),
            # A = sum_{TZ}(v-tau), B = Mreg + sum_{TZ} tau, over FIXED tails.
            rad1, tau1, v1, _ = side_scalars(P, s1)
            rad2, tau2, v2, _ = side_scalars(P, s2)
            tau1, v1, tau2, v2 = map(float, (tau1, v1, tau2, v2))
            # fixed-tail indicators (tail fixed iff not freed by the mask)
            tf1 = (~tailfree)[:, None, None]   # side1 tail fixed
            tf2 = (~tailfree)[None, :, None]
            # Mreg = P'' minus fixed-tail root masses
            Mreg = Pp - tau1 * tf1 - tau2 * tf2
            red = np.minimum(W, Mreg)                     # TZ = {}
            red = np.maximum(red, np.where(
                tf1, np.minimum(W - (v1 - tau1), Mreg + tau1), -np.inf))
            red = np.maximum(red, np.where(
                tf2, np.minimum(W - (v2 - tau2), Mreg + tau2), -np.inf))
            red = np.maximum(red, np.where(
                tf1 & tf2,
                np.minimum(W - (v1 - tau1) - (v2 - tau2),
                           Mreg + tau1 + tau2), -np.inf))
            red = np.maximum(red, 0.0)
            G["MOME"] = cost + (2 * Pp - red + Eb) / 2
        if restrict_hyp_T:
            for f in CONDITIONAL_FORMS:
                if f in G:
                    G[f][:, :, t_bad] = np.inf
        for g in G.values():
            g[0, 0, :] = np.inf
        yield sig, G


# ---- HOLMOM: full Hoelder-signature family ----
# For (sigma, T) index ALL blocks of the two counted sides (no free sets):
# regular block i (root mass s_i), tails (tau, v).  Choose per block PAY
# (term s_i resp. tau; = the r -> infinity sup-norm limit) or HOLDER with
# integer r_i >= 1, budget sum_{holdered} 1/(2 r_i) <= 1:
#   reg:  term = s_i/2 + (1/(2r)) max(0, r s_i - W) = s_i - min(s_i, W/r)/2
#   tail: term = tau/2 + (1/(2r)) min(r tau, max(0, r v - W))
#         (v-branch variant tau/2 + (1/2)max(0, v - W/r) is the useful one;
#          the tau-branch equals PAY and is dominated)
#   G_holmom = cost(T) + sum_blocks term.
# PROOF: Cartesian majorization (ambient box, units mod M), character
# orthogonality, triangle, Hoelder with exponents 2r_i; per-factor moment =
# product-congruence count <= X^eps (rootvol^r + rootvol^{2r}/M) via torsion
# stripping (|mu_k(M)| = X^{o(1)}) + divisor bounds; tails = sparse subsets.
# NO q-reduction, NO Lemma A; valid for arbitrary M (any T).
#
# EXACT ENVELOPE (inf over all integer assignments; same density argument
# as mom_inf_exact, x = 1/(2r) in (0, 1/2]):
#   reduction vs all-PAY: reg red(x) = min(s_i/2, W x); tail red(x) =
#   clamp(W x - (v-tau)/2, 0, tau/2); all rates W =>
#   maxRed = max over TZ subset of tails of
#     max(0, min(W - sum_TZ (v-tau)/2,
#                sum_reg min(s_i, W)/2 + sum_TZ min(tau, max(0, W-(v-tau)))/2))
#   G_env = cost + (sum_reg s_i + sum_tails tau) - maxRed.

def holmom_blocks(P, sig):
    """All blocks of the two counted sides: ('reg', slot, s) / ('tail',
    slot, tau, v); zero-mass blocks skipped (any choice contributes 0)."""
    out = []
    for sideno, s in enumerate(SIDES[sig], start=1):
        rad, tau, v, _ = side_scalars(P, s)
        for j in RNG:
            if P[f"{s}{j}"] > 0:
                out.append(("reg", (sideno, j), P[f"{s}{j}"], None))
        if tau > 0:
            out.append(("tail", (sideno, TAIL), tau, v))
    return out


def holmom_env_exact(P, sig, mT):
    """Exact HOLMOM envelope value at (sigma, T). Returns (G, bestTZ)."""
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    cost, W = ct[mT], wt[mT]
    blocks = holmom_blocks(P, sig)
    base = sum((b[2] for b in blocks), Fr(0))
    regcap = sum((min(b[2], W) for b in blocks if b[0] == "reg"),
                 Fr(0)) / 2
    tails = [b for b in blocks if b[0] == "tail"]
    best = Fr(0)
    bestTZ = ()
    for nsel in range(len(tails) + 1):
        for TZ in itertools.combinations(tails, nsel):
            thr = sum((b[3] - b[2] for b in TZ), Fr(0)) / 2
            caps = regcap + sum((min(b[2], max(Fr(0), W - (b[3] - b[2])))
                                 for b in TZ), Fr(0)) / 2
            red = min(W - thr, caps)
            if red > best:
                best = red
                bestTZ = tuple(b[1][0] for b in TZ)
    return cost + base - best, bestTZ


def eval_holmom_exact(P, sig, mT, assign):
    """Exact G of a CONCRETE HOLMOM row.  assign: dict slot -> integer r
    (slots absent = PAY).  Checks the budget sum 1/(2r) <= 1."""
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    cost, W = ct[mT], wt[mT]
    assert sum(Fr(1, 2 * r) for r in assign.values()) <= 1, "budget"
    G = cost
    for kind, slot, m, v in holmom_blocks(P, sig):
        r = assign.get(slot)
        if r is None:
            G += m
        elif kind == "reg":
            G += m / 2 + max(Fr(0), m - Fr(W, r)) / 2 if False else \
                m / 2 + Fr(1, 2 * r) * max(Fr(0), r * m - W)
        else:
            G += m / 2 + Fr(1, 2 * r) * min(r * m, max(Fr(0), r * v - W))
    return G


def holmom_greedy(P, sig, mT, rpartial_cap=4096):
    """Greedy near-envelope integer assignment at (sigma, T).
    Strategy: per block compute the zero-penalty option (reg: r=floor(W/s),
    gain s/2, budget 1/(2r); tail: r=floor(W/v), gain tau/2); sort by
    gain/budget, take while budget lasts; spend leftover on the best
    remaining block with one fine partial r.  Returns (assign, G)."""
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    W = wt[mT]
    opts = []
    for kind, slot, m, v in holmom_blocks(P, sig):
        mm = m if kind == "reg" else v
        if W >= mm and mm > 0:
            r0 = int(W / mm)
            gain = m / 2 if kind == "reg" else m / 2
            opts.append((gain / Fr(1, 2 * r0), gain, Fr(1, 2 * r0),
                         slot, r0, kind, m, v))
        elif mm > 0:
            opts.append((Fr(0), Fr(0), Fr(1), slot, None, kind, m, v))
    opts.sort(key=lambda t: -t[0])
    assign = {}
    budget = Fr(1)
    rest = []
    for eff, gain, b, slot, r0, kind, m, v in opts:
        if r0 is not None and b <= budget and gain > 0:
            assign[slot] = r0
            budget -= b
        else:
            rest.append((slot, kind, m, v))
    # one partial top-up on the largest remaining block
    if rest and budget > 0:
        rest.sort(key=lambda t: -t[2])
        slot, kind, m, v = rest[0]
        r = max(int(Fr(1) / (2 * budget)) + (0 if Fr(1, 2) / budget ==
                int(Fr(1) / (2 * budget)) else 1), 1)
        if r <= rpartial_cap:
            # gain check: reg partial gain = (m - max(0, m - W/r))/2 > 0?
            mm = m if kind == "reg" else v
            if W > 0 and Fr(W, r) > (mm - m if kind == "tail" else 0):
                assign[slot] = r
    return assign, eval_holmom_exact(P, sig, mT, assign)


# ---- HOLMOM2: real-order (chord / Lyapunov-hull) extension ---------------
# Moment interpolation (Lyapunov): for 1 <= p < q, ||S||_{2r} with
# 1/(2r) = theta/(2p) + (1-theta)/(2q) satisfies
#   exponent(2r-th normalized moment) <= theta*c_p + (1-theta)*c_q,
# i.e. the per-block cost as a function of the BUDGET u = 1/(2r) is bounded
# by the chord between ANY two proven anchor points -- so the proven family
# per block is the LOWER CONVEX HULL of the anchors
#   (u=0, PAY cost) and (u_k = 1/(2k), anchor_k cost), k = 1..rcap:
#   reg  anchor_k = s/2 + max(0, s - W/k)/2                 (PAY cost s)
#   tail anchor_k = min over branches:                       (PAY cost tau)
#        'v': tau/2 + max(0, v - W/k)/2     't': tau  (= PAY, no y-term)
# Blocks couple only through sum_j u_j <= 1; block hulls are convex, so the
# exact family optimum per (sigma,T) is a merged marginal-rate greedy over
# hull segments (heap by most-negative rate, per-block in hull order).

def holmom2_anchor(kind, m, v, W, k):
    """(cost, branch) of anchor k (k=0 -> PAY). Exact for Fraction data."""
    if k == 0:
        return m, "t"
    if kind == "reg":
        return m / 2 + max(Fr(0), m - W / k) / 2, None
    cv = m / 2 + max(Fr(0), v - W / k) / 2
    return (cv, "v") if cv <= m else (m, "t")


def holmom2_hull(kind, m, v, W, rcap=64):
    """Lower convex hull of the anchor points in (u, cost) space.
    Returns list of hull vertices [(u, cost, k, branch)] with u ascending
    (starts at PAY (0, m|tau, 0))."""
    pts = [(Fr(0), m, 0, "t")]   # PAY point (u = 0)
    for k in range(rcap, 0, -1):
        c, br = holmom2_anchor(kind, m, v, W, k)
        pts.append((Fr(1, 2 * k), c, k, br))
    hull = []
    for p in pts:  # monotone-chain lower hull (u ascending)
        while len(hull) >= 2:
            (u1, c1, _, _), (u2, c2, _, _) = hull[-2], hull[-1]
            # drop hull[-1] if it is above the segment hull[-2] -> p
            if (c2 - c1) * (p[0] - u1) >= (p[1] - c1) * (u2 - u1):
                hull.pop()
            else:
                break
        hull.append(p)
    return hull


def holmom2_opt(P, sig, mT, rcap=64):
    """EXACT optimum of the chord/hull HOLMOM family at (sigma, T).
    Returns (G, assignment); assignment: slot -> (kA, kB, theta, brA, brB)
    meaning u* = theta*u_{kA} + (1-theta)*u_{kB} (k=0 -> PAY anchor);
    PAY-only slots absent."""
    import heapq
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    cost, W = ct[mT], wt[mT]
    blocks = holmom_blocks(P, sig)
    total = cost + sum((b[2] for b in blocks), Fr(0))   # all-PAY level
    hulls = {}
    segptr = {}
    heap = []
    for kind, slot, m, v in blocks:
        h = holmom2_hull(kind, m, v, W, rcap)
        hulls[slot] = h
        segptr[slot] = 0
        if len(h) > 1:
            (u1, c1, _, _), (u2, c2, _, _) = h[0], h[1]
            rate = (c2 - c1) / (u2 - u1)
            if rate < 0:
                heapq.heappush(heap, (rate, slot))
    budget = Fr(1)
    used = {}          # slot -> u consumed
    while heap and budget > 0:
        rate, slot = heapq.heappop(heap)
        i = segptr[slot]
        h = hulls[slot]
        u1, c1 = h[i][0], h[i][1]
        u2, c2 = h[i + 1][0], h[i + 1][1]
        du = u2 - u1
        take = min(du, budget)
        total += rate * take
        used[slot] = used.get(slot, Fr(0)) + take
        budget -= take
        if take == du:
            segptr[slot] = i + 1
            if i + 2 < len(h):
                nrate = (h[i + 2][1] - c2) / (h[i + 2][0] - u2)
                if nrate < 0:
                    heapq.heappush(heap, (nrate, slot))
    assign = {}
    for slot, u in used.items():
        if u == 0:
            continue
        h = hulls[slot]
        # locate u within hull vertices
        j = 0
        while j + 1 < len(h) and h[j + 1][0] <= u:
            j += 1
        if h[j][0] == u:          # exactly at a vertex
            _, _, k, br = h[j]
            assign[slot] = (k, k, Fr(1), br, br)
        else:
            uA, _, kA, brA = h[j]
            uB, _, kB, brB = h[j + 1]
            th = (uB - u) / (uB - uA)      # u = th*uA + (1-th)*uB
            assign[slot] = (kA, kB, th, brA, brB)
    return total, assign


def eval_holmom2_exact(P, sig, mT, assign, rcap=64):
    """Exact G of a concrete chord row (independent recomputation; uses the
    STORED anchors/branches, checks the budget)."""
    ct, wt, _, _ = side_tables(P, sig, numeric=Fr)
    cost, W = ct[mT], wt[mT]
    G = cost
    bud = Fr(0)
    for kind, slot, m, v in holmom_blocks(P, sig):
        a = assign.get(slot)
        if a is None:
            G += m
            continue
        kA, kB, th, brA, brB = a
        for k, br, wgt in ((kA, brA, th), (kB, brB, 1 - th)):
            if wgt == 0:
                continue
            if k == 0 or (kind == "tail" and br == "t"):
                G += wgt * m
            elif kind == "reg":
                G += wgt * (m / 2 + max(Fr(0), m - W / k) / 2)
            else:
                G += wgt * (m / 2 + max(Fr(0), v - W / k) / 2)
            if k > 0:
                bud += wgt * Fr(1, 2 * k)
    assert bud <= 1, f"budget {bud} > 1"
    return G
