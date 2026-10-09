#!/usr/bin/env python3
"""Exact arithmetic audit of the proposed 20/37 independent-row witness.

This verifies algebraic feasibility in the declared scan_lib universe.  It
does not prove the analytic soundness of that universe, nor an upper bound.
The exhaustive UN/CS/RM scan uses a common integer scale, so no floating
comparison occurs.
"""

from fractions import Fraction as F
from math import gcd

import numpy as np


RNG = range(1, 7)
SIDES = {"a": ("b", "c"), "b": ("a", "c"), "c": ("a", "b")}
NM = 128
TARGET = F(20, 37)
DEN = 37


def witness():
    p = {"D": TARGET}
    for s in "abc":
        p[s] = F(0)
        p[f"v{s}"] = F(0)
        for i in RNG:
            p[f"{s}{i}"] = F(0)
    p.update({
        "a": F(17, 37), "a1": F(7, 37), "a3": F(10, 37),
        "b": F(7, 37), "b1": F(2, 37), "vb": F(35, 37),
        "c": F(13, 37), "c1": F(5, 37), "c4": F(8, 37),
    })
    return p


P = witness()


def side_scalars(s):
    root_sum = sum(P[f"{s}{i}"] for i in RNG)
    tau = P[s] - root_sum
    val = sum(i * P[f"{s}{i}"] for i in RNG) + P[f"v{s}"]
    return root_sum, tau, val


def mask_tables_num(s):
    """Numerators over DEN of selected root mass and value mass."""
    root_sum, tau, _ = side_scalars(s)
    assert (DEN * root_sum).denominator == 1
    assert (DEN * tau).denominator == 1
    out_f = np.zeros(NM, dtype=np.int64)
    out_w = np.zeros(NM, dtype=np.int64)
    block = {i: int(DEN * P[f"{s}{i}"]) for i in RNG}
    tau_n = int(DEN * tau)
    v_n = int(DEN * P[f"v{s}"])
    for m in range(NM):
        out_f[m] = sum(block[i] for i in RNG if m & (1 << (i - 1)))
        out_w[m] = sum(i * block[i] for i in RNG if m & (1 << (i - 1)))
        if m & 64:
            out_f[m] += tau_n
            out_w[m] += v_n
    return out_f, out_w


def verify_base_geometry():
    D = P["D"]
    L = sum(P[s] for s in "abc")
    assert L <= 1
    assert all(x >= 0 for x in P.values())
    vals = {}
    for s in "abc":
        root_sum, tau, vals[s] = side_scalars(s)
        assert root_sum <= P[s]
        assert P[f"v{s}"] >= 7 * tau
        assert vals[s] <= 1
        assert 7 * P[s] - 1 <= sum((7 - i) * P[f"{s}{i}"] for i in RNG)
    assert D <= min(P["a"] + P["b"], P["a"] + P["c"], P["b"] + P["c"])
    m = {
        s: max(P[f"{s}2"] + P[f"{s}4"] + P[f"{s}6"],
               P[f"{s}3"] + P[f"{s}6"], P[f"{s}5"])
        for s in "abc"
    }
    assert sum(m.values()) <= 4 * L - 6 * D

    pf = {i: sum(P[f"{s}{i}"] for s in "abc") for i in RNG}
    pairs = []
    pairs.append((pf[1] + pf[2] + pf[4], 1 - pf[2] - 3 * pf[4]))
    for s in "abc":
        pairs.append((pf[1] + pf[2] + P[f"{s}3"],
                      1 - pf[2] - 2 * P[f"{s}3"]))
    for s, t in (("a", "b"), ("b", "c"), ("c", "a")):
        pairs.append((pf[1] + pf[2] + P[f"{s}3"] + P[f"{t}3"],
                      1 - pf[2] - 2 * P[f"{s}3"] - 2 * P[f"{t}3"]))
    for s in "abc":
        y, z = [u for u in "abc" if u != s]
        pairs.append((pf[1] + P[f"{s}3"] + P[f"{y}2"] + P[f"{z}2"],
                      1 - 2 * P[f"{s}3"] - P[f"{y}2"] - P[f"{z}2"]))
    for s in "abc":
        y, z = [u for u in "abc" if u != s]
        pairs.append((pf[1] + P[f"{s}2"] + P[f"{y}3"] + P[f"{z}3"],
                      1 - P[f"{s}2"] - 2 * P[f"{y}3"] - 2 * P[f"{z}3"]))
    assert len(pairs) == 13
    for e1, e2 in pairs:
        assert min(e1, e2) <= L - D
    return vals


def verify_static_and_moment(vals):
    D = P["D"]
    hb3 = sum(P[s] - P[f"{s}3"] for s in "abc")
    assert D <= hb3
    det = {}
    for k in (2, 4, 5, 6):
        det[k] = (sum(P[s] - P[f"{s}{k}"] for s in "abc")
                  + F(2, k) * max(P[f"{s}{k}"] for s in "abc"))
        assert D <= det[k]

    tabs = {s: mask_tables_num(s) for s in "abc"}
    ps_min = None
    ps_arg = None
    cs4_min = None
    cs4_arg = None
    for sig in "abc":
        s1, s2 = SIDES[sig]
        p_pair = P[s1] + P[s2]
        held_masses = [P[f"{s}{i}"] for s in (s1, s2) for i in RNG]
        # Guaranteed exact-seven root mass in each tail: rho=(8*tau-v)_+.
        for s in (s1, s2):
            _, tau, _ = side_scalars(s)
            held_masses.append(max(F(0), 8 * tau - P[f"v{s}"]))
        h4 = sum(sorted(held_masses, reverse=True)[:4])
        ft, wt = tabs[sig]
        for mt in range(1, NM):
            cost, W = F(int(ft[mt]), DEN), F(int(wt[mt]), DEN)
            gps = cost + p_pair - min(p_pair / 2, F(2, 3) * W)
            gcs = cost + p_pair - min(W, h4 / 2)
            if ps_min is None or gps < ps_min:
                ps_min, ps_arg = gps, (sig, mt)
            if cs4_min is None or gcs < cs4_min:
                cs4_min, cs4_arg = gcs, (sig, mt, h4)
    assert D <= ps_min
    assert D <= cs4_min
    return hb3, det, ps_min, ps_arg, cs4_min, cs4_arg


def verify_spacing():
    vals = {s: side_scalars(s)[2] for s in "abc"}
    best = None
    arg = None
    for e in "abc":
        o1, o2 = SIDES[e]
        for y, z in ((o1, o2), (o2, o1)):
            for k in range(2, 7):
                g = (P[y] + P[z] - P[f"{z}{k}"]
                     + max(F(0), vals[e] - vals[z] + P[f"{z}{k}"]))
                if best is None or g < best:
                    best, arg = g, (e, y, z, k)
    assert P["D"] <= best
    return best, arg


def q_matrix():
    basis = []
    for m in range(NM):
        if m & 64:
            basis.append(1)
        else:
            g = 0
            for i in RNG:
                if m & (1 << (i - 1)):
                    g = gcd(g, i)
            basis.append(g)
    q = np.ones((NM, NM), dtype=np.int64)
    for i in range(NM):
        for j in range(NM):
            q[i, j] = gcd(basis[i], basis[j]) or 1
    return q


def exact_scan_extended_un_cs_rm():
    # Common exact scale: 2*lcm(1,...,6)*DEN.  This clears q and every /2.
    scale = 120 * DEN
    unit = scale // DEN
    assert (scale * TARGET).denominator == 1
    target_i = int(scale * TARGET)
    qmat = q_matrix()
    tabs = {s: mask_tables_num(s) for s in "abc"}
    rad = {s: int(DEN * P[s]) for s in "abc"}
    val = {s: int(DEN * side_scalars(s)[2]) for s in "abc"}
    minima = {f: None for f in ("UN", "CS1", "CS2A", "CS2B", "CS3", "RMA", "RMB")}
    argmins = {f: None for f in minima}

    for sig in "abc":
        s1, s2 = SIDES[sig]
        f1, w1 = tabs[s1]
        f2, w2 = tabs[s2]
        ct, wt = tabs[sig]
        p1 = rad[s1] - f1
        p2 = rad[s2] - f2
        v1 = val[s1] - w1
        v2 = val[s2] - w2
        cost = ct[1:][None, None, :]
        W = wt[1:][None, None, :]
        Pp = p1[:, None, None] + p2[None, :, None]
        # Exact scaled positive part of (w1+w2)/q-W.
        mfw = np.maximum(
            0,
            (unit // qmat)[:, :, None] * (w1[:, None, None] + w2[None, :, None])
            - unit * W,
        )
        eb = unit * (f1[:, None, None] + f2[None, :, None]) + mfw
        mv12 = unit * np.maximum(0, v1[:, None, None] + v2[None, :, None] - W)
        mv1 = unit * np.maximum(0, v1[:, None, None] - W)
        mv2 = unit * np.maximum(0, v2[None, :, None] - W)
        pp_s = unit * Pp
        cost_s = unit * cost
        forms = {
            "UN": pp_s + cost_s + mfw,
            "CS1": cost_s + (pp_s + mv12 + eb) // 2,
            "CS2A": cost_s + (pp_s + unit * p2[None, :, None] + mv1 + eb) // 2,
            "CS2B": cost_s + (pp_s + unit * p1[:, None, None] + mv2 + eb) // 2,
            "CS3": cost_s + pp_s + eb // 2,
            "RMA": (cost_s + unit * p2[None, :, None] + mv1
                    + unit * (f1[:, None, None] + f2[None, :, None])),
            "RMB": (cost_s + unit * p1[:, None, None] + mv2
                    + unit * (f1[:, None, None] + f2[None, :, None])),
        }
        for name, arr in forms.items():
            # The extended row universe has exactly
            # 3*(128^2-1)*127 tuples: (R1,R2)=(empty,empty) is excluded.
            arr[0, 0, :] = np.iinfo(np.int64).max
            flat_ix = int(np.argmin(arr))
            value = int(arr.ravel()[flat_ix])
            if minima[name] is None or value < minima[name]:
                m1, rem = divmod(flat_ix, NM * (NM - 1))
                m2, mt0 = divmod(rem, NM - 1)
                minima[name] = value
                argmins[name] = (sig, m1, m2, mt0 + 1)

    for name, value in minima.items():
        assert value >= target_i, (name, value, target_i, argmins[name])
    return scale, minima, argmins


def main():
    vals = verify_base_geometry()
    hb3, det, ps_min, ps_arg, cs_min, cs_arg = verify_static_and_moment(vals)
    spacing_min, spacing_arg = verify_spacing()
    scale, minima, argmins = exact_scan_extended_un_cs_rm()
    print("EXACT_WITNESS_PASS")
    print(f"D={P['D']} L={sum(P[s] for s in 'abc')} vals={vals}")
    print(f"HB3={hb3}; DET={det}")
    print(f"PS23 minimum={ps_min} at {ps_arg}")
    print(f"CS4(exact-seven-safe) minimum={cs_min} at {cs_arg}")
    print(f"Spacing minimum={spacing_min} at {spacing_arg}")
    for name in minima:
        print(f"{name} minimum={F(minima[name], scale)} at {argmins[name]}")


if __name__ == "__main__":
    main()
