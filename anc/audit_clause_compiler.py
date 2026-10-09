#!/usr/bin/env python3
"""Exact randomized equivalence checks for dynamic_tree_ind clause arms."""

import random
from fractions import Fraction as F

from dynamic_tree_ind import (ARCH, DET, GEOMETRY, IDX, NM, POW3A_ALLOWED,
                              GROUP12A_C_SINGLETON_POOL,
                              GROUP12B_C_SINGLETON_POOL,
                              GROUP1212A_SINGLETON_POOL,
                              GROUP1212B_SINGLETON_POOL, RNG, SIDES,
                              SPACING, SPACING_META, VARS, cs4_clause,
                              group12a_c_clause, group12b_c_clause,
                              group1212a_clause, group1212b_clause,
                              group12c_clause, pow3_clause,
                              pow3b_clause, prop_clause, ps_clause)
from scan_lib import eval_forms_exact, mask_elems, TAIL


random.seed(20260719)


def profile():
    p = {}
    for s in "abc":
        blocks = {i: F(random.randrange(0, 7), 37) for i in RNG}
        tau = F(random.randrange(0, 7), 37)
        p[s] = sum(blocks.values()) + tau
        for i, v in blocks.items():
            p[f"{s}{i}"] = v
        p[f"v{s}"] = 7 * tau + F(random.randrange(0, 7), 37)
    return p


def arm_g(arm, p):
    d, rhs, _ = arm
    # row is D-G <= 0 (or <= rhs); evaluate at D=0.
    lhs0 = sum(v * p.get(k, F(0)) for k, v in d.items() if k != "D")
    return rhs - lhs0


forms = ("UN", "CS1", "CS2A", "CS2B", "CS3", "RMA", "RMB")
for _ in range(500):
    p = profile()
    pf = {i: sum(p[f"{s}{i}"] for s in "abc") for i in RNG}
    geom_pairs = [(pf[1] + pf[2] + pf[4], 1 - pf[2] - 3 * pf[4])]
    for s in "abc":
        geom_pairs.append((pf[1] + pf[2] + p[f"{s}3"],
                           1 - pf[2] - 2 * p[f"{s}3"]))
    for s, t in (("a", "b"), ("b", "c"), ("c", "a")):
        geom_pairs.append((pf[1] + pf[2] + p[f"{s}3"] + p[f"{t}3"],
                           1 - pf[2] - 2 * p[f"{s}3"] - 2 * p[f"{t}3"]))
    for s in "abc":
        y, z = [u for u in "abc" if u != s]
        geom_pairs.append((pf[1] + p[f"{s}3"] + p[f"{y}2"] + p[f"{z}2"],
                           1 - 2 * p[f"{s}3"] - p[f"{y}2"] - p[f"{z}2"]))
    for s in "abc":
        y, z = [u for u in "abc" if u != s]
        geom_pairs.append((pf[1] + p[f"{s}2"] + p[f"{y}3"] + p[f"{z}3"],
                           1 - p[f"{s}2"] - 2 * p[f"{y}3"] - 2 * p[f"{z}3"]))
    L = sum(p[s] for s in "abc")
    assert len(geom_pairs) == len(GEOMETRY) == 13
    for (_, arms), (e1, e2) in zip(GEOMETRY, geom_pairs):
        assert max(arm_g(a, p) for a in arms) == L - min(e1, e2)

    for k, (_, arms) in zip((2, 4, 5, 6), DET):
        expected = (sum(p[s] - p[f"{s}{k}"] for s in "abc")
                    + F(2, k) * max(p[f"{s}{k}"] for s in "abc"))
        assert max(arm_g(a, p) for a in arms) == expected

    vals = {s: sum(i * p[f"{s}{i}"] for i in RNG) + p[f"v{s}"]
            for s in "abc"}
    assert len(ARCH) == 1 and ARCH[0][0] == "ARCH:max"
    arch_arms = ARCH[0][1]
    arch_lhs = []
    for arm in arch_arms:
        coeff, rhs, _label = arm
        arch_lhs.append(sum(value * p.get(variable, F(0))
                            for variable, value in coeff.items()) - rhs)
    assert tuple(arch_lhs) == (vals["c"] - vals["a"],
                               vals["c"] - vals["b"])
    isp = 0
    for e in "abc":
        o1, o2 = SIDES[e]
        for y, z in ((o1, o2), (o2, o1)):
            for k in range(2, 7):
                _, arms = SPACING[isp]
                expected = (p[y] + p[z] - p[f"{z}{k}"]
                            + max(F(0), vals[e] - vals[z] + p[f"{z}{k}"]))
                assert max(arm_g(a, p) for a in arms) == expected
                isp += 1
    assert isp == 30
    # Exact Boolean compression: AND_k(B OR A_k) == B OR AND_k(A_k).
    Dtest = F(random.randrange(0, 100), 37)
    for imeta, (_, branches) in enumerate(SPACING_META):
        original = SPACING[5 * imeta:5 * imeta + 5]
        lhs = all(Dtest <= max(arm_g(a, p) for a in arms)
                  for _, arms in original)
        b_ok = Dtest <= arm_g(branches[0][1][0], p)
        aall_ok = all(Dtest <= arm_g(a, p) for a in branches[1][1])
        assert lhs == (b_ok or aall_ok)

    sig = random.choice("abc")
    m1 = random.randrange(NM)
    m2 = random.randrange(NM)
    if m1 == m2 == 0:
        m1 = 1
    mt = random.randrange(1, NM)
    exact = eval_forms_exact(p, sig, m1, m2, mt, restrict_hyp_T=True)
    for form in forms:
        _, arms = prop_clause(form, sig, m1, m2, mt)
        got = max(arm_g(a, p) for a in arms)
        assert got == exact[form], (form, sig, m1, m2, mt, got, exact[form])

    _, psarms = ps_clause(sig, mt)
    s1, s2 = SIDES[sig]
    tau = p[sig] - sum(p[f"{sig}{i}"] for i in RNG)
    C = sum(p[f"{sig}{j}"] for j in mask_elems(mt) if j != TAIL)
    W = sum(j * p[f"{sig}{j}"] for j in mask_elems(mt) if j != TAIL)
    if TAIL in mask_elems(mt):
        C += tau
        W += p[f"v{sig}"]
    pair = p[s1] + p[s2]
    gps = C + pair - min(pair / 2, F(2, 3) * W)
    assert max(arm_g(a, p) for a in psarms) == gps

    slots = [f"{s}{i}" for s in (s1, s2) for i in RNG]
    held = tuple(random.sample(slots, 4))
    _, csarms = cs4_clause(sig, mt, held)
    h = sum(p[u] for u in held)
    gcs = C + pair - min(W, h / 2)
    assert max(arm_g(a, p) for a in csarms) == gcs

    pow_slots = [f"{side}{index}" for side in "ac" for index in RNG]
    pow_held = tuple(sorted(random.sample(pow_slots, 4)))
    _, pow_arms = pow3b_clause(pow_held)
    pow_C = p["b"] - p["b3"] - p["b6"]
    pow_R = p["a"] + p["c"]
    pow_P = sum(p[slot] for slot in pow_held)
    pow_S = pow_C + pow_R - pow_P / 2
    pow_expected = max(pow_S, (pow_S + pow_R) / 2)
    assert max(arm_g(arm, p) for arm in pow_arms) == pow_expected

    pow_a_held = random.choice(POW3A_ALLOWED)
    _, pow_a_arms = pow3_clause("a", pow_a_held)
    pow_a_C = p["a"] - p["a3"] - p["a6"]
    pow_a_R = p["b"] + p["c"]
    pow_a_P = sum(p[slot] for slot in pow_a_held)
    pow_a_S = pow_a_C + pow_a_R - pow_a_P / 2
    pow_a_expected = max(pow_a_S, (pow_a_S + pow_a_R) / 2)
    assert max(arm_g(arm, p) for arm in pow_a_arms) == pow_a_expected

    pow_c_slots = [f"{side}{index}" for side in "ab" for index in RNG]
    pow_c_held = tuple(sorted(random.sample(pow_c_slots, 4)))
    _, pow_c_arms = pow3_clause("c", pow_c_held)
    pow_c_C = p["c"] - p["c3"] - p["c6"]
    pow_c_R = p["a"] + p["b"]
    pow_c_P = sum(p[slot] for slot in pow_c_held)
    pow_c_S = pow_c_C + pow_c_R - pow_c_P / 2
    pow_c_expected = max(pow_c_S, (pow_c_S + pow_c_R) / 2)
    assert max(arm_g(arm, p) for arm in pow_c_arms) == pow_c_expected

    for group_side in "ab":
        other_side = "b" if group_side == "a" else "a"
        _, group_arms = group12c_clause(group_side)
        group_C = p["c"] - p["c3"] - p["c6"]
        group_W = (p["vc"] + p["c1"] + 2 * p["c2"]
                   + p["c4"] + 2 * p["c5"])
        group_R = p["a"] + p["b"]
        retained = (f"{group_side}1", f"{group_side}2",
                    f"{group_side}4", f"{other_side}1",
                    f"{other_side}4")
        group_P = sum(p[slot] for slot in retained)
        group_L = p[f"{group_side}1"] + 2 * p[f"{group_side}2"]
        group_S = group_C + group_R - group_P / 2
        expected = (group_S, (group_S + group_R) / 2,
                    group_S + group_L - group_W / 2)
        assert tuple(arm_g(arm, p) for arm in group_arms) == expected

    single_combo = tuple(random.sample(GROUP12A_C_SINGLETON_POOL, 3))
    singletons = (tuple(sorted(slot for slot in single_combo if slot[0] == "c"))
                  + tuple(sorted(slot for slot in single_combo if slot[0] == "b")))
    _, group_a_arms = group12a_c_clause(singletons)
    group_a_C = p["a"] - p["a3"] - p["a6"]
    group_a_W = p["va"] + p["a1"] + 2*p["a2"] + p["a4"] + 2*p["a5"]
    group_a_R = p["b"] + p["c"]
    group_a_P = p["c1"] + p["c2"] + sum(p[slot] for slot in singletons)
    group_a_L = p["c1"] + 2*p["c2"]
    group_a_S = group_a_C + group_a_R - group_a_P/2
    assert tuple(arm_g(arm, p) for arm in group_a_arms) == (
        group_a_S, (group_a_S + group_a_R)/2,
        group_a_S + group_a_L - group_a_W/2)

    double_combo = tuple(random.sample(GROUP1212A_SINGLETON_POOL, 2))
    doubletons = tuple(sorted(double_combo, key=lambda slot: (slot[0], slot[1])))
    _, double_arms = group1212a_clause(doubletons)
    double_P = (p["b1"] + p["b2"] + p["c1"] + p["c2"]
                + sum(p[slot] for slot in doubletons))
    double_S = group_a_C + group_a_R - double_P/2
    double_Lb = p["b1"] + 2*p["b2"]
    double_Lc = p["c1"] + 2*p["c2"]
    assert tuple(arm_g(arm, p) for arm in double_arms) == (
        double_S, (double_S + group_a_R)/2,
        double_S + double_Lb - group_a_W/2,
        double_S + double_Lc - group_a_W/2)

    single_b_combo = tuple(random.sample(GROUP12B_C_SINGLETON_POOL, 3))
    single_b = (tuple(sorted(slot for slot in single_b_combo
                             if slot[0] == "c"))
                + tuple(sorted(slot for slot in single_b_combo
                               if slot[0] == "a")))
    _, group_b_arms = group12b_c_clause(single_b)
    group_b_C = p["b"] - p["b3"] - p["b6"]
    group_b_W = p["vb"] + p["b1"] + 2*p["b2"] + p["b4"] + 2*p["b5"]
    group_b_R = p["a"] + p["c"]
    group_b_P = p["c1"] + p["c2"] + sum(p[slot] for slot in single_b)
    group_b_L = p["c1"] + 2*p["c2"]
    group_b_S = group_b_C + group_b_R - group_b_P/2
    assert tuple(arm_g(arm, p) for arm in group_b_arms) == (
        group_b_S, (group_b_S + group_b_R)/2,
        group_b_S + group_b_L - group_b_W/2)

    double_b_combo = tuple(random.sample(GROUP1212B_SINGLETON_POOL, 2))
    double_b = tuple(sorted(double_b_combo,
                            key=lambda slot: (slot[0], slot[1])))
    _, double_b_arms = group1212b_clause(double_b)
    double_b_P = (p["a1"] + p["a2"] + p["c1"] + p["c2"]
                  + sum(p[slot] for slot in double_b))
    double_b_S = group_b_C + group_b_R - double_b_P/2
    double_La = p["a1"] + 2*p["a2"]
    double_Lc = p["c1"] + 2*p["c2"]
    assert tuple(arm_g(arm, p) for arm in double_b_arms) == (
        double_b_S, (double_b_S + group_b_R)/2,
        double_b_S + double_La - group_b_W/2,
        double_b_S + double_Lc - group_b_W/2)

print("EXACT_CLAUSE_COMPILER_AUDIT_PASS "
      "samples=500 forms=3500+PS+CS4+POW3abc+ARCH+GROUP12c+GROUP12ab+GROUP1212ab+geometry+DET+Spacing")
