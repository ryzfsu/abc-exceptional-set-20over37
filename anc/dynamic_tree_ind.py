#!/usr/bin/env python3
"""On-demand disjunctive proof-tree prototype for D <= 20/37.

The search LPs are floating-point guides.  A node is pruned only after an
exact rational dual certificate has been reconstructed and checked.  Every
branch is a union over all arms of one valid OR clause; arms are not treated
as mutually exclusive.

This prototype uses regular-block CS4 and globally valid unlocalized POW2
and POW3 rows.  All four-block POW2 rows are target-safe.  All four-block
POW3(b) and sum-quotient POW3(c) rows are allowed.  POW3(a) rows use the
exact target-safe subfamily whose retained mass at the displayed 20/37
equality witness is at most 14/37.
Failure to close is therefore inconclusive for stronger row packages;
successful closure is sufficient because every installed row is valid.
"""

import argparse
import itertools
import json
import sys
import time
from fractions import Fraction as F

import numpy as np
from scipy.optimize import linprog

from scan_lib import (NM, QMAT, RNG, SIDES, TAIL, mask_elems,
                      scan_forms_np, side_tables)


TARGET = F(20, 37)
VARS = (["D", "a", "b", "c"]
        + [f"{s}{i}" for s in "abc" for i in RNG]
        + [f"v{s}" for s in "abc"]
        + [f"m{s}" for s in "abc"])
IDX = {v: i for i, v in enumerate(VARS)}
NVAR = len(VARS)
assert NVAR == 28


# For powered side a, represented slots lie on b,c.  At the target equality
# witness their only nonzero masses are b1=2/37, c1=5/37, c4=8/37.  The POW3
# bound preserves D=20/37 exactly when P_J <= 14/37.  Store the numerator
# test here so the dynamic separator can never install an unsafe descriptor.
POW3A_TARGET_MASS_NUM = {"b1": 2, "c1": 5, "c4": 8}
POW3A_ALLOWED = tuple(
    held for held in itertools.combinations(
        tuple(f"{side}{index}" for side in "bc" for index in RNG), 4)
    if sum(POW3A_TARGET_MASS_NUM.get(slot, 0) for slot in held) <= 14
)
assert len(POW3A_ALLOWED) == 486


def merge(*terms):
    out = {}
    for coeff, scale in terms:
        scale = F(scale)
        for k, v in coeff.items():
            out[k] = out.get(k, F(0)) + scale * F(v)
    return {k: v for k, v in out.items() if v}


def row(coeff, rhs=0, label=""):
    return ({k: F(v) for k, v in coeff.items() if v}, F(rhs), label)


def upper_arm(g, label):
    """The linear arm D <= g(x), encoded coeff.x <= 0."""
    return row(merge(({"D": 1}, 1), (g, -1)), 0, label)


def eval_row(r, x):
    d, rhs, _ = r
    return sum(float(v) * x[IDX[k]] for k, v in d.items()) - float(rhs)


def to_np(rows):
    A = np.zeros((len(rows), NVAR))
    b = np.zeros(len(rows))
    for ir, (d, rhs, _) in enumerate(rows):
        for k, v in d.items():
            A[ir, IDX[k]] = float(v)
        b[ir] = float(rhs)
    return A, b


def p(i):
    return {f"{s}{i}": F(1) for s in "abc"}


def val_expr(s):
    return {**{f"{s}{i}": F(i) for i in RNG}, f"v{s}": F(1)}


def make_base():
    out = [row({"a": 1, "b": 1, "c": 1}, 1, "L")]
    for s in "abc":
        out.append(row(merge(({f"{s}{i}": 1 for i in RNG}, 1), ({s: 1}, -1)),
                       0, f"roots<={s}"))
        out.append(row(merge(({s: 7}, 1),
                             ({f"{s}{i}": 7 for i in RNG}, -1),
                             ({f"v{s}": 1}, -1)), 0, f"tail7-{s}"))
        out.append(row({**{f"{s}{i}": F(i) for i in RNG}, f"v{s}": 1},
                       1, f"val-{s}"))
        out.append(row({s: 7, **{f"{s}{i}": -(7 - i) for i in RNG}},
                       1, f"rad-{s}"))
        for j, inds in enumerate(((2, 4, 6), (3, 6), (5,))):
            out.append(row({**{f"{s}{i}": 1 for i in inds}, f"m{s}": -1},
                           0, f"fourier-{s}-{j}"))
    for y, z in (("a", "b"), ("a", "c"), ("b", "c")):
        out.append(row({"D": 1, y: -1, z: -1}, 0, f"pair-{y}{z}"))
    out.append(row({"ma": 1, "mb": 1, "mc": 1,
                    "a": -4, "b": -4, "c": -4, "D": 6},
                   0, "fourier-sum"))
    out.append(row({"D": 1, "a": -1, "b": -1, "c": -1,
                    "a3": 1, "b3": 1, "c3": 1}, 0, "HB3"))
    # Positive a+b=c forces each addend to be no larger than c.  These are
    # the homogeneous half of the frozen archimedean root cover.
    out.append(row(merge((val_expr("a"), 1), (val_expr("c"), -1)),
                   0, "ARCH:a<=c"))
    out.append(row(merge((val_expr("b"), 1), (val_expr("c"), -1)),
                   0, "ARCH:b<=c"))
    return out


BASE = make_base()


def make_arch():
    """Homogeneous cover c <= 2*max(a,b) at exponent precision.

    Together with the two base rows above this states
    value_c=max(value_a,value_b), up to the finite-eta slack absorbed in
    X^epsilon.  It is the scale-free form of the production tree's two
    normalized archimedean root branches.
    """
    return [("ARCH:max", [
        row(merge((val_expr("c"), 1), (val_expr("a"), -1)),
            0, "ARCH:max-a"),
        row(merge((val_expr("c"), 1), (val_expr("b"), -1)),
            0, "ARCH:max-b"),
    ])]


ARCH = make_arch()


def make_geometry():
    clauses = []
    L = {"a": 1, "b": 1, "c": 1}

    def add(name, e1, c1, e2, c2):
        # min(e1+c1,e2+c2) <= L-D, so D <= max(L-e1-c1,L-e2-c2).
        g1 = merge((L, 1), (e1, -1))
        g2 = merge((L, 1), (e2, -1))
        clauses.append((name, [row(merge(({"D": 1}, 1), (g1, -1)), -F(c1), name+":0"),
                               row(merge(({"D": 1}, 1), (g2, -1)), -F(c2), name+":1")]))

    add("G0", merge((p(1), 1), (p(2), 1), (p(4), 1)), 0,
        merge((p(2), -1), (p(4), -3)), 1)
    for s in "abc":
        add(f"G1-{s}", merge((p(1), 1), (p(2), 1), ({f"{s}3": 1}, 1)), 0,
            merge((p(2), -1), ({f"{s}3": -2}, 1)), 1)
    for s, t in (("a", "b"), ("b", "c"), ("c", "a")):
        add(f"G2-{s}{t}",
            merge((p(1), 1), (p(2), 1), ({f"{s}3": 1, f"{t}3": 1}, 1)), 0,
            merge((p(2), -1), ({f"{s}3": -2, f"{t}3": -2}, 1)), 1)
    for s in "abc":
        y, z = [u for u in "abc" if u != s]
        add(f"G3-{s}",
            merge((p(1), 1), ({f"{s}3": 1, f"{y}2": 1, f"{z}2": 1}, 1)), 0,
            {f"{s}3": -2, f"{y}2": -1, f"{z}2": -1}, 1)
    for s in "abc":
        y, z = [u for u in "abc" if u != s]
        add(f"G4-{s}",
            merge((p(1), 1), ({f"{s}2": 1, f"{y}3": 1, f"{z}3": 1}, 1)), 0,
            {f"{s}2": -1, f"{y}3": -2, f"{z}3": -2}, 1)
    assert len(clauses) == 13
    return clauses


GEOMETRY = make_geometry()


def make_det():
    clauses = []
    for k in (2, 4, 5, 6):
        base = merge(({s: 1 for s in "abc"}, 1),
                     ({f"{s}{k}": 1 for s in "abc"}, -1))
        arms = []
        for s in "abc":
            g = merge((base, 1), ({f"{s}{k}": F(2, k)}, 1))
            arms.append(upper_arm(g, f"DET{k}:{s}"))
        clauses.append((f"DET{k}", arms))
    return clauses


DET = make_det()


def make_spacing():
    clauses = []
    for e in "abc":
        o1, o2 = SIDES[e]
        for y, z in ((o1, o2), (o2, o1)):
            for k in range(2, 7):
                base = {y: F(1), z: F(1), f"{z}{k}": F(-1)}
                excess = merge((val_expr(e), 1), (val_expr(z), -1),
                               ({f"{z}{k}": 1}, 1))
                key = f"SP:{e}:{y}:{z}:{k}"
                arms = [upper_arm(base, key+":0"),
                        upper_arm(merge((base, 1), (excess, 1)), key+":1")]
                clauses.append((key, arms))
    assert len(clauses) == 30
    return clauses


SPACING = make_spacing()


def make_spacing_meta():
    """Compress five clauses (B or A_k) to B or (A_2 and ... and A_6)."""
    clauses = []
    for e in "abc":
        o1, o2 = SIDES[e]
        for y, z in ((o1, o2), (o2, o1)):
            prefix = f"SPM:{e}:{y}:{z}"
            gB = merge(({y: 1, z: 1}, 1), (val_expr(e), 1),
                       (val_expr(z), -1))
            rowB = upper_arm(gB, prefix + ":B")
            rowsA = [upper_arm({y: 1, z: 1, f"{z}{k}": -1},
                               prefix + f":A{k}")
                     for k in range(2, 7)]
            branches = [(prefix + ":B", [rowB]),
                        (prefix + ":AALL", rowsA)]
            clauses.append((prefix, branches))
    assert len(clauses) == 6
    return clauses


SPACING_META = make_spacing_meta()


def fw_expr(s, mask):
    f = {}
    w = {}
    for j in mask_elems(mask):
        if j == TAIL:
            f = merge((f, 1), ({s: 1}, 1), ({f"{s}{i}": 1 for i in RNG}, -1))
            w = merge((w, 1), ({f"v{s}": 1}, 1))
        else:
            f = merge((f, 1), ({f"{s}{j}": 1}, 1))
            w = merge((w, 1), ({f"{s}{j}": j}, 1))
    return f, w


def ps_clause(sig, mt):
    cost, W = fw_expr(sig, mt)
    y, z = SIDES[sig]
    pair = {y: 1, z: 1}
    g0 = merge((cost, 1), (pair, F(1, 2)))
    g1 = merge((cost, 1), (pair, 1), (W, F(-2, 3)))
    key = f"PS:{sig}:{mt}"
    return key, [upper_arm(g0, key+":half"), upper_arm(g1, key+":2W3")]


def cs4_clause(sig, mt, held):
    cost, W = fw_expr(sig, mt)
    y, z = SIDES[sig]
    pair = {y: 1, z: 1}
    h = {slot: 1 for slot in held}
    g0 = merge((cost, 1), (pair, 1), (W, -1))
    g1 = merge((cost, 1), (pair, 1), (h, F(-1, 2)))
    hs = ",".join(held)
    key = f"CS4:{sig}:{mt}:{hs}"
    return key, [upper_arm(g0, key+":W"), upper_arm(g1, key+":h2")]


def pow_clause(k, sig, held):
    """Global unlocalized POW-k row for side ``sig`` and regular |J|=4.

    With C=sig-sum_{k|i}sig_i, R=sum(other radicals), and P_J=sum(held),
    put S=C+R-P_J/2.
    The direct pair row already supplies D<=R; the power sieve supplies the
    exact OR D<=S or D<=(S+R)/2.
    """
    assert k in (2, 3)
    assert sig in "abc"
    represented = tuple(side for side in "abc" if side != sig)
    assert len(held) == 4 and len(set(held)) == 4
    assert tuple(sorted(held)) == tuple(held)
    assert all(slot[0] in represented and slot[1:] in tuple(map(str, RNG))
               for slot in held)
    if k == 3 and sig == "a":
        assert tuple(held) in POW3A_ALLOWED
    C = {sig: F(1)}
    C.update({f"{sig}{i}": F(-1) for i in RNG if i % k == 0})
    R = {side: F(1) for side in represented}
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    held_text = ",".join(held)
    key = f"POW{k}{sig}:{held_text}"
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg")]


def pow3_clause(sig, held):
    """Compatibility wrapper for the established cubic rows."""
    return pow_clause(3, sig, held)


def pow3b_clause(held):
    """Compatibility wrapper used by the earlier independent audit."""
    return pow3_clause("b", held)


def mix3c_fiveblock_clause():
    """Fixed mixed-moment POW3(c) row for the 152/281 face.

    Retain a1 at L^6, a2 at L^12, and a4,b1,b4 at L^4.  The Holder
    budgets are 1/6+1/12+3/4=1.  With Q=Mr and r=pq, half-cost for the two
    higher moments requires W+2*theta >= 3*a1 and >= 6*a2.  Optimizing the
    ordinary POW3 generic/diagonal pair subject to those lower bounds gives
    the four affine OR arms below; the direct pair row supplies D<=R.
    """
    C = {"c": F(1), "c3": F(-1), "c6": F(-1)}
    W = {"vc": F(1), "c1": F(1), "c2": F(2),
         "c4": F(1), "c5": F(2)}
    R = {"a": F(1), "b": F(1)}
    held = ("a1", "a2", "a4", "b1", "b4")
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    gate6 = merge((S, 1), ({"a1": F(3)}, F(1, 2)),
                  (W, F(-1, 2)))
    gate12 = merge((S, 1), ({"a2": F(6)}, F(1, 2)),
                   (W, F(-1, 2)))
    key = "MIX3c:a1q6,a2q12,a4q4,b1q4,b4q4"
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg"),
                 upper_arm(gate6, key + ":gate6"),
                 upper_arm(gate12, key + ":gate12")]


GROUP12A_C_SINGLETON_POOL = (
    tuple(f"c{i}" for i in range(3, 7))
    + tuple(f"b{i}" for i in range(1, 7))
)
GROUP12B_C_SINGLETON_POOL = (
    tuple(f"c{i}" for i in range(3, 7))
    + tuple(f"a{i}" for i in range(1, 7))
)
GROUP1212A_SINGLETON_POOL = (
    tuple(f"b{i}" for i in range(3, 7))
    + tuple(f"c{i}" for i in range(3, 7))
)
GROUP1212B_SINGLETON_POOL = (
    tuple(f"a{i}" for i in range(3, 7))
    + tuple(f"c{i}" for i in range(3, 7))
)


def canonical_group12a_c_singletons(singletons):
    assert isinstance(singletons, tuple) and len(singletons) == 3
    assert len(set(singletons)) == 3
    assert set(singletons) <= set(GROUP12A_C_SINGLETON_POOL)
    canonical = (tuple(sorted(slot for slot in singletons if slot[0] == "c"))
                 + tuple(sorted(slot for slot in singletons if slot[0] == "b")))
    assert singletons == canonical
    return singletons


def group12a_c_clause(singletons):
    """Full target-safe powered-a family with grouped c1*c2^2."""
    singletons = canonical_group12a_c_singletons(singletons)
    C = {"a": F(1), "a3": F(-1), "a6": F(-1)}
    W = {"va": F(1), "a1": F(1), "a2": F(2),
         "a4": F(1), "a5": F(2)}
    R = {"b": F(1), "c": F(1)}
    held = ("c1", "c2") + singletons
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    length = {"c1": F(1), "c2": F(2)}
    gate = merge((S, 1), (length, 1), (W, F(-1, 2)))
    key = "GROUP12a:c1c2sq+" + "+".join(singletons)
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg"),
                 upper_arm(gate, key + ":gate")]


def canonical_group12b_c_singletons(singletons):
    assert isinstance(singletons, tuple) and len(singletons) == 3
    assert len(set(singletons)) == 3
    assert set(singletons) <= set(GROUP12B_C_SINGLETON_POOL)
    canonical = (tuple(sorted(slot for slot in singletons if slot[0] == "c"))
                 + tuple(sorted(slot for slot in singletons if slot[0] == "a")))
    assert singletons == canonical
    return singletons


def group12b_c_clause(singletons):
    """Full target-safe powered-b family with grouped c1*c2^2."""
    singletons = canonical_group12b_c_singletons(singletons)
    C = {"b": F(1), "b3": F(-1), "b6": F(-1)}
    W = {"vb": F(1), "b1": F(1), "b2": F(2),
         "b4": F(1), "b5": F(2)}
    R = {"a": F(1), "c": F(1)}
    held = ("c1", "c2") + singletons
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    length = {"c1": F(1), "c2": F(2)}
    gate = merge((S, 1), (length, 1), (W, F(-1, 2)))
    key = "GROUP12b:c1c2sq+" + "+".join(singletons)
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg"),
                 upper_arm(gate, key + ":gate")]


def canonical_group1212a_singletons(singletons):
    assert isinstance(singletons, tuple) and len(singletons) == 2
    assert len(set(singletons)) == 2
    assert set(singletons) <= set(GROUP1212A_SINGLETON_POOL)
    canonical = tuple(sorted(singletons, key=lambda slot: (slot[0], slot[1])))
    assert singletons == canonical
    return singletons


def group1212a_clause(singletons):
    """Powered-a family with grouped b1*b2^2 and c1*c2^2."""
    singletons = canonical_group1212a_singletons(singletons)
    C = {"a": F(1), "a3": F(-1), "a6": F(-1)}
    W = {"va": F(1), "a1": F(1), "a2": F(2),
         "a4": F(1), "a5": F(2)}
    R = {"b": F(1), "c": F(1)}
    held = ("b1", "b2", "c1", "c2") + singletons
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    length_b = {"b1": F(1), "b2": F(2)}
    length_c = {"c1": F(1), "c2": F(2)}
    gate_b = merge((S, 1), (length_b, 1), (W, F(-1, 2)))
    gate_c = merge((S, 1), (length_c, 1), (W, F(-1, 2)))
    key = "GROUP1212a:b1b2sq+c1c2sq+" + "+".join(singletons)
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg"),
                 upper_arm(gate_b, key + ":gate-b"),
                 upper_arm(gate_c, key + ":gate-c")]


def canonical_group1212b_singletons(singletons):
    assert isinstance(singletons, tuple) and len(singletons) == 2
    assert len(set(singletons)) == 2
    assert set(singletons) <= set(GROUP1212B_SINGLETON_POOL)
    canonical = tuple(sorted(singletons, key=lambda slot: (slot[0], slot[1])))
    assert singletons == canonical
    return singletons


def group1212b_clause(singletons):
    """Powered-b family with grouped a1*a2^2 and c1*c2^2."""
    singletons = canonical_group1212b_singletons(singletons)
    C = {"b": F(1), "b3": F(-1), "b6": F(-1)}
    W = {"vb": F(1), "b1": F(1), "b2": F(2),
         "b4": F(1), "b5": F(2)}
    R = {"a": F(1), "c": F(1)}
    held = ("a1", "a2", "c1", "c2") + singletons
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    length_a = {"a1": F(1), "a2": F(2)}
    length_c = {"c1": F(1), "c2": F(2)}
    gate_a = merge((S, 1), (length_a, 1), (W, F(-1, 2)))
    gate_c = merge((S, 1), (length_c, 1), (W, F(-1, 2)))
    key = "GROUP1212b:a1a2sq+c1c2sq+" + "+".join(singletons)
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg"),
                 upper_arm(gate_a, key + ":gate-a"),
                 upper_arm(gate_c, key + ":gate-c")]


def group12_clause(powered_side, group_side, other_index=4):
    """Authorized grouped-factor POW3 row with an exact-1/exact-2 pair.

    On a represented ``group_side``, treat F_1(chi) F_2(chi**2) as one Dirichlet
    polynomial G(chi), and combine it by fourfold Holder with that side's
    exact-4 singleton and the other side's exact-1 plus one authorized
    regular singleton.
    If Q has exponent W+2*theta and

        W + 2*theta >= 2*(s1 + 2*s2),

    full-character orthogonality followed by divisor bounds gives the
    required fourth moment for G.  Optimizing theta subject to this gate
    gives the three affine alternatives below.  The direct pair row still
    supplies D <= R.
    """
    if powered_side in "ab":
        assert group_side == "c" and other_index in range(1, 7)
        other_side = "b" if powered_side == "a" else "a"
        raw = ("c4", f"{other_side}1", f"{other_side}{other_index}")
        if powered_side == "a":
            singletons = canonical_group12a_c_singletons(
                ("c4",) + tuple(sorted(raw[1:])))
            return group12a_c_clause(singletons)
        singletons = canonical_group12b_c_singletons(
            ("c4",) + tuple(sorted(raw[1:])))
        return group12b_c_clause(singletons)
    assert (powered_side, group_side, other_index) in {
        ("c", "a", 4), ("c", "b", 4)}
    represented = tuple(side for side in "abc" if side != powered_side)
    other_side = next(side for side in represented if side != group_side)
    C = {powered_side: F(1), f"{powered_side}3": F(-1),
         f"{powered_side}6": F(-1)}
    W = {f"v{powered_side}": F(1), f"{powered_side}1": F(1),
         f"{powered_side}2": F(2), f"{powered_side}4": F(1),
         f"{powered_side}5": F(2)}
    R = {side: F(1) for side in represented}
    held = tuple(sorted((f"{group_side}1", f"{group_side}2",
                         f"{group_side}4", f"{other_side}1",
                         f"{other_side}{other_index}")))
    P = {slot: F(1) for slot in held}
    S = merge((C, 1), (R, 1), (P, F(-1, 2)))
    average = merge((S, F(1, 2)), (R, F(1, 2)))
    length = {f"{group_side}1": F(1), f"{group_side}2": F(2)}
    gate = merge((S, 1), (length, 1), (W, F(-1, 2)))
    singles = "+".join((f"{group_side}4", f"{other_side}1",
                        f"{other_side}{other_index}"))
    key = (f"GROUP12{powered_side}:"
           f"{group_side}1{group_side}2sq+{singles}")
    return key, [upper_arm(S, key + ":S"),
                 upper_arm(average, key + ":avg"),
                 upper_arm(gate, key + ":gate")]


def group12c_clause(group_side):
    """Compatibility wrapper for the two established POW3(c) rows."""
    return group12_clause("c", group_side)


def group12c_b12_clause():
    """Compatibility wrapper for the first discovered grouped row."""
    return group12c_clause("b")


def prop_clause(form, sig, m1, m2, mt):
    s1, s2 = SIDES[sig]
    C, W = fw_expr(sig, mt)
    f1, w1 = fw_expr(s1, m1)
    f2, w2 = fw_expr(s2, m2)
    P1 = merge(({s1: 1}, 1), (f1, -1))
    P2 = merge(({s2: 1}, 1), (f2, -1))
    Pp = merge((P1, 1), (P2, 1))
    v1 = merge((val_expr(s1), 1), (w1, -1))
    v2 = merge((val_expr(s2), 1), (w2, -1))

    # q is the gcd of regular freed exponents, forced to one by any tail.
    elems = [j for j in mask_elems(m1) + mask_elems(m2) if j != TAIL]
    if (m1 | m2) & 64:
        q = 1
    else:
        q = 0
        from math import gcd
        for j in elems:
            q = gcd(q, j)
        q = q or 1
    BF = merge((w1, F(1, q)), (w2, F(1, q)), (W, -1))
    BV12 = merge((v1, 1), (v2, 1), (W, -1))
    BV1 = merge((v1, 1), (W, -1))
    BV2 = merge((v2, 1), (W, -1))
    key = f"{form}:{sig}:{m1}:{m2}:{mt}"

    specs = []
    if form == "UN":
        base = merge((Pp, 1), (C, 1))
        specs = [(base, "00"), (merge((base, 1), (BF, 1)), "10")]
    elif form == "CS1":
        base = merge((C, 1), (Pp, F(1, 2)), (f1, F(1, 2)), (f2, F(1, 2)))
        specs = [(merge((base, 1), (BF, F(e, 2)), (BV12, F(v, 2))), f"{e}{v}")
                 for e, v in itertools.product((0, 1), repeat=2)]
    elif form == "CS2A":
        base = merge((C, 1), (Pp, F(1, 2)), (P2, F(1, 2)),
                     (f1, F(1, 2)), (f2, F(1, 2)))
        specs = [(merge((base, 1), (BF, F(e, 2)), (BV1, F(v, 2))), f"{e}{v}")
                 for e, v in itertools.product((0, 1), repeat=2)]
    elif form == "CS2B":
        base = merge((C, 1), (Pp, F(1, 2)), (P1, F(1, 2)),
                     (f1, F(1, 2)), (f2, F(1, 2)))
        specs = [(merge((base, 1), (BF, F(e, 2)), (BV2, F(v, 2))), f"{e}{v}")
                 for e, v in itertools.product((0, 1), repeat=2)]
    elif form == "CS3":
        base = merge((C, 1), (Pp, 1), (f1, F(1, 2)), (f2, F(1, 2)))
        specs = [(merge((base, 1), (BF, F(e, 2))), str(e)) for e in (0, 1)]
    elif form == "RMA":
        base = merge((C, 1), (P2, 1), (f1, 1), (f2, 1))
        specs = [(merge((base, 1), (BV1, e)), str(e)) for e in (0, 1)]
    elif form == "RMB":
        base = merge((C, 1), (P1, 1), (f1, 1), (f2, 1))
        specs = [(merge((base, 1), (BV2, e)), str(e)) for e in (0, 1)]
    else:
        raise ValueError(form)
    return key, [upper_arm(g, key+":"+suffix) for g, suffix in specs]


FORMS = ("UN", "CS1", "CS2A", "CS2B", "CS3", "RMA", "RMB")


def point_dict(x):
    return {v: float(x[IDX[v]]) for v in VARS if v[0] in "abc" or v.startswith("v")}


def best_clause(x, tol, use_prop=True, prop_forms=FORMS,
                regular_free=False, spacing_first=False,
                spacing_meta=False):
    Dv = float(x[IDX["D"]])
    best = None

    def consider(key, arms):
        nonlocal best
        # Clause bound is max over its arms; all arm rows must be violated.
        gap = min(eval_row(a, x) for a in arms)
        if gap > tol and (best is None or gap > best[0]):
            best = (gap, key, [(a[2], [a]) for a in arms])

    def consider_meta(key, branches):
        nonlocal best
        # A conjunction branch is violated when at least one required row
        # is violated, hence max(row violations) for that branch.
        branch_gaps = [max(eval_row(r, x) for r in required)
                       for _, required in branches]
        gap = min(branch_gaps)
        if gap > tol and (best is None or gap > best[0]):
            best = (gap, key, branches)

    if spacing_first:
        if spacing_meta:
            for key, branches in SPACING_META:
                consider_meta(key, branches)
        else:
            for key, arms in SPACING:
                consider(key, arms)
        if best is not None:
            return best
    for key, arms in GEOMETRY:
        consider(key, arms)
    for key, arms in ARCH:
        consider(key, arms)
    for key, arms in DET:
        consider(key, arms)
    if not spacing_first:
        if spacing_meta:
            for key, branches in SPACING_META:
                consider_meta(key, branches)
        else:
            for key, arms in SPACING:
                consider(key, arms)

    pd = point_dict(x)
    # Two reflected grouped-factor rows retain five regular represented
    # blocks using one exact-1/exact-2 product polynomial plus three
    # singleton factors.  The a-grouped row separates the balanced 139/257
    # face exposed after restoring the frozen archimedean value cover.
    for group_side in "ab":
        consider(*group12c_clause(group_side))
    # Each powered difference direction a,b has a complete target-safe
    # C(10,3)=120 single-group family.  At a point the strongest member
    # retains the three largest singleton masses.
    for powered_side, pool, constructor in (
            ("a", GROUP12A_C_SINGLETON_POOL, group12a_c_clause),
            ("b", GROUP12B_C_SINGLETON_POOL, group12b_c_clause)):
        group12_singletons = tuple(sorted(
            sorted(pool, key=lambda slot: pd[slot], reverse=True)[:3],
            key=lambda slot: (0 if slot[0] == "c" else 1, slot[1])))
        consider(*constructor(group12_singletons))

    # Likewise each powered difference direction has C(8,2)=28
    # double-group clauses and four elimination arms.
    for pool, constructor in (
            (GROUP1212A_SINGLETON_POOL, group1212a_clause),
            (GROUP1212B_SINGLETON_POOL, group1212b_clause)):
        group1212_singletons = tuple(sorted(
            sorted(pool, key=lambda slot: pd[slot], reverse=True)[:2],
            key=lambda slot: (slot[0], slot[1])))
        consider(*constructor(group1212_singletons))

    # All POW3(b) descriptors are target-safe; the strongest one at a point
    # is obtained by retaining the four largest represented blocks.
    pow_b_slots = [f"{side}{index}" for side in "ac" for index in RNG]
    pow_b_held = tuple(sorted(
        sorted(pow_b_slots, key=lambda slot: pd[slot], reverse=True)[:4]))
    pow_b_C = pd["b"] - pd["b3"] - pd["b6"]
    pow_b_R = pd["a"] + pd["c"]
    pow_b_P = sum(pd[slot] for slot in pow_b_held)
    pow_b_S = pow_b_C + pow_b_R - pow_b_P / 2
    pow_b_bound = max(pow_b_S, (pow_b_S + pow_b_R) / 2)
    if Dv - pow_b_bound > tol:
        consider(*pow3_clause("b", pow_b_held))

    # The result-side c direction uses the separately proved sum-quotient
    # Fourier identity.  Every four-set on represented sides a,b is safe at
    # the target witness, so again retain the four largest current blocks.
    pow_c_slots = [f"{side}{index}" for side in "ab" for index in RNG]
    pow_c_held = tuple(sorted(
        sorted(pow_c_slots, key=lambda slot: pd[slot], reverse=True)[:4]))
    pow_c_C = pd["c"] - pd["c3"] - pd["c6"]
    pow_c_R = pd["a"] + pd["b"]
    pow_c_P = sum(pd[slot] for slot in pow_c_held)
    pow_c_S = pow_c_C + pow_c_R - pow_c_P / 2
    pow_c_bound = max(pow_c_S, (pow_c_S + pow_c_R) / 2)
    if Dv - pow_c_bound > tol:
        consider(*pow3_clause("c", pow_c_held))

    # On the a-powered side maximize P_J only over the exact target-safe
    # whitelist.  This kills the a<->b reflection of the 6/11 survivor while
    # retaining the original equality witness.
    pow_a_held = max(
        POW3A_ALLOWED, key=lambda held: sum(pd[slot] for slot in held))
    pow_a_C = pd["a"] - pd["a3"] - pd["a6"]
    pow_a_R = pd["b"] + pd["c"]
    pow_a_P = sum(pd[slot] for slot in pow_a_held)
    pow_a_S = pow_a_C + pow_a_R - pow_a_P / 2
    pow_a_bound = max(pow_a_S, (pow_a_S + pow_a_R) / 2)
    if Dv - pow_a_bound > tol:
        consider(*pow3_clause("a", pow_a_held))

    for sig in "abc":
        y, z = SIDES[sig]
        pair = pd[y] + pd[z]
        tau = pd[sig] - sum(pd[f"{sig}{i}"] for i in RNG)
        slots = [f"{s}{i}" for s in (y, z) for i in RNG]
        held = tuple(sorted(sorted(slots, key=lambda u: pd[u], reverse=True)[:4]))
        h = sum(pd[u] for u in held)
        for mt in range(1, NM):
            elems = mask_elems(mt)
            C = sum(pd[f"{sig}{j}"] for j in elems if j != TAIL)
            W = sum(j * pd[f"{sig}{j}"] for j in elems if j != TAIL)
            if TAIL in elems:
                C += tau
                W += pd[f"v{sig}"]
            gps = C + pair - min(pair / 2, 2 * W / 3)
            if Dv - gps > tol:
                consider(*ps_clause(sig, mt))
            gcs = C + pair - min(W, h / 2)
            if Dv - gcs > tol:
                consider(*cs4_clause(sig, mt, held))

    if use_prop and regular_free and prop_forms == ("UN",):
        # Fast exact-semantics separator for the original Proposition 5.1
        # universe R_y,R_z subset [6].  This avoids constructing the six
        # unused CS/RM tensors and the counted-side free-tail half-cubes.
        tabs = {s: side_tables(pd, s, numeric=float) for s in "abc"}
        for sig in "abc":
            s1, s2 = SIDES[sig]
            f1, w1, P1f, _ = tabs[s1]
            f2, w2, P2f, _ = tabs[s2]
            ct, wt, _, _ = tabs[sig]
            Ffree = ((w1[:64, None] + w2[None, :64])
                     / QMAT[:64, :64])
            arr = (P1f[:64, None, None] + P2f[None, :64, None]
                   + ct[1:][None, None, :]
                   + np.maximum(0.0, Ffree[:, :, None]
                                - wt[1:][None, None, :]))
            arr[0, 0, :] = np.inf
            ix = int(np.argmin(arr))
            g = float(arr.ravel()[ix])
            if Dv - g <= tol:
                continue
            m1, rem = divmod(ix, 64 * (NM - 1))
            m2, mt0 = divmod(rem, NM - 1)
            consider(*prop_clause("UN", sig, m1, m2, mt0 + 1))
    elif use_prop:
        for sig, forms in scan_forms_np(pd, use_hyp=False, use_hmax=False,
                                        use_mome=False):
            for form in prop_forms:
                arr = forms[form]
                view = arr[:64, :64, :] if regular_free else arr
                ix = int(np.argmin(view))
                g = float(view.ravel()[ix])
                if Dv - g <= tol:
                    continue
                nmask = 64 if regular_free else NM
                m1, rem = divmod(ix, nmask * (NM - 1))
                m2, mt0 = divmod(rem, NM - 1)
                consider(*prop_clause(form, sig, m1, m2, mt0 + 1))
    return best


def exact_solve_columns(cols, target):
    """Solve sum_j mu_j cols[j] = target exactly, free variables set to 0."""
    neq = len(target)
    m = len(cols)
    mat = [[F(cols[j][i]) for j in range(m)] + [F(target[i])]
           for i in range(neq)]
    pivots = []
    rr = 0
    for cc in range(m):
        pr = next((r for r in range(rr, neq) if mat[r][cc]), None)
        if pr is None:
            continue
        mat[rr], mat[pr] = mat[pr], mat[rr]
        pv = mat[rr][cc]
        mat[rr] = [v / pv for v in mat[rr]]
        for r in range(neq):
            if r != rr and mat[r][cc]:
                fac = mat[r][cc]
                mat[r] = [a - fac * b for a, b in zip(mat[r], mat[rr])]
        pivots.append(cc)
        rr += 1
        if rr == neq:
            break
    if any(all(mat[r][c] == 0 for c in range(m)) and mat[r][m] != 0
           for r in range(rr, neq)):
        return None
    mu = [F(0)] * m
    for r, cc in enumerate(pivots):
        mu[cc] = mat[r][m]
    return mu


def constraint_columns(rows):
    cons = list(rows)
    for v in VARS:
        cons.append(row({v: -1}, 0, "nonneg:"+v))
    cols = []
    for d, _, _ in cons:
        cols.append([d.get(v, F(0)) for v in VARS])
    rhs = [r[1] for r in cons]
    return cons, cols, rhs


def exact_upper_cert(rows):
    cons, cols, rhs = constraint_columns(rows)
    m = len(cons)
    Aeq = np.array([[float(cols[j][i]) for j in range(m)] for i in range(NVAR)])
    beq = np.zeros(NVAR)
    beq[IDX["D"]] = 1.0
    obj = np.array([float(v) for v in rhs])
    res = linprog(obj, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m,
                  method="highs")
    if not res.success or res.fun > float(TARGET) + 1e-8:
        return None
    for eps in (1e-7, 1e-9, 1e-11):
        support = [j for j, v in enumerate(res.x) if v > eps]
        mu = exact_solve_columns([cols[j] for j in support],
                                 [F(1) if i == IDX["D"] else F(0)
                                  for i in range(NVAR)])
        if mu is None or any(v < 0 for v in mu):
            continue
        total_rhs = sum(mu[k] * rhs[support[k]] for k in range(len(support)))
        if total_rhs <= TARGET:
            return {"rhs": str(total_rhs),
                    "terms": [(cons[support[k]][2], str(mu[k]))
                              for k in range(len(support)) if mu[k]]}
    return None


def exact_infeas_cert(rows):
    cons, cols, rhs = constraint_columns(rows)
    m = len(cons)
    Aeq = np.zeros((NVAR + 1, m))
    for i in range(NVAR):
        Aeq[i, :] = [float(cols[j][i]) for j in range(m)]
    Aeq[NVAR, :] = 1.0
    beq = np.zeros(NVAR + 1)
    beq[NVAR] = 1.0
    obj = np.array([float(v) for v in rhs])
    res = linprog(obj, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * m,
                  method="highs")
    if not res.success or res.fun >= -1e-10:
        return None
    support = [j for j, v in enumerate(res.x) if v > 1e-10]
    target = [F(0)] * NVAR + [F(1)]
    augcols = [cols[j] + [F(1)] for j in support]
    mu = exact_solve_columns(augcols, target)
    if mu is None or any(v < 0 for v in mu):
        return None
    total_rhs = sum(mu[k] * rhs[support[k]] for k in range(len(support)))
    if total_rhs >= 0:
        return None
    return {"rhs": str(total_rhs),
            "terms": [(cons[support[k]][2], str(mu[k]))
                      for k in range(len(support)) if mu[k]]}


def solve(rows):
    A, b = to_np(rows)
    c = np.zeros(NVAR)
    c[IDX["D"]] = -1
    return linprog(c, A_ub=A, b_ub=b, bounds=[(0, None)] * NVAR,
                   method="highs")


def row_to_json(r):
    d, rhs, label = r
    return {"coeff": {k: str(v) for k, v in d.items()},
            "rhs": str(rhs), "label": label}


def row_from_json(obj):
    return row({k: F(v) for k, v in obj["coeff"].items()},
               F(obj["rhs"]), obj["label"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-nodes", type=int, default=200)
    ap.add_argument("--tol", type=float, default=2e-8)
    ap.add_argument("--no-prop", action="store_true")
    ap.add_argument("--prop-forms", default=",".join(FORMS),
                    help="comma-separated unconditional proposition forms")
    ap.add_argument("--regular-free", action="store_true",
                    help="restrict counted-side free masks to subsets of [6]")
    ap.add_argument("--spacing-first", action="store_true")
    ap.add_argument("--spacing-meta", action="store_true")
    ap.add_argument("--report", default="dynamic_tree_report.json")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--preload-report")
    args = ap.parse_args()
    prop_forms = tuple(x for x in args.prop_forms.split(",") if x)
    assert all(x in FORMS for x in prop_forms), prop_forms

    if args.resume:
        old = json.load(open(args.report))
        assert not old["complete"] and not old["survivors"]
        stack = [([row_from_json(r) for r in item["fixed"]], item["path"])
                 for item in old["open_stack"]]
        stats = old["stats"]
        certs = old["certificates"]
        survivors = old["survivors"]
        print(f"resumed nodes={stats['nodes']} open={len(stack)}", flush=True)
    else:
        stack = [([], [])]  # fixed arm rows, branch-occurrence labels
        stats = {"nodes": 0, "upper_exact": 0, "infeas_exact": 0,
                 "bad_cert": 0, "survivors": 0, "open": 0, "max_depth": 0}
        certs = []
        survivors = []
    preload = []
    if args.preload_report:
        prior = json.load(open(args.preload_report))
        always = {r[2] for r in BASE}
        for cert in prior["certificates"]:
            deps = frozenset(label for label, _ in cert["terms"]
                             if label not in always
                             and not label.startswith("nonneg:"))
            preload.append((deps, cert))
        preload.sort(key=lambda item: len(item[0]))
        print(f"preloaded {len(preload)} exact partial-cube certificates",
              flush=True)
    t0 = time.time()
    while stack and stats["nodes"] < args.max_nodes:
        fixed, path = stack.pop()
        stats["nodes"] += 1
        stats["max_depth"] = max(stats["max_depth"], len(path))
        path_set = set(path)
        reused = next((cert for deps, cert in preload if deps <= path_set), None)
        if reused is not None:
            lifted = dict(reused)
            lifted["path"] = path
            certs.append(lifted)
            if reused["kind"] == "upper":
                stats["upper_exact"] += 1
            else:
                stats["infeas_exact"] += 1
            continue
        rows = BASE + fixed
        res = solve(rows)
        if not res.success:
            cert = exact_infeas_cert(rows)
            if cert is None:
                stats["bad_cert"] += 1
                survivors.append({"kind": "FLOAT_INFEAS_NO_EXACT_CERT", "path": path})
                break
            stats["infeas_exact"] += 1
            certs.append({"kind": "infeas", "path": path, **cert})
            continue
        Dv = -float(res.fun)
        if Dv <= float(TARGET) + args.tol:
            cert = exact_upper_cert(rows)
            if cert is None:
                stats["bad_cert"] += 1
                survivors.append({"kind": "UPPER_NO_EXACT_CERT", "D": Dv, "path": path})
                break
            stats["upper_exact"] += 1
            certs.append({"kind": "upper", "path": path, **cert})
            continue
        clause = best_clause(res.x, args.tol, use_prop=not args.no_prop,
                             prop_forms=prop_forms,
                             regular_free=args.regular_free,
                             spacing_first=args.spacing_first,
                             spacing_meta=args.spacing_meta)
        if clause is None:
            stats["survivors"] += 1
            survivors.append({
                "kind": "NO_VIOLATED_CLAUSE", "D": Dv, "path": path,
                "point_fraction_hints": {
                    v: str(F(float(res.x[IDX[v]])).limit_denominator(1000000))
                    for v in VARS},
            })
            break
        gap, key, branches = clause
        # DFS: append weaker-looking arms first so the strongest current arm
        # is explored next.  Correctness is independent of this ordering.
        branch_order = sorted(
            branches,
            key=lambda item: max(eval_row(r, res.x) for r in item[1]))
        for occurrence, required_rows in branch_order:
            stack.append((fixed + required_rows, path + [occurrence]))
        if stats["nodes"] % 10 == 0:
            print(f"nodes={stats['nodes']} open={len(stack)} depth={len(path)} "
                  f"D={Dv:.9f} branch={key} gap={gap:.3g}", flush=True)

    stats["open"] = len(stack)
    system = ("base+ARCH-value-cover+HB3+13geom+DET+Spacing+allPS23"
              "+CS4regular+POW3abc-regular(a-target-safe)"
              "+GROUP12c(a/b)+GROUP12ab(c;all3)+GROUP1212ab(all2) grouped rows")
    if not args.no_prop:
        system += "+extended-" + "/".join(prop_forms)
        if args.regular_free:
            system += "(regular-free)"
    report = {
        "target": str(TARGET),
        "system": system,
        "search_flags": {
            "no_prop": args.no_prop,
            "spacing_first": args.spacing_first,
            "spacing_meta": args.spacing_meta,
            "prop_forms": prop_forms,
            "regular_free": args.regular_free,
            "pow3b_regular": True,
            "pow3a_target_safe": True,
            "pow3c_regular": True,
            "arch_value_cover": True,
            "group12c_ab12": True,
            "group12a_c12_all3": True,
            "group12b_c12_all3": True,
            "group1212a_all2": True,
            "group1212b_all2": True,
        },
        "complete": not stack and not survivors and not stats["bad_cert"],
        "elapsed_s": time.time() - t0,
        "stats": stats,
        "certificates": certs,
        "survivors": survivors,
        "open_stack": [
            {"fixed": [row_to_json(r) for r in fixed], "path": path}
            for fixed, path in stack],
    }
    with open(args.report, "w") as fh:
        json.dump(report, fh, indent=2, sort_keys=True)
    print(json.dumps({k: report[k] for k in ("target", "system", "complete", "elapsed_s", "stats")},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
