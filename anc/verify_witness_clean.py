#!/usr/bin/env python3
"""Standalone exact witness verifier for the 20/37 profile.

Only the Python standard library and fractions.Fraction are used.  This
file does not import the proof-tree generator, scan_lib, NumPy, SciPy, or
the independent tree verifier.  It reconstructs the proposed 28-variable
profile and checks the complete lower-bound system relevant to the final
tree:

  base + homogeneous ARCH value cover + HB3 + 13 geometry clauses
  + DET + 30 Spacing clauses
  + all PS23 + every regular-held CS4 clause
  + every four-regular-block unlocalized POW3(b) clause
  + every four-regular-block sum-quotient POW3(c) clause
  + the exact target-safe four-block unlocalized POW3(a) subfamily
  + both fixed GROUP12(c) clauses, all 240 target-safe GROUP12(a/b,c;all3)
    clauses, and all 56 target-safe GROUP1212(a/b;all2) clauses
  + every docs/885 Proposition 5.1 UN tuple with regular free masks.

For UN, R_1,R_2 are subsets of [6], not both empty, while the nonempty
modulus mask T is allowed to include the multiplicity-at-least-seven tail.
The exhaustive UN count is therefore 3*(64^2-1)*127 = 1,560,195.
"""

import argparse
import itertools
import math
from fractions import Fraction


Q = Fraction
TARGET = Q(20, 37)
RNG = tuple(range(1, 7))
SIDES = {"a": ("b", "c"), "b": ("a", "c"), "c": ("a", "b")}
VARS = tuple(
    ["D", "a", "b", "c"]
    + [f"{side}{i}" for side in "abc" for i in RNG]
    + [f"v{side}" for side in "abc"]
    + [f"m{side}" for side in "abc"]
)
VAR_SET = frozenset(VARS)
POW3A_TARGET_MASS_NUM = {"b1": 2, "c1": 5, "c4": 8}
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


class WitnessError(Exception):
    pass


def fail(message):
    raise WitnessError(message)


def require(condition, message):
    if not condition:
        fail(message)


def build_witness():
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(20, 37),
        "a": Q(17, 37), "a1": Q(7, 37), "a3": Q(10, 37),
        "b": Q(7, 37), "b1": Q(2, 37), "vb": Q(35, 37),
        "c": Q(13, 37), "c1": Q(5, 37), "c4": Q(8, 37),
        # Exact epigraph witnesses for the three Fourier maxima.
        "ma": Q(10, 37), "mb": Q(0), "mc": Q(8, 37),
    })
    return profile


def build_survivor_6_11():
    """Exact obstruction found by the regular-free-UN proof-tree search."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(6, 11),
        "a": Q(3, 11), "a3": Q(1, 11), "a4": Q(2, 11),
        "b": Q(5, 11), "b1": Q(2, 11), "b3": Q(3, 11),
        "c": Q(3, 11), "c1": Q(1, 11), "c5": Q(2, 11),
        "ma": Q(3, 11), "mb": Q(3, 11), "mc": Q(2, 11),
    })
    return profile


def build_reflected_survivor_6_11():
    """The a<->b reflection, which requires the safe POW3(a) direction."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(6, 11),
        "a": Q(5, 11), "a1": Q(2, 11), "a3": Q(3, 11),
        "b": Q(3, 11), "b3": Q(1, 11), "b4": Q(2, 11),
        "c": Q(3, 11), "c1": Q(1, 11), "c5": Q(2, 11),
        "ma": Q(3, 11), "mb": Q(3, 11), "mc": Q(2, 11),
    })
    return profile


def build_result_side_survivor_6_11():
    """The c-heavy obstruction, which requires the sum-quotient POW3(c)."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(6, 11),
        "a": Q(3, 11), "a1": Q(1, 11), "a5": Q(2, 11),
        "b": Q(3, 11), "b3": Q(1, 11), "b4": Q(2, 11),
        "c": Q(5, 11), "c1": Q(2, 11), "c3": Q(3, 11),
        "ma": Q(3, 11), "mb": Q(2, 11), "mc": Q(3, 11),
    })
    return profile


def build_balanced_139_257():
    """Balanced ARCH-compatible face strictly cut by GROUP12(c,a)."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(139, 257),
        "a": Q(439, 1285), "a1": Q(137, 1285),
        "a2": Q(30, 1285), "a4": Q(272, 1285),
        "b": Q(451, 1285), "b1": Q(173, 1285),
        "b4": Q(278, 1285),
        "c": Q(395, 1285), "c1": Q(10, 1285),
        "c3": Q(355, 1285), "vc": Q(210, 1285),
        "ma": Q(302, 1285), "mb": Q(278, 1285),
        "mc": Q(355, 1285),
    })
    return profile


def build_group12a_c_survivor_6_11():
    """Exact ARCH-compatible face cut by grouped c1*c2^2 for powered a."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(6, 11),
        "a": Q(449, 1375), "a1": Q(23, 2750),
        "a3": Q(412, 1375), "a5": Q(51, 2750),
        "b": Q(41, 125), "b1": Q(148, 1375),
        "b4": Q(288, 1375), "b5": Q(3, 275),
        "c": Q(19, 55), "c1": Q(7, 55), "c4": Q(12, 55),
        "ma": Q(412, 1375), "mb": Q(288, 1375),
        "mc": Q(12, 55),
    })
    return profile


def build_group12a_c_second_face_110_203():
    """Second exact ARCH-compatible face, cut by the b5 singleton variant."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(110, 203),
        "a": Q(229, 609), "a1": Q(2, 87), "a2": Q(50, 609),
        "a3": Q(55, 203),
        "b": Q(167, 609), "b1": Q(52, 609), "b2": Q(2, 203),
        "b5": Q(109, 609),
        "c": Q(71, 203), "c1": Q(27, 203), "c4": Q(44, 203),
        "ma": Q(215, 609), "mb": Q(109, 609), "mc": Q(44, 203),
    })
    return profile


def build_group1212a_third_face_46_85():
    """Third ARCH-compatible face, cut by grouping b1*b2^2 and c1*c2^2."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(46, 85),
        "a": Q(27, 85), "a1": Q(3, 85), "a3": Q(24, 85),
        "b": Q(141, 425), "b1": Q(33, 425), "b2": Q(4, 85),
        "b4": Q(88, 425),
        "c": Q(149, 425), "c1": Q(57, 425), "c4": Q(92, 425),
        "ma": Q(24, 85), "mb": Q(108, 425), "mc": Q(92, 425),
    })
    return profile


def build_group1212b_reflected_face_46_85():
    """The exact a<->b reflection, cut by the powered-b double group."""
    profile = {variable: Q(0) for variable in VARS}
    profile.update({
        "D": Q(46, 85),
        "a": Q(141, 425), "a1": Q(33, 425), "a2": Q(4, 85),
        "a4": Q(88, 425),
        "b": Q(27, 85), "b1": Q(3, 85), "b3": Q(24, 85),
        "c": Q(149, 425), "c1": Q(57, 425), "c4": Q(92, 425),
        "ma": Q(108, 425), "mb": Q(24, 85), "mc": Q(92, 425),
    })
    return profile


def validate_profile(profile):
    require(type(profile) is dict, "profile must be a dictionary")
    require(set(profile) == VAR_SET,
            f"profile variable set mismatch: {set(profile) ^ VAR_SET}")
    for variable in VARS:
        require(type(profile[variable]) is Q,
                f"profile[{variable}] is not a Fraction")


def side_scalars(profile, side):
    require(side in SIDES, f"unknown side: {side!r}")
    root_sum = sum(profile[f"{side}{i}"] for i in RNG)
    tail_root = profile[side] - root_sum
    value = sum(i * profile[f"{side}{i}"] for i in RNG) + profile[f"v{side}"]
    return root_sum, tail_root, value


def check_arch_cover(profile):
    values = {side: side_scalars(profile, side)[2] for side in "abc"}
    require(values["a"] <= values["c"], "ARCH:a<=c failed")
    require(values["b"] <= values["c"], "ARCH:b<=c failed")
    require(values["c"] <= values["a"] or values["c"] <= values["b"],
            "ARCH:max two-arm cover failed")
    return values


def mask_elements(mask, allow_tail, require_nonempty=False):
    require(type(mask) is int and not isinstance(mask, bool), "mask is not an integer")
    upper = 128 if allow_tail else 64
    require(0 <= mask < upper,
            f"mask {mask} is outside the allowed range [0,{upper - 1}]")
    require(not require_nonempty or mask != 0, "selected mask must be nonempty")
    regular = tuple(i for i in RNG if mask & (1 << (i - 1)))
    has_tail = bool(mask & 64) if allow_tail else False
    return regular, has_tail


def selected_root_value(profile, side, mask, *, allow_tail,
                        require_nonempty=False):
    regular, has_tail = mask_elements(mask, allow_tail, require_nonempty)
    cost = sum(profile[f"{side}{i}"] for i in regular)
    weight = sum(i * profile[f"{side}{i}"] for i in regular)
    if has_tail:
        _root_sum, tail_root, _value = side_scalars(profile, side)
        cost += tail_root
        weight += profile[f"v{side}"]
    return cost, weight


def free_gcd(free1, free2):
    elems1, tail1 = mask_elements(free1, allow_tail=False)
    elems2, tail2 = mask_elements(free2, allow_tail=False)
    require(not tail1 and not tail2, "internal regular-free mask error")
    q = 0
    for exponent in elems1 + elems2:
        q = math.gcd(q, exponent)
    require(q >= 1, "Proposition 5.1 free masks are both empty")
    return q


def check_base_and_hb3(profile):
    validate_profile(profile)
    for variable, value in profile.items():
        require(value >= 0, f"nonnegativity failed at {variable}: {value}")
    D = profile["D"]
    total_radical = sum(profile[side] for side in "abc")
    require(total_radical <= 1, f"L row failed: {total_radical} > 1")
    for side in "abc":
        root_sum, tail_root, value = side_scalars(profile, side)
        require(root_sum <= profile[side], f"root row failed on {side}")
        require(profile[f"v{side}"] >= 7 * tail_root,
                f"tail7 row failed on {side}")
        require(value <= 1, f"value row failed on {side}")
        rad_left = 7 * profile[side] - sum(
            (7 - i) * profile[f"{side}{i}"] for i in RNG)
        require(rad_left <= 1, f"rad row failed on {side}")
        fourier_arms = (
            profile[f"{side}2"] + profile[f"{side}4"] + profile[f"{side}6"],
            profile[f"{side}3"] + profile[f"{side}6"],
            profile[f"{side}5"],
        )
        for arm_index, arm in enumerate(fourier_arms):
            require(arm <= profile[f"m{side}"],
                    f"Fourier epigraph row {side}/{arm_index} failed")
    for y, z in (("a", "b"), ("a", "c"), ("b", "c")):
        require(D <= profile[y] + profile[z], f"pair row {y}{z} failed")
    require(profile["ma"] + profile["mb"] + profile["mc"]
            <= 4 * total_radical - 6 * D,
            "Fourier-sum row failed")
    values = check_arch_cover(profile)
    hb3_bound = total_radical - sum(profile[f"{side}3"] for side in "abc")
    require(D <= hb3_bound, f"HB3 failed: D={D}, bound={hb3_bound}")
    return {
        "L": total_radical,
        "HB3": hb3_bound,
        "values": values,
    }


def geometry_bounds(profile):
    pf = {i: sum(profile[f"{side}{i}"] for side in "abc") for i in RNG}
    pairs = [("G0", pf[1] + pf[2] + pf[4], 1 - pf[2] - 3 * pf[4])]
    for side in "abc":
        pairs.append((
            f"G1-{side}",
            pf[1] + pf[2] + profile[f"{side}3"],
            1 - pf[2] - 2 * profile[f"{side}3"],
        ))
    for side, other in (("a", "b"), ("b", "c"), ("c", "a")):
        pairs.append((
            f"G2-{side}{other}",
            pf[1] + pf[2] + profile[f"{side}3"] + profile[f"{other}3"],
            1 - pf[2] - 2 * profile[f"{side}3"] - 2 * profile[f"{other}3"],
        ))
    for side in "abc":
        y, z = tuple(other for other in "abc" if other != side)
        pairs.append((
            f"G3-{side}",
            pf[1] + profile[f"{side}3"] + profile[f"{y}2"]
            + profile[f"{z}2"],
            1 - 2 * profile[f"{side}3"] - profile[f"{y}2"]
            - profile[f"{z}2"],
        ))
    for side in "abc":
        y, z = tuple(other for other in "abc" if other != side)
        pairs.append((
            f"G4-{side}",
            pf[1] + profile[f"{side}2"] + profile[f"{y}3"]
            + profile[f"{z}3"],
            1 - profile[f"{side}2"] - 2 * profile[f"{y}3"]
            - 2 * profile[f"{z}3"],
        ))
    require(len(pairs) == 13, f"geometry constructor returned {len(pairs)} clauses")
    total_radical = sum(profile[side] for side in "abc")
    return [(name, total_radical - min(first, second))
            for name, first, second in pairs]


def check_geometry(profile):
    bounds = geometry_bounds(profile)
    for name, bound in bounds:
        require(profile["D"] <= bound,
                f"geometry clause {name} failed: D={profile['D']}, bound={bound}")
    return min(bounds, key=lambda item: item[1]), len(bounds)


def check_det(profile):
    bounds = {}
    for k in (2, 4, 5, 6):
        bound = (sum(profile[side] - profile[f"{side}{k}"] for side in "abc")
                 + Q(2, k) * max(profile[f"{side}{k}"] for side in "abc"))
        require(profile["D"] <= bound,
                f"DET{k} failed: D={profile['D']}, bound={bound}")
        bounds[k] = bound
    return bounds


def spacing_bound(profile, equation_side, y, z, k):
    require(equation_side in SIDES, "Spacing has an invalid equation side")
    require((y, z) in (SIDES[equation_side], SIDES[equation_side][::-1]),
            "Spacing has invalid counted-side ordering")
    require(k in range(2, 7), "Spacing exponent is outside [2,6]")
    value_e = side_scalars(profile, equation_side)[2]
    value_z = side_scalars(profile, z)[2]
    return (profile[y] + profile[z] - profile[f"{z}{k}"]
            + max(Q(0), value_e - value_z + profile[f"{z}{k}"]))


def check_spacing(profile):
    minimum = None
    count = 0
    for equation_side in "abc":
        other1, other2 = SIDES[equation_side]
        for y, z in ((other1, other2), (other2, other1)):
            for k in range(2, 7):
                bound = spacing_bound(profile, equation_side, y, z, k)
                require(profile["D"] <= bound,
                        f"Spacing({equation_side};{y},{z};{k}) failed")
                item = (bound, equation_side, y, z, k)
                minimum = item if minimum is None or item < minimum else minimum
                count += 1
    require(count == 30, f"Spacing constructor returned {count} rows")
    return minimum, count


def ps23_bound(profile, side, selected_mask):
    require(side in SIDES, "PS23 has an invalid modulus side")
    cost, weight = selected_root_value(
        profile, side, selected_mask, allow_tail=True, require_nonempty=True)
    y, z = SIDES[side]
    pair = profile[y] + profile[z]
    return max(cost + pair / 2, cost + pair - Q(2, 3) * weight)


def check_all_ps23(profile):
    minimum = None
    count = 0
    for side in "abc":
        for selected_mask in range(1, 128):
            bound = ps23_bound(profile, side, selected_mask)
            require(profile["D"] <= bound,
                    f"PS23({side},{selected_mask}) failed")
            item = (bound, side, selected_mask)
            minimum = item if minimum is None or item < minimum else minimum
            count += 1
    require(count == 3 * 127, f"PS23 count mismatch: {count}")
    return minimum, count


def cs4_bound(profile, side, selected_mask, held):
    require(side in SIDES, "CS4 has an invalid modulus side")
    require(type(held) is tuple and len(held) == 4 and len(set(held)) == 4,
            "CS4 held tuple must contain four distinct regular slots")
    allowed = frozenset(f"{other}{i}" for other in SIDES[side] for i in RNG)
    require(all(slot in allowed for slot in held),
            "CS4 held tuple contains a forbidden slot")
    cost, weight = selected_root_value(
        profile, side, selected_mask, allow_tail=True, require_nonempty=True)
    y, z = SIDES[side]
    pair = profile[y] + profile[z]
    held_mass = sum(profile[slot] for slot in held)
    return max(cost + pair - weight, cost + pair - held_mass / 2)


def check_all_regular_cs4(profile):
    minimum = None
    count = 0
    for side in "abc":
        slots = tuple(f"{other}{i}" for other in SIDES[side] for i in RNG)
        held_sets = tuple(itertools.combinations(slots, 4))
        require(len(held_sets) == 495, "CS4 held-set count is not C(12,4)")
        for selected_mask in range(1, 128):
            for held in held_sets:
                bound = cs4_bound(profile, side, selected_mask, held)
                require(profile["D"] <= bound,
                        f"CS4({side},{selected_mask},{held}) failed")
                item = (bound, side, selected_mask, held)
                minimum = item if minimum is None or item < minimum else minimum
                count += 1
    expected = 3 * 127 * 495
    require(count == expected, f"regular CS4 count {count} != {expected}")
    return minimum, count


def pow3_bound(profile, side, held):
    """Evaluate one allowed global unlocalized directional cubic-sieve row."""
    require(side in ("a", "b", "c"), "POW3 has a forbidden powered side")
    prefix = f"POW3{side}"
    require(type(held) is tuple and len(held) == 4 and len(set(held)) == 4,
            f"{prefix} retained tuple must contain four distinct regular slots")
    require(tuple(sorted(held)) == held,
            f"{prefix} retained tuple is not canonical-sorted")
    represented = tuple(other for other in "abc" if other != side)
    allowed = frozenset(
        f"{other}{index}" for other in represented for index in RNG)
    require(all(slot in allowed for slot in held),
            f"{prefix} retained tuple contains a forbidden slot")
    if side == "a":
        target_mass_num = sum(
            POW3A_TARGET_MASS_NUM.get(slot, 0) for slot in held)
        require(target_mass_num <= 14,
                "POW3a retained tuple is outside target-safe whitelist")
    coefficient_cost = profile[side] - profile[f"{side}3"] - profile[f"{side}6"]
    represented_radical = sum(profile[other] for other in represented)
    retained_mass = sum(profile[slot] for slot in held)
    S = coefficient_cost + represented_radical - retained_mass / 2
    return max(S, (S + represented_radical) / 2)


def check_all_directional_pow3(profile):
    summaries = {}
    slots = tuple(f"{side}{index}" for side in "ac" for index in RNG)
    minimum = None
    count = 0
    for held in itertools.combinations(slots, 4):
        bound = pow3_bound(profile, "b", held)
        require(profile["D"] <= bound,
                f"POW3b({held}) failed: D={profile['D']}, bound={bound}")
        item = (bound, held)
        minimum = item if minimum is None or item < minimum else minimum
        count += 1
    require(count == 495, f"regular POW3b count {count} != 495")
    summaries["b"] = (minimum, count)

    slots = tuple(f"{side}{index}" for side in "bc" for index in RNG)
    minimum = None
    count = 0
    for held in itertools.combinations(slots, 4):
        if sum(POW3A_TARGET_MASS_NUM.get(slot, 0) for slot in held) > 14:
            continue
        bound = pow3_bound(profile, "a", held)
        require(profile["D"] <= bound,
                f"POW3a({held}) failed: D={profile['D']}, bound={bound}")
        item = (bound, held)
        minimum = item if minimum is None or item < minimum else minimum
        count += 1
    require(count == 486, f"target-safe regular POW3a count {count} != 486")
    summaries["a"] = (minimum, count)

    slots = tuple(f"{side}{index}" for side in "ab" for index in RNG)
    minimum = None
    count = 0
    for held in itertools.combinations(slots, 4):
        bound = pow3_bound(profile, "c", held)
        require(profile["D"] <= bound,
                f"POW3c({held}) failed: D={profile['D']}, bound={bound}")
        item = (bound, held)
        minimum = item if minimum is None or item < minimum else minimum
        count += 1
    require(count == 495, f"regular POW3c count {count} != 495")
    summaries["c"] = (minimum, count)
    return summaries


def check_directional_pow3_canaries():
    original = build_survivor_6_11()
    reflected = build_reflected_survivor_6_11()
    result_side = build_result_side_survivor_6_11()
    b_descriptor = ("a3", "a4", "c1", "c5")
    a_descriptor = ("b3", "b4", "c1", "c5")
    c_descriptor = ("a1", "a5", "b3", "b4")
    b_bound = pow3_bound(original, "b", b_descriptor)
    a_bound = pow3_bound(reflected, "a", a_descriptor)
    c_bound = pow3_bound(result_side, "c", c_descriptor)
    require(b_bound == Q(1, 2), f"unexpected POW3b canary bound: {b_bound}")
    require(a_bound == Q(1, 2), f"unexpected POW3a canary bound: {a_bound}")
    require(c_bound == Q(1, 2), f"unexpected POW3c canary bound: {c_bound}")
    require(original["D"] - b_bound == Q(1, 22),
            "POW3b canary saving is not 1/22")
    require(reflected["D"] - a_bound == Q(1, 22),
            "POW3a canary saving is not 1/22")
    require(result_side["D"] - c_bound == Q(1, 22),
            "POW3c canary saving is not 1/22")
    return {"POW3b": b_bound, "POW3a": a_bound, "POW3c": c_bound,
            "saving": Q(1, 22)}


def group12_data(profile, powered_side, group_side, other_index=4):
    """Evaluate one of the two fixed powered-c grouped-factor rows."""
    authorized = {("c", "a", 4), ("c", "b", 4)}
    require((powered_side, group_side, other_index) in authorized,
            "GROUP12 powered/grouped pair is not authorized")
    represented = tuple(side for side in "abc" if side != powered_side)
    other = next(side for side in represented if side != group_side)
    coefficient_cost = (profile[powered_side]
                        - profile[f"{powered_side}3"]
                        - profile[f"{powered_side}6"])
    coefficient_weight = (
        profile[f"v{powered_side}"] + profile[f"{powered_side}1"]
        + 2 * profile[f"{powered_side}2"] + profile[f"{powered_side}4"]
        + 2 * profile[f"{powered_side}5"])
    represented_radical = sum(profile[side] for side in represented)
    grouped_linear = profile[f"{group_side}1"]
    grouped_quadratic = profile[f"{group_side}2"]
    retained = (
        f"{group_side}1", f"{group_side}2", f"{group_side}4",
        f"{other}1", f"{other}{other_index}")
    retained_mass = sum(profile[slot] for slot in retained)
    grouped_length = grouped_linear + 2 * grouped_quadratic
    S = coefficient_cost + represented_radical - retained_mass / 2
    arms = (S, (S + represented_radical) / 2,
            S + grouped_length - coefficient_weight / 2)
    return {
        "powered_side": powered_side,
        "other_index": other_index,
        "side": group_side,
        "retained": retained,
        "C": coefficient_cost,
        "W": coefficient_weight,
        "R": represented_radical,
        "P": retained_mass,
        "L": grouped_length,
        "S": S,
        "arms": arms,
        "bound": max(arms),
    }


def group12c_data(profile, group_side):
    """Compatibility wrapper for the two established powered-c rows."""
    return group12_data(profile, "c", group_side)


def canonical_group12a_c_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 3,
            "GROUP12a(c) requires three singleton slots")
    require(len(set(singletons)) == 3
            and set(singletons) <= set(GROUP12A_C_SINGLETON_POOL),
            "GROUP12a(c) singleton set is invalid")
    canonical = (tuple(sorted(slot for slot in singletons if slot[0] == "c"))
                 + tuple(sorted(slot for slot in singletons if slot[0] == "b")))
    require(singletons == canonical,
            "GROUP12a(c) singleton tuple is not canonical")
    return singletons


def group12a_c_data(profile, singletons):
    singletons = canonical_group12a_c_singletons(singletons)
    C = profile["a"] - profile["a3"] - profile["a6"]
    W = (profile["va"] + profile["a1"] + 2 * profile["a2"]
         + profile["a4"] + 2 * profile["a5"])
    R = profile["b"] + profile["c"]
    retained = ("c1", "c2") + singletons
    P = sum(profile[slot] for slot in retained)
    L = profile["c1"] + 2 * profile["c2"]
    S = C + R - P / 2
    arms = (S, (S + R) / 2, S + L - W / 2)
    return {"singletons": singletons, "retained": retained,
            "C": C, "W": W, "R": R, "P": P, "L": L, "S": S,
            "arms": arms, "bound": max(arms)}


def canonical_group12b_c_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 3,
            "GROUP12b(c) requires three singleton slots")
    require(len(set(singletons)) == 3
            and set(singletons) <= set(GROUP12B_C_SINGLETON_POOL),
            "GROUP12b(c) singleton set is invalid")
    canonical = (tuple(sorted(slot for slot in singletons if slot[0] == "c"))
                 + tuple(sorted(slot for slot in singletons if slot[0] == "a")))
    require(singletons == canonical,
            "GROUP12b(c) singleton tuple is not canonical")
    return singletons


def group12b_c_data(profile, singletons):
    singletons = canonical_group12b_c_singletons(singletons)
    C = profile["b"] - profile["b3"] - profile["b6"]
    W = (profile["vb"] + profile["b1"] + 2 * profile["b2"]
         + profile["b4"] + 2 * profile["b5"])
    R = profile["a"] + profile["c"]
    retained = ("c1", "c2") + singletons
    P = sum(profile[slot] for slot in retained)
    L = profile["c1"] + 2 * profile["c2"]
    S = C + R - P / 2
    arms = (S, (S + R) / 2, S + L - W / 2)
    return {"singletons": singletons, "retained": retained,
            "C": C, "W": W, "R": R, "P": P, "L": L, "S": S,
            "arms": arms, "bound": max(arms)}


def canonical_group1212a_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 2,
            "GROUP1212a requires two singleton slots")
    require(len(set(singletons)) == 2
            and set(singletons) <= set(GROUP1212A_SINGLETON_POOL),
            "GROUP1212a singleton set is invalid")
    canonical = tuple(sorted(singletons, key=lambda slot: (slot[0], slot[1])))
    require(singletons == canonical,
            "GROUP1212a singleton tuple is not canonical")
    return singletons


def group1212a_data(profile, singletons):
    singletons = canonical_group1212a_singletons(singletons)
    C = profile["a"] - profile["a3"] - profile["a6"]
    W = (profile["va"] + profile["a1"] + 2 * profile["a2"]
         + profile["a4"] + 2 * profile["a5"])
    R = profile["b"] + profile["c"]
    retained = ("b1", "b2", "c1", "c2") + singletons
    P = sum(profile[slot] for slot in retained)
    Lb = profile["b1"] + 2 * profile["b2"]
    Lc = profile["c1"] + 2 * profile["c2"]
    S = C + R - P / 2
    arms = (S, (S + R) / 2, S + Lb - W / 2, S + Lc - W / 2)
    return {"singletons": singletons, "retained": retained,
            "C": C, "W": W, "R": R, "P": P, "Lb": Lb, "Lc": Lc,
            "S": S, "arms": arms, "bound": max(arms)}


def canonical_group1212b_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 2,
            "GROUP1212b requires two singleton slots")
    require(len(set(singletons)) == 2
            and set(singletons) <= set(GROUP1212B_SINGLETON_POOL),
            "GROUP1212b singleton set is invalid")
    canonical = tuple(sorted(singletons, key=lambda slot: (slot[0], slot[1])))
    require(singletons == canonical,
            "GROUP1212b singleton tuple is not canonical")
    return singletons


def group1212b_data(profile, singletons):
    singletons = canonical_group1212b_singletons(singletons)
    C = profile["b"] - profile["b3"] - profile["b6"]
    W = (profile["vb"] + profile["b1"] + 2 * profile["b2"]
         + profile["b4"] + 2 * profile["b5"])
    R = profile["a"] + profile["c"]
    retained = ("a1", "a2", "c1", "c2") + singletons
    P = sum(profile[slot] for slot in retained)
    La = profile["a1"] + 2 * profile["a2"]
    Lc = profile["c1"] + 2 * profile["c2"]
    S = C + R - P / 2
    arms = (S, (S + R) / 2, S + La - W / 2, S + Lc - W / 2)
    return {"singletons": singletons, "retained": retained,
            "C": C, "W": W, "R": R, "P": P, "La": La, "Lc": Lc,
            "S": S, "arms": arms, "bound": max(arms)}


def check_all_group12a_families(profile):
    single_minimum = None
    single_count = 0
    for combo in itertools.combinations(GROUP12A_C_SINGLETON_POOL, 3):
        singletons = (tuple(sorted(slot for slot in combo if slot[0] == "c"))
                      + tuple(sorted(slot for slot in combo if slot[0] == "b")))
        data = group12a_c_data(profile, singletons)
        require(profile["D"] <= data["bound"],
                f"GROUP12a(c,{singletons}) cuts the protected profile")
        item = (data["bound"], singletons)
        single_minimum = (item if single_minimum is None
                          or item < single_minimum else single_minimum)
        single_count += 1
    require(single_count == 120, "GROUP12a(c) exhaustive count mismatch")

    double_minimum = None
    double_count = 0
    for combo in itertools.combinations(GROUP1212A_SINGLETON_POOL, 2):
        singletons = tuple(sorted(combo, key=lambda slot: (slot[0], slot[1])))
        data = group1212a_data(profile, singletons)
        require(profile["D"] <= data["bound"],
                f"GROUP1212a({singletons}) cuts the protected profile")
        item = (data["bound"], singletons)
        double_minimum = (item if double_minimum is None
                          or item < double_minimum else double_minimum)
        double_count += 1
    require(double_count == 28, "GROUP1212a exhaustive count mismatch")

    single_b_minimum = None
    single_b_count = 0
    for combo in itertools.combinations(GROUP12B_C_SINGLETON_POOL, 3):
        singletons = (tuple(sorted(slot for slot in combo if slot[0] == "c"))
                      + tuple(sorted(slot for slot in combo if slot[0] == "a")))
        data = group12b_c_data(profile, singletons)
        require(profile["D"] <= data["bound"],
                f"GROUP12b(c,{singletons}) cuts the protected profile")
        item = (data["bound"], singletons)
        single_b_minimum = (item if single_b_minimum is None
                            or item < single_b_minimum else single_b_minimum)
        single_b_count += 1
    require(single_b_count == 120, "GROUP12b(c) exhaustive count mismatch")

    double_b_minimum = None
    double_b_count = 0
    for combo in itertools.combinations(GROUP1212B_SINGLETON_POOL, 2):
        singletons = tuple(sorted(combo, key=lambda slot: (slot[0], slot[1])))
        data = group1212b_data(profile, singletons)
        require(profile["D"] <= data["bound"],
                f"GROUP1212b({singletons}) cuts the protected profile")
        item = (data["bound"], singletons)
        double_b_minimum = (item if double_b_minimum is None
                            or item < double_b_minimum else double_b_minimum)
        double_b_count += 1
    require(double_b_count == 28, "GROUP1212b exhaustive count mismatch")
    return {"single_a": (single_minimum, single_count),
            "double_a": (double_minimum, double_count),
            "single_b": (single_b_minimum, single_b_count),
            "double_b": (double_b_minimum, double_b_count)}


def check_fixed_group12(profile):
    summaries = {}
    for powered_side, group_side, other_index in (
            ("c", "a", 4), ("c", "b", 4)):
        data = group12_data(profile, powered_side, group_side, other_index)
        require(profile["D"] <= data["bound"],
                f"GROUP12({powered_side},{group_side}) failed: "
                f"D={profile['D']}, bound={data['bound']}")
        summaries[(powered_side, group_side, other_index)] = data
    return summaries


def check_group12_canary():
    profile = build_balanced_139_257()
    values = check_arch_cover(profile)
    require(values == {"a": Q(1), "b": Q(1), "c": Q(1)},
            f"balanced GROUP12 canary has unexpected ARCH values: {values}")
    data = group12c_data(profile, "a")
    require(data["C"] == Q(40, 1285), "GROUP12 canary C mismatch")
    require(data["W"] == Q(220, 1285), "GROUP12 canary W mismatch")
    require(data["R"] == Q(890, 1285), "GROUP12 canary R mismatch")
    require(data["P"] == Q(890, 1285), "GROUP12 canary P mismatch")
    require(data["L"] == Q(197, 1285), "GROUP12 canary L mismatch")
    require(data["S"] == Q(485, 1285), "GROUP12 canary S mismatch")
    expected_arms = (Q(485, 1285), Q(275, 514), Q(572, 1285))
    require(data["arms"] == expected_arms,
            f"GROUP12 canary arms mismatch: {data['arms']}")
    require(data["bound"] == Q(275, 514),
            f"GROUP12 canary bound mismatch: {data['bound']}")
    require(profile["D"] - data["bound"] == Q(3, 514),
            "GROUP12 canary saving is not 3/514")
    ordinary_descriptor = ("a1", "a4", "b1", "b4")
    ordinary_bound = pow3_bound(profile, "c", ordinary_descriptor)
    require(ordinary_bound == profile["D"] == Q(139, 257),
            f"ordinary POW3c canary is not tight: {ordinary_bound}")
    return {
        "profile_D": profile["D"],
        "ARCH_values": values,
        "GROUP12a": data,
        "ordinary_POW3c": ordinary_bound,
        "saving": Q(3, 514),
    }


def check_group12a_c_canary():
    profile = build_group12a_c_survivor_6_11()
    values = check_arch_cover(profile)
    require(values == {"a": Q(1), "b": Q(1), "c": Q(1)},
            f"GROUP12a(c) canary has unexpected ARCH values: {values}")
    data = group12a_c_data(profile, ("c4", "b1", "b4"))
    require(data["C"] == Q(37, 1375), "GROUP12a(c) canary C mismatch")
    require(data["W"] == Q(1, 22), "GROUP12a(c) canary W mismatch")
    require(data["R"] == Q(926, 1375), "GROUP12a(c) canary R mismatch")
    require(data["P"] == Q(911, 1375), "GROUP12a(c) canary P mismatch")
    require(data["L"] == Q(7, 55), "GROUP12a(c) canary L mismatch")
    require(data["S"] == Q(203, 550), "GROUP12a(c) canary S mismatch")
    expected_arms = (Q(203, 550), Q(2867, 5500), Q(521, 1100))
    require(data["arms"] == expected_arms,
            f"GROUP12a(c) canary arms mismatch: {data['arms']}")
    require(data["bound"] == Q(2867, 5500),
            f"GROUP12a(c) canary bound mismatch: {data['bound']}")
    require(profile["D"] - data["bound"] == Q(133, 5500),
            "GROUP12a(c) canary cut margin mismatch")

    target_data = group12a_c_data(build_witness(), ("c4", "b1", "b4"))
    require(target_data["C"] == target_data["W"] == Q(7, 37),
            "target GROUP12a(c) coefficient ledger mismatch")
    require(target_data["R"] == Q(20, 37)
            and target_data["P"] == Q(15, 37)
            and target_data["L"] == Q(5, 37)
            and target_data["S"] == Q(39, 74),
            "target GROUP12a(c) retained/group ledger mismatch")
    require(target_data["arms"]
            == (Q(39, 74), Q(79, 148), Q(21, 37)),
            "target GROUP12a(c) arms mismatch")
    require(build_witness()["D"] <= target_data["bound"],
            "GROUP12a(c) cuts the protected target")
    second = build_group12a_c_second_face_110_203()
    second_values = check_arch_cover(second)
    require(second_values == {"a": Q(1), "b": Q(1), "c": Q(1)},
            f"second GROUP12a(c) face has unexpected ARCH values: {second_values}")
    second_data = group12a_c_data(second, ("c4", "b1", "b5"))
    require((second_data["C"], second_data["W"], second_data["R"],
             second_data["P"], second_data["L"], second_data["S"])
            == (Q(64, 609), Q(38, 203), Q(380, 609), Q(374, 609),
                Q(27, 203), Q(257, 609)),
            "second GROUP12a(c;b5) coefficient/retained ledger mismatch")
    require(second_data["arms"]
            == (Q(257, 609), Q(91, 174), Q(281, 609)),
            "second GROUP12a(c;b5) arms mismatch")
    require(second_data["bound"] == Q(91, 174)
            and second["D"] - second_data["bound"] == Q(23, 1218),
            "second GROUP12a(c;b5) cut mismatch")
    target_b5 = group12a_c_data(build_witness(), ("c4", "b1", "b5"))
    require(all(target_b5[key] == target_data[key]
                for key in ("C", "W", "R", "P", "L", "S", "arms", "bound")),
            "b4/b5 variants should have the same target ledger")

    third = build_group1212a_third_face_46_85()
    third_values = check_arch_cover(third)
    require(third_values == {"a": Q(15, 17), "b": Q(1), "c": Q(1)},
            f"GROUP1212a face has unexpected ARCH values: {third_values}")
    third_data = group1212a_data(third, ("b4", "c4"))
    require((third_data["C"], third_data["W"], third_data["R"],
             third_data["P"], third_data["Lb"], third_data["Lc"],
             third_data["S"])
            == (Q(3, 85), Q(3, 85), Q(58, 85), Q(58, 85),
                Q(73, 425), Q(57, 425), Q(32, 85)),
            "GROUP1212a third-face ledger mismatch")
    require(third_data["arms"]
            == (Q(32, 85), Q(9, 17), Q(451, 850), Q(419, 850)),
            "GROUP1212a third-face arms mismatch")
    require(third_data["bound"] == Q(451, 850)
            and third["D"] - third_data["bound"] == Q(9, 850),
            "GROUP1212a third-face cut mismatch")
    third_target = group1212a_data(build_witness(), ("b4", "c4"))
    require(third_target["arms"]
            == (Q(39, 74), Q(79, 148), Q(18, 37), Q(21, 37))
            and build_witness()["D"] <= third_target["bound"],
            "GROUP1212a cuts the protected target")

    reflected = build_group1212b_reflected_face_46_85()
    reflected_values = check_arch_cover(reflected)
    require(reflected_values == {"a": Q(1), "b": Q(15, 17), "c": Q(1)},
            f"GROUP1212b reflected face has unexpected ARCH values: "
            f"{reflected_values}")
    reflected_data = group1212b_data(reflected, ("a4", "c4"))
    require((reflected_data["C"], reflected_data["W"], reflected_data["R"],
             reflected_data["P"], reflected_data["La"], reflected_data["Lc"],
             reflected_data["S"])
            == (Q(3, 85), Q(3, 85), Q(58, 85), Q(58, 85),
                Q(73, 425), Q(57, 425), Q(32, 85)),
            "GROUP1212b reflected-face ledger mismatch")
    require(reflected_data["arms"]
            == (Q(32, 85), Q(9, 17), Q(451, 850), Q(419, 850)),
            "GROUP1212b reflected-face arms mismatch")
    require(reflected_data["bound"] == Q(451, 850)
            and reflected["D"] - reflected_data["bound"] == Q(9, 850),
            "GROUP1212b reflected-face cut mismatch")
    reflected_target = group1212b_data(build_witness(), ("a4", "c4"))
    require(build_witness()["D"] <= reflected_target["bound"],
            "GROUP1212b cuts the protected target")

    return {
        "profile_D": profile["D"], "ARCH_values": values,
        "GROUP12a_c_b4": data, "second_profile_D": second["D"],
        "second_ARCH_values": second_values, "GROUP12a_c_b5": second_data,
        "target_GROUP12a_c": target_data,
        "third_profile_D": third["D"], "third_ARCH_values": third_values,
        "GROUP1212a": third_data, "target_GROUP1212a": third_target,
        "reflected_profile_D": reflected["D"],
        "reflected_ARCH_values": reflected_values,
        "GROUP1212b": reflected_data, "target_GROUP1212b": reflected_target,
        "saving": profile["D"] - data["bound"],
        "second_saving": second["D"] - second_data["bound"],
        "third_saving": third["D"] - third_data["bound"],
        "reflected_saving": reflected["D"] - reflected_data["bound"],
    }


def un_bound(profile, side, free1, free2, selected_mask):
    """Evaluate docs/885 Proposition 5.1, equation (5.6), exactly."""
    require(side in SIDES, "UN has an invalid modulus side")
    mask_elements(free1, allow_tail=False)
    mask_elements(free2, allow_tail=False)
    require(free1 or free2, "Proposition 5.1 free masks are both empty")
    cost, weight = selected_root_value(
        profile, side, selected_mask, allow_tail=True, require_nonempty=True)
    y, z = SIDES[side]
    free_root_y, free_value_y = selected_root_value(
        profile, y, free1, allow_tail=False)
    free_root_z, free_value_z = selected_root_value(
        profile, z, free2, allow_tail=False)
    q = free_gcd(free1, free2)
    fixed_cost = (profile[y] - free_root_y
                  + profile[z] - free_root_z + cost)
    return fixed_cost + max(Q(0), (free_value_y + free_value_z) / q - weight)


def check_all_regular_free_un(profile):
    minimum = None
    count = 0
    # Cache each fixed/free component without changing the Fraction semantics.
    tables = {}
    for side in "abc":
        tables[side] = {
            "regular": tuple(selected_root_value(
                profile, side, mask, allow_tail=False) for mask in range(64)),
            "modulus": tuple([None] + [selected_root_value(
                profile, side, mask, allow_tail=True, require_nonempty=True)
                for mask in range(1, 128)]),
        }
    for side in "abc":
        y, z = SIDES[side]
        for free1 in range(64):
            free_root_y, free_value_y = tables[y]["regular"][free1]
            for free2 in range(64):
                if free1 == 0 and free2 == 0:
                    continue
                free_root_z, free_value_z = tables[z]["regular"][free2]
                q = free_gcd(free1, free2)
                fixed_yz = (profile[y] - free_root_y
                            + profile[z] - free_root_z)
                free_value = (free_value_y + free_value_z) / q
                for selected_mask in range(1, 128):
                    cost, weight = tables[side]["modulus"][selected_mask]
                    bound = fixed_yz + cost + max(Q(0), free_value - weight)
                    require(profile["D"] <= bound,
                            f"UN({side},{free1},{free2},{selected_mask}) failed")
                    item = (bound, side, free1, free2, selected_mask)
                    minimum = item if minimum is None or item < minimum else minimum
                    count += 1
    expected = 3 * (64 * 64 - 1) * 127
    require(count == expected, f"regular-free UN count {count} != {expected}")
    return minimum, count


def expect_failure(name, function):
    try:
        function()
    except WitnessError:
        return name
    fail(f"mutation test {name!r} was incorrectly accepted")


def run_fail_closed_mutation_tests(profile, un_minimum):
    passed = []

    bad_extra = dict(profile)
    bad_extra["unexpected"] = Q(0)
    passed.append(expect_failure("unknown-profile-variable",
                                 lambda: validate_profile(bad_extra)))

    bad_negative = dict(profile)
    bad_negative["a2"] = Q(-1, 37)
    passed.append(expect_failure("negative-root-mass",
                                 lambda: check_base_and_hb3(bad_negative)))

    bad_tail = dict(profile)
    bad_tail["vb"] = Q(34, 37)
    passed.append(expect_failure("tail7-underpayment",
                                 lambda: check_base_and_hb3(bad_tail)))

    bad_D = dict(profile)
    bad_D["D"] = profile["D"] + Q(1, 37)
    passed.append(expect_failure("spacing-D-increase",
                                 lambda: check_spacing(bad_D)))

    passed.append(expect_failure(
        "empty-PS23-modulus-mask", lambda: ps23_bound(profile, "a", 0)))
    passed.append(expect_failure(
        "free-tail-UN-mask", lambda: un_bound(profile, "a", 64, 1, 1)))
    passed.append(expect_failure(
        "double-empty-UN-free-mask", lambda: un_bound(profile, "a", 0, 0, 1)))
    passed.append(expect_failure(
        "duplicate-CS4-held-slot",
        lambda: cs4_bound(profile, "a", 1, ("b1", "b1", "c1", "c2"))))
    passed.append(expect_failure(
        "powered-side-POW3b-held-slot",
        lambda: pow3_bound(profile, "b", ("a1", "a3", "b1", "c1"))))
    passed.append(expect_failure(
        "powered-side-POW3a-held-slot",
        lambda: pow3_bound(profile, "a", ("a1", "b1", "c1", "c3"))))
    passed.append(expect_failure(
        "unsafe-POW3a-held-tuple",
        lambda: pow3_bound(profile, "a", ("b1", "b2", "c1", "c4"))))
    passed.append(expect_failure(
        "powered-side-POW3c-held-slot",
        lambda: pow3_bound(profile, "c", ("a1", "b1", "c1", "c3"))))

    bad_arch = dict(profile)
    bad_arch["c4"] = Q(7, 37)
    passed.append(expect_failure(
        "ARCH-value-cover-violation", lambda: check_arch_cover(bad_arch)))
    passed.append(expect_failure(
        "forbidden-GROUP12-powered-grouped-pair",
        lambda: group12_data(profile, "a", "b", 4)))
    passed.append(expect_failure(
        "noncanonical-GROUP12a-singletons",
        lambda: group12a_c_data(profile, ("b1", "c4", "b4"))))
    passed.append(expect_failure(
        "noncanonical-GROUP12b-singletons",
        lambda: group12b_c_data(profile, ("a1", "c4", "a4"))))
    passed.append(expect_failure(
        "duplicate-GROUP1212a-singletons",
        lambda: group1212a_data(profile, ("b4", "b4"))))
    passed.append(expect_failure(
        "duplicate-GROUP1212b-singletons",
        lambda: group1212b_data(profile, ("a4", "a4"))))

    # The exhaustive scan found an exact target-binding UN tuple.  Increasing
    # D must therefore fail the already-computed exact lower-bound comparison.
    passed.append(expect_failure(
        "UN-D-increase",
        lambda: require(bad_D["D"] <= un_minimum[0],
                        "mutated D exceeds exhaustive UN minimum")))
    require(len(passed) == 19, "mutation-test count mismatch")
    return passed


def main():
    parser = argparse.ArgumentParser(
        description="Standalone exact audit of a declared profile")
    parser.add_argument(
        "--profile", choices=("target-20/37", "survivor-6/11"),
        default="target-20/37")
    args = parser.parse_args()
    profile = (build_witness() if args.profile == "target-20/37"
               else build_survivor_6_11())
    base = check_base_and_hb3(profile)
    geometry_minimum, geometry_count = check_geometry(profile)
    det = check_det(profile)
    spacing_minimum, spacing_count = check_spacing(profile)
    ps_minimum, ps_count = check_all_ps23(profile)
    cs4_minimum, cs4_count = check_all_regular_cs4(profile)
    pow3 = check_all_directional_pow3(profile)
    pow3_canaries = check_directional_pow3_canaries()
    group12 = check_fixed_group12(profile)
    group12a_families = check_all_group12a_families(profile)
    group12_canary = check_group12_canary()
    group12a_c_canary = check_group12a_c_canary()
    un_minimum, un_count = check_all_regular_free_un(profile)
    mutation_tests = run_fail_closed_mutation_tests(profile, un_minimum)

    print("EXACT_WITNESS_CLEAN_PASS")
    print(f"profile={args.profile}")
    print(f"D={profile['D']} L={base['L']} values={base['values']}")
    print(f"HB3={base['HB3']} DET={det}")
    print(f"geometry_count={geometry_count} minimum={geometry_minimum}")
    print(f"spacing_count={spacing_count} minimum={spacing_minimum}")
    print(f"PS23_count={ps_count} minimum={ps_minimum}")
    print(f"regular_CS4_count={cs4_count} minimum={cs4_minimum}")
    print(f"regular_POW3b_count={pow3['b'][1]} minimum={pow3['b'][0]}")
    print(f"target_safe_POW3a_count={pow3['a'][1]} minimum={pow3['a'][0]}")
    print(f"regular_POW3c_count={pow3['c'][1]} minimum={pow3['c'][0]}")
    print(f"directional_6over11_canaries={pow3_canaries}")
    print(f"fixed_GROUP12c_a={group12[('c', 'a', 4)]}")
    print(f"fixed_GROUP12c_b={group12[('c', 'b', 4)]}")
    print(f"exhaustive_GROUP12ab_families={group12a_families}")
    print(f"balanced_139over257_GROUP12_canary={group12_canary}")
    print(f"six_over_11_GROUP12a_c_canary={group12a_c_canary}")
    print(f"regular_free_UN_count={un_count} minimum={un_minimum}")
    print(f"fail_closed_mutations={len(mutation_tests)} names={','.join(mutation_tests)}")


if __name__ == "__main__":
    try:
        main()
    except (WitnessError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
