#!/usr/bin/env python3
"""Standalone exact audit of the result-side unlocalized POW3(c) row.

Only the Python standard library is used.  This file imports neither the
search generator nor either clean verifier.
"""

import itertools
from fractions import Fraction


Q = Fraction
RNG = tuple(range(1, 7))
TARGET_A_MASS_NUM = {"b1": 2, "c1": 5, "c4": 8}


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def blank_profile():
    profile = {side: Q(0) for side in "abc"}
    profile.update({f"{side}{index}": Q(0)
                    for side in "abc" for index in RNG})
    profile["D"] = Q(0)
    return profile


def target_profile():
    profile = blank_profile()
    profile.update({
        "D": Q(20, 37),
        "a": Q(17, 37), "a1": Q(7, 37), "a3": Q(10, 37),
        "b": Q(7, 37), "b1": Q(2, 37),
        "c": Q(13, 37), "c1": Q(5, 37), "c4": Q(8, 37),
    })
    return profile


def result_side_survivor():
    profile = blank_profile()
    profile.update({
        "D": Q(6, 11),
        "a": Q(3, 11), "a1": Q(1, 11), "a5": Q(2, 11),
        "b": Q(3, 11), "b3": Q(1, 11), "b4": Q(2, 11),
        "c": Q(5, 11), "c1": Q(2, 11), "c3": Q(3, 11),
    })
    return profile


def regular_slots(represented):
    return tuple(f"{side}{index}" for side in represented for index in RNG)


def pow3_arms(profile, powered_side, held):
    require(powered_side in "abc", "forbidden powered side")
    require(type(held) is tuple and len(held) == 4,
            "retained tuple must have length four")
    require(len(set(held)) == 4, "duplicate retained slot")
    require(tuple(sorted(held)) == held, "retained tuple is not canonical")
    represented = tuple(side for side in "abc" if side != powered_side)
    allowed = frozenset(regular_slots(represented))
    require(all(slot in allowed for slot in held),
            "retained slot lies on powered side or is malformed")
    if powered_side == "a":
        target_mass = sum(TARGET_A_MASS_NUM.get(slot, 0) for slot in held)
        require(target_mass <= 14, "unsafe POW3(a) target descriptor")

    coefficient_cost = (profile[powered_side]
                        - profile[f"{powered_side}3"]
                        - profile[f"{powered_side}6"])
    represented_radical = sum((profile[side] for side in represented), Q(0))
    retained_mass = sum((profile[slot] for slot in held), Q(0))
    child_s = coefficient_cost + represented_radical - retained_mass / 2
    child_average = (child_s + represented_radical) / 2
    return {
        "C": coefficient_cost,
        "R": represented_radical,
        "P": retained_mass,
        "S": child_s,
        "average": child_average,
        "bound": max(child_s, child_average),
    }


def scan_family(profile, powered_side):
    represented = tuple(side for side in "abc" if side != powered_side)
    minimum = None
    count = 0
    tight_minimum = 0
    for held in itertools.combinations(regular_slots(represented), 4):
        if powered_side == "a" and sum(
                TARGET_A_MASS_NUM.get(slot, 0) for slot in held) > 14:
            continue
        arms = pow3_arms(profile, powered_side, held)
        item = (arms["bound"], held)
        if minimum is None or item[0] < minimum[0]:
            minimum = item
            tight_minimum = 1
        elif item[0] == minimum[0]:
            tight_minimum += 1
        count += 1
    return minimum, count, tight_minimum


def expect_failure(name, function):
    try:
        function()
    except AuditError:
        return name
    raise AuditError(f"mutation {name!r} was accepted")


def mutation_suite(target, survivor):
    passed = []
    passed.append(expect_failure(
        "powered-side-c-slot",
        lambda: pow3_arms(target, "c", ("a1", "b1", "c1", "c3"))))
    passed.append(expect_failure(
        "duplicate-slot",
        lambda: pow3_arms(target, "c", ("a1", "a1", "b1", "b2"))))
    passed.append(expect_failure(
        "noncanonical-order",
        lambda: pow3_arms(target, "c", ("b1", "a1", "a2", "b2"))))
    passed.append(expect_failure(
        "unsafe-a-descriptor",
        lambda: pow3_arms(target, "a", ("b1", "b2", "c1", "c4"))))
    passed.append(expect_failure(
        "forbidden-powered-side",
        lambda: pow3_arms(target, "d", ("a1", "a2", "b1", "b2"))))

    weaker = pow3_arms(survivor, "c", ("a1", "a2", "a5", "b3"))
    passed.append(expect_failure(
        "weakened-canary-descriptor-does-not-cut",
        lambda: require(weaker["bound"] < survivor["D"],
                        "weakened descriptor is not a strict cut")))
    require(len(passed) == 6, "mutation count mismatch")
    return passed


def main():
    target = target_profile()
    survivor = result_side_survivor()

    target_c_minimum, target_c_count, target_c_ties = scan_family(target, "c")
    require(target_c_count == 495, "POW3(c) target descriptor count mismatch")
    require(target_c_minimum[0] == Q(55, 74),
            "unexpected target POW3(c) minimum")
    require(target_c_ties == 9, "unexpected target POW3(c) minimum tie count")
    require(target["a"] + target["b"] == Q(24, 37),
            "unexpected target direct represented radical")
    require(target["D"] <= target_c_minimum[0],
            "POW3(c) cuts the target witness")

    descriptor = ("a1", "a5", "b3", "b4")
    c_canary = pow3_arms(survivor, "c", descriptor)
    require(c_canary["R"] == Q(6, 11), "unexpected canary direct R")
    require(c_canary["S"] == Q(5, 11), "unexpected canary S child")
    require(c_canary["average"] == Q(1, 2),
            "unexpected canary average child")
    require(c_canary["bound"] == Q(1, 2), "unexpected canary POW3(c) bound")
    require(survivor["D"] - c_canary["bound"] == Q(1, 22),
            "unexpected canary strict saving")

    b_minimum, b_count, _ = scan_family(survivor, "b")
    a_minimum, a_count, _ = scan_family(survivor, "a")
    require(b_count == 495 and b_minimum[0] == Q(7, 11),
            "POW3(b) canary scan mismatch")
    require(a_count == 486 and a_minimum[0] == Q(15, 22),
            "POW3(a) canary scan mismatch")
    require(b_minimum[0] >= survivor["D"]
            and a_minimum[0] >= survivor["D"],
            "an a/b row unexpectedly cuts the c-heavy canary")

    mutations = mutation_suite(target, survivor)
    print("POW3C_PROFILES_STANDALONE_PASS")
    print(f"target_direct_R={target['a'] + target['b']} "
          f"pow3c_count={target_c_count} minimum={target_c_minimum} "
          f"minimum_ties={target_c_ties}")
    print(f"c_heavy_descriptor={descriptor} C={c_canary['C']} R={c_canary['R']} "
          f"P={c_canary['P']} S={c_canary['S']} "
          f"average={c_canary['average']} saving={survivor['D'] - c_canary['bound']}")
    print(f"c_heavy_pow3b_minimum={b_minimum} count={b_count}")
    print(f"c_heavy_pow3a_safe_minimum={a_minimum} count={a_count}")
    print(f"fail_closed_mutations={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
