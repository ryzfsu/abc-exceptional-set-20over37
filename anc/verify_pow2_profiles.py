#!/usr/bin/env python3
"""Standalone exact audit of regular four-block unlocalized POW2 rows.

Only the Python standard library is used.  This verifier is independent of
the search generator and both clean verifiers.
"""

import itertools
from fractions import Fraction


Q = Fraction
RNG = tuple(range(1, 7))


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def blank_profile():
    profile = {"D": Q(0), "a": Q(0), "b": Q(0), "c": Q(0)}
    profile.update({f"{side}{index}": Q(0)
                    for side in "abc" for index in RNG})
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


def survivor_46_85():
    profile = blank_profile()
    profile.update({
        "D": Q(46, 85),
        "a": Q(141, 425),
        "a1": Q(33, 425), "a2": Q(20, 425), "a4": Q(88, 425),
        "b": Q(149, 425),
        "b1": Q(57, 425), "b4": Q(92, 425),
        "c": Q(135, 425),
        "c1": Q(15, 425), "c3": Q(120, 425),
    })
    return profile


def reflected_b_canary():
    """The a<->b reflection of the exact 46/85 profile."""
    original = survivor_46_85()
    profile = blank_profile()
    profile["D"] = original["D"]
    for index in RNG:
        profile[f"a{index}"] = original[f"b{index}"]
        profile[f"b{index}"] = original[f"a{index}"]
        profile[f"c{index}"] = original[f"c{index}"]
    profile["a"], profile["b"], profile["c"] = (
        original["b"], original["a"], original["c"])
    return profile


def rotated_c_canary():
    """A coefficient/result-side arithmetic canary with the same ledger."""
    profile = blank_profile()
    profile.update({
        "D": Q(46, 85),
        "a": Q(149, 425), "a1": Q(57, 425), "a4": Q(92, 425),
        "b": Q(135, 425), "b1": Q(15, 425), "b3": Q(120, 425),
        "c": Q(141, 425),
        "c1": Q(33, 425), "c2": Q(20, 425), "c4": Q(88, 425),
    })
    return profile


def regular_slots(represented):
    return tuple(f"{side}{index}" for side in represented for index in RNG)


def pow2_arms(profile, powered_side, held):
    require(powered_side in "abc", "forbidden powered side")
    require(type(held) is tuple and len(held) == 4,
            "retained tuple must have length four")
    require(len(set(held)) == 4, "duplicate retained slot")
    require(tuple(sorted(held)) == held, "retained tuple is not canonical")
    represented = tuple(side for side in "abc" if side != powered_side)
    allowed = frozenset(regular_slots(represented))
    require(all(slot in allowed for slot in held),
            "retained slot lies on powered side or is malformed")

    coefficient_cost = (profile[powered_side]
                        - profile[f"{powered_side}2"]
                        - profile[f"{powered_side}4"]
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
    records = []
    for held in itertools.combinations(regular_slots(represented), 4):
        records.append((pow2_arms(profile, powered_side, held)["bound"], held))
    require(len(records) == 495, "descriptor count is not C(12,4)")
    minimum_value = min(record[0] for record in records)
    minima = tuple(record for record in records if record[0] == minimum_value)
    cuts = tuple(record for record in records if record[0] < profile["D"])
    tight = tuple(record for record in records if record[0] == profile["D"])
    return {"minimum": minima[0], "minimum_ties": len(minima),
            "cuts": cuts, "tight": tight, "count": len(records)}


def expect_failure(name, function):
    try:
        function()
    except AuditError:
        return name
    raise AuditError(f"mutation {name!r} was accepted")


def mutation_suite(target, survivor):
    passed = []
    passed.append(expect_failure(
        "powered-side-slot",
        lambda: pow2_arms(target, "a", ("a1", "b1", "c1", "c3"))))
    passed.append(expect_failure(
        "duplicate-slot",
        lambda: pow2_arms(target, "a", ("b1", "b1", "c1", "c3"))))
    passed.append(expect_failure(
        "noncanonical-order",
        lambda: pow2_arms(target, "a", ("c1", "b1", "b4", "c3"))))
    passed.append(expect_failure(
        "forbidden-powered-side",
        lambda: pow2_arms(target, "d", ("a1", "a2", "b1", "b2"))))
    passed.append(expect_failure(
        "tail-slot-is-not-regular",
        lambda: pow2_arms(target, "a", ("b1", "b4", "c1", "c7"))))

    weaker = pow2_arms(survivor, "a", ("b1", "b4", "c2", "c3"))
    passed.append(expect_failure(
        "weakened-descriptor-does-not-cut",
        lambda: require(weaker["bound"] < survivor["D"],
                        "weakened descriptor is not a strict cut")))
    require(len(passed) == 6, "mutation count mismatch")
    return passed


def main():
    target = target_profile()
    survivor = survivor_46_85()

    target_expected = {
        "a": (Q(59, 74), 9),
        "b": (Q(26, 37), 1),
        "c": (Q(87, 148), 9),
    }
    target_scans = {}
    for side in "abc":
        result = scan_family(target, side)
        target_scans[side] = result
        require((result["minimum"][0], result["minimum_ties"])
                == target_expected[side], f"target POW2({side}) minimum mismatch")
        require(not result["cuts"] and not result["tight"],
                f"target is cut or bound by POW2({side})")

    survivor_expected = {
        "a": Q(27, 50),
        "b": Q(957, 1700),
        "c": Q(58, 85),
    }
    survivor_scans = {}
    for side in "abc":
        result = scan_family(survivor, side)
        survivor_scans[side] = result
        require(result["minimum"][0] == survivor_expected[side]
                and result["minimum_ties"] == 1,
                f"survivor POW2({side}) minimum mismatch")
    require(len(survivor_scans["a"]["cuts"]) == 1,
            "survivor should have exactly one POW2(a) cut")
    require(not survivor_scans["b"]["cuts"]
            and not survivor_scans["c"]["cuts"],
            "survivor is unexpectedly cut in another direction")

    descriptor_a = ("b1", "b4", "c1", "c3")
    arms_a = pow2_arms(survivor, "a", descriptor_a)
    require(arms_a["C"] == Q(33, 425)
            and arms_a["R"] == arms_a["P"] == Q(284, 425),
            "survivor POW2(a) ledger mismatch")
    require(arms_a["S"] == Q(7, 17)
            and arms_a["average"] == Q(27, 50),
            "survivor POW2(a) children mismatch")
    require(survivor["D"] - arms_a["bound"] == Q(1, 850),
            "survivor POW2(a) margin mismatch")
    require(pow2_arms(target, "a", descriptor_a)["bound"] == Q(67, 74),
            "fixed descriptor is not target-safe")

    reflection = reflected_b_canary()
    descriptor_b = ("a1", "a4", "c1", "c3")
    reflection_arms = pow2_arms(reflection, "b", descriptor_b)
    require(reflection_arms["bound"] == Q(27, 50)
            and reflection["D"] - reflection_arms["bound"] == Q(1, 850),
            "reflected POW2(b) canary mismatch")

    rotation = rotated_c_canary()
    descriptor_c = ("a1", "a4", "b1", "b3")
    rotation_arms = pow2_arms(rotation, "c", descriptor_c)
    require(rotation_arms["bound"] == Q(27, 50)
            and rotation["D"] - rotation_arms["bound"] == Q(1, 850),
            "rotated POW2(c) canary mismatch")

    mutations = mutation_suite(target, survivor)
    print("POW2_PROFILES_STANDALONE_PASS")
    for side in "abc":
        result = target_scans[side]
        print(f"target_POW2{side}_count={result['count']} "
              f"minimum={result['minimum']} ties={result['minimum_ties']} "
              f"cuts={len(result['cuts'])} tight={len(result['tight'])}")
    for side in "abc":
        result = survivor_scans[side]
        print(f"W46_POW2{side}_count={result['count']} "
              f"minimum={result['minimum']} ties={result['minimum_ties']} "
              f"cuts={len(result['cuts'])} tight={len(result['tight'])}")
    print(f"W46_descriptor={descriptor_a} C={arms_a['C']} R={arms_a['R']} "
          f"P={arms_a['P']} S={arms_a['S']} average={arms_a['average']} "
          f"margin={survivor['D'] - arms_a['bound']}")
    print(f"reflected_b_descriptor={descriptor_b} bound={reflection_arms['bound']} "
          f"margin={reflection['D'] - reflection_arms['bound']}")
    print(f"rotated_c_descriptor={descriptor_c} bound={rotation_arms['bound']} "
          f"margin={rotation['D'] - rotation_arms['bound']}")
    print("minimal_current_static_subset=POW2a:b1,b4,c1,c3")
    print(f"fail_closed_mutations={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
