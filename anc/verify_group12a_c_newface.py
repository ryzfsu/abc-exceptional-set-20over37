#!/usr/bin/env python3
"""Standalone exact audit of the target-safe GROUP12(a,c) clause.

The powered side is a.  The represented c-side factors c1 and c2 are
grouped as F_c1(chi) F_c2(chi**2), while c4, b1, and b4 are singleton
fourth-moment factors.  This file uses only the Python standard library and
imports nothing from the generator or either tree verifier.
"""

from fractions import Fraction


Q = Fraction
RNG = tuple(range(1, 7))
DESCRIPTORS = {
    4: (("c1", "c2"), ("b1", "b4", "c4")),
    5: (("c1", "c2"), ("b1", "b5", "c4")),
}


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def blank_profile():
    profile = {"D": Q(0), "a": Q(0), "b": Q(0), "c": Q(0)}
    profile.update({f"{side}{index}": Q(0)
                    for side in "abc" for index in RNG})
    profile.update({f"v{side}": Q(0) for side in "abc"})
    return profile


def target_profile():
    profile = blank_profile()
    profile.update({
        "D": Q(20, 37),
        "a": Q(17, 37), "a1": Q(7, 37), "a3": Q(10, 37),
        "b": Q(7, 37), "b1": Q(2, 37), "vb": Q(35, 37),
        "c": Q(13, 37), "c1": Q(5, 37), "c4": Q(8, 37),
    })
    return profile


def new_face_profile():
    profile = blank_profile()
    profile.update({
        "D": Q(6, 11),
        "a": Q(449, 1375), "a1": Q(23, 2750),
        "a3": Q(412, 1375), "a5": Q(51, 2750),
        "b": Q(41, 125), "b1": Q(148, 1375),
        "b4": Q(288, 1375), "b5": Q(3, 275),
        "c": Q(19, 55), "c1": Q(7, 55), "c4": Q(12, 55),
    })
    return profile


def second_face_profile():
    profile = blank_profile()
    profile.update({
        "D": Q(110, 203),
        "a": Q(229, 609), "a1": Q(2, 87), "a2": Q(50, 609),
        "a3": Q(55, 203),
        "b": Q(167, 609), "b1": Q(52, 609), "b2": Q(2, 203),
        "b5": Q(109, 609),
        "c": Q(71, 203), "c1": Q(27, 203), "c4": Q(44, 203),
    })
    return profile


def slot_parts(slot):
    require(type(slot) is str and len(slot) == 2
            and slot[0] in "abc" and slot[1] in "123456",
            "invalid regular slot")
    return slot[0], int(slot[1])


def coefficient(profile):
    regular = sum((profile[f"a{i}"] for i in RNG), Q(0))
    tail = profile["a"] - regular
    require(tail >= 0, "powered-side regular mass exceeds radical mass")
    require(profile["va"] >= 7 * tail,
            "powered-side tail value is below seven times its mass")
    cost = tail + sum((profile[f"a{i}"] for i in (1, 2, 4, 5)), Q(0))
    weight = (profile["va"] + profile["a1"] + 2 * profile["a2"]
              + profile["a4"] + 2 * profile["a5"])
    require(cost == profile["a"] - profile["a3"] - profile["a6"],
            "coefficient cost identity failed")
    require(weight >= cost, "coefficient value is below root cost")
    return cost, weight


def group12a_c(profile, other_index=4, group=None, singletons=None):
    require(other_index in DESCRIPTORS, "unauthorized other-side singleton")
    expected_group, expected_singletons = DESCRIPTORS[other_index]
    group = expected_group if group is None else group
    singletons = expected_singletons if singletons is None else singletons
    require(type(group) is tuple and group == expected_group,
            "group is not the typed c1,c2 pair")
    require(type(singletons) is tuple and singletons == expected_singletons,
            "singletons do not match the fixed b1,b4,c4 triple")
    selected = group + singletons
    require(len(set(selected)) == 5, "selected blocks are not distinct")
    require(all(slot_parts(slot)[0] in "bc" for slot in selected),
            "a selected block lies on powered side a")
    require(slot_parts(group[0]) == ("c", 1)
            and slot_parts(group[1]) == ("c", 2),
            "grouped character powers are not chi,chi^2 on side c")
    require(Q(1, 4) + 3 * Q(1, 4) == 1,
            "fourfold Holder budget does not close")

    C, W = coefficient(profile)
    R = profile["b"] + profile["c"]
    P = sum((profile[slot] for slot in selected), Q(0))
    L = profile["c1"] + 2 * profile["c2"]
    S = C + R - P / 2
    threshold = L - W / 2
    balance = (R - S) / 2
    theta = max(Q(0), threshold, balance)
    q = W + 2 * theta
    require(q >= 2 * L, "grouped fourth-moment guard failed")
    arms = (S, (S + R) / 2, S + threshold)
    direct = max(S + theta, R - theta)
    require(max(arms) == direct,
            "three-arm OR disagrees with direct scale optimization")
    return {
        "C": C, "W": W, "R": R, "P": P, "L": L, "S": S,
        "threshold": threshold, "balance": balance, "theta": theta,
        "q": q, "guard_slack": q - 2 * L, "arms": arms,
        "theorem": max(arms), "direct_R": R,
        "effective": min(R, max(arms)),
    }


def optimizer_grid_audit():
    values = (Q(0), Q(1, 10), Q(1, 4), Q(1, 2), Q(4, 5))
    cases = 0
    checks = 0
    for S in values:
        for R in values:
            for L in values:
                for W in values:
                    threshold = L - W / 2
                    theta = max(Q(0), threshold, (R - S) / 2)
                    direct = max(S + theta, R - theta)
                    arms = (S, (S + R) / 2, S + threshold)
                    require(direct == max(arms), "optimizer grid mismatch")
                    for D in values:
                        require((D <= max(arms)) == any(D <= arm for arm in arms),
                                "OR/max equivalence failed")
                        checks += 1
                    cases += 1
    return cases, checks


def expect_failure(name, function):
    try:
        function()
    except AuditError:
        return name
    raise AuditError(f"mutation {name!r} was accepted")


def mutation_suite(target, face):
    passed = []
    passed.append(expect_failure(
        "duplicate-group-slot",
        lambda: group12a_c(target, group=("c1", "c1"))))
    passed.append(expect_failure(
        "cross-side-group",
        lambda: group12a_c(target, group=("c1", "b2"))))
    passed.append(expect_failure(
        "wrong-singleton",
        lambda: group12a_c(target, singletons=("b1", "b4", "c5"))))
    passed.append(expect_failure(
        "powered-side-singleton",
        lambda: group12a_c(target, singletons=("a1", "b4", "c4"))))
    passed.append(expect_failure(
        "unauthorized-other-index",
        lambda: group12a_c(target, other_index=3)))

    S, R, L, W = Q(1, 10), Q(1, 2), Q(4, 5), Q(1, 5)
    correct = max(S, (S + R) / 2, S + L - W / 2)
    reversed_sign = max(S, (S + R) / 2, S - L + W / 2)
    missing_two = max(S, (S + R) / 2, S + (L - W) / 2)
    passed.append(expect_failure(
        "reversed-guard-sign",
        lambda: require(reversed_sign == correct, "guard sign changed")))
    passed.append(expect_failure(
        "missing-factor-two",
        lambda: require(missing_two == correct, "guard factor changed")))

    mutated = dict(face)
    mutated["a"] += Q(1, 1375)
    passed.append(expect_failure(
        "unresolved-powered-mass", lambda: group12a_c(mutated)))
    require(len(passed) == 8, "mutation count mismatch")
    return passed


def main():
    target = target_profile()
    face = new_face_profile()
    second = second_face_profile()
    got_target = group12a_c(target, 4)
    got_target_b5 = group12a_c(target, 5)
    got_face = group12a_c(face, 4)
    got_second = group12a_c(second, 5)

    require((got_target["C"], got_target["W"], got_target["R"],
             got_target["P"], got_target["L"], got_target["S"])
            == (Q(7, 37), Q(7, 37), Q(20, 37), Q(15, 37),
                Q(5, 37), Q(39, 74)),
            "target coefficient/retained ledger mismatch")
    require(got_target["arms"]
            == (Q(39, 74), Q(79, 148), Q(21, 37)),
            "target arms mismatch")
    require(got_target["effective"] == target["D"] == Q(20, 37),
            "target is not preserved by direct R equality")
    require(all(got_target_b5[key] == got_target[key]
                for key in ("C", "W", "R", "P", "L", "S", "arms",
                            "theorem", "effective")),
            "b4/b5 target ledgers differ")

    require((got_face["C"], got_face["W"], got_face["R"],
             got_face["P"], got_face["L"], got_face["S"])
            == (Q(37, 1375), Q(1, 22), Q(926, 1375), Q(911, 1375),
                Q(7, 55), Q(203, 550)),
            "new-face coefficient/retained ledger mismatch")
    require(got_face["arms"]
            == (Q(203, 550), Q(2867, 5500), Q(521, 1100)),
            "new-face arms mismatch")
    require(got_face["effective"] == Q(2867, 5500),
            "new-face effective bound mismatch")
    require(face["D"] - got_face["effective"] == Q(133, 5500),
            "new-face strict cut mismatch")
    require(Q(20, 37) - got_face["effective"] == Q(3921, 203500),
            "new-face margin below target mismatch")

    require((got_second["C"], got_second["W"], got_second["R"],
             got_second["P"], got_second["L"], got_second["S"])
            == (Q(64, 609), Q(38, 203), Q(380, 609), Q(374, 609),
                Q(27, 203), Q(257, 609)),
            "second-face coefficient/retained ledger mismatch")
    require(got_second["arms"]
            == (Q(257, 609), Q(91, 174), Q(281, 609)),
            "second-face arms mismatch")
    require(got_second["effective"] == Q(91, 174),
            "second-face effective bound mismatch")
    require(second["D"] - got_second["effective"] == Q(23, 1218),
            "second-face strict cut mismatch")
    require(Q(20, 37) - got_second["effective"] == Q(113, 6438),
            "second-face margin below target mismatch")

    cases, checks = optimizer_grid_audit()
    mutations = mutation_suite(target, face)
    print("GROUP12A_C_NEWFACE_STANDALONE_PASS")
    print(f"descriptors=powered_a {DESCRIPTORS}")
    print(f"target C={got_target['C']} W={got_target['W']} R={got_target['R']} "
          f"P={got_target['P']} L={got_target['L']} S={got_target['S']} "
          f"arms={got_target['arms']} effective={got_target['effective']}")
    print(f"new_face D={face['D']} C={got_face['C']} W={got_face['W']} "
          f"R={got_face['R']} P={got_face['P']} L={got_face['L']} "
          f"S={got_face['S']} arms={got_face['arms']} "
          f"effective={got_face['effective']} "
          f"cut_margin={face['D'] - got_face['effective']}")
    print(f"second_face D={second['D']} C={got_second['C']} "
          f"W={got_second['W']} R={got_second['R']} P={got_second['P']} "
          f"L={got_second['L']} S={got_second['S']} "
          f"arms={got_second['arms']} effective={got_second['effective']} "
          f"cut_margin={second['D'] - got_second['effective']}")
    print(f"optimizer_cases={cases} or_checks={checks}")
    print(f"fail_closed_mutations={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
