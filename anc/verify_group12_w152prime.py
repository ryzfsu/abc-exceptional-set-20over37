#!/usr/bin/env python3
"""Standalone exact audit of fixed GROUP12(a/b)-POW3(c) candidates.

The grouped factor is

    G(chi) = F_b1(chi) F_b2(chi**2).

Its fourth moment is diagonal-sized once the full Fourier modulus exponent
q = W + 2*theta satisfies q >= 2*(b1 + 2*b2).  Three further regular
blocks use the frozen smooth nonprincipal fourth moment.  This file uses
only the Python standard library and imports nothing from the search code.
"""

from fractions import Fraction


Q = Fraction
REGULAR = tuple(range(1, 7))
DESCRIPTORS = {
    "a": (("a1", "a2"), ("a4", "b1", "b4")),
    "b": (("b1", "b2"), ("a1", "a4", "b4")),
}


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def blank_profile():
    profile = {"D": Q(0), "a": Q(0), "b": Q(0), "c": Q(0)}
    profile.update({f"{side}{index}": Q(0)
                    for side in "abc" for index in REGULAR})
    profile.update({f"v{side}": Q(0) for side in "abc"})
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


def survivor_152prime_281():
    profile = blank_profile()
    profile.update({
        "D": Q(152, 281),
        "a": Q(493, 1405), "a1": Q(189, 1405),
        "a4": Q(304, 1405),
        "b": Q(477, 1405), "b1": Q(141, 1405),
        "b2": Q(40, 1405), "b4": Q(296, 1405),
        "c": Q(435, 1405), "c1": Q(5, 1405),
        "c2": Q(30, 1405), "c3": Q(390, 1405),
        "c4": Q(10, 1405),
    })
    return profile


def survivor_86_159():
    profile = blank_profile()
    profile.update({
        "D": Q(86, 159),
        "a": Q(271, 795), "a1": Q(83, 795),
        "a2": Q(20, 795), "a4": Q(168, 795),
        "b": Q(279, 795), "b1": Q(107, 795),
        "b4": Q(172, 795),
        "c": Q(245, 795), "c2": Q(20, 795),
        "c3": Q(220, 795), "c4": Q(5, 795),
    })
    return profile


def survivor_139_257():
    profile = blank_profile()
    profile.update({
        "D": Q(139, 257),
        "a": Q(439, 1285), "a1": Q(137, 1285),
        "a2": Q(30, 1285), "a4": Q(272, 1285),
        "b": Q(451, 1285), "b1": Q(173, 1285),
        "b4": Q(278, 1285),
        "c": Q(395, 1285), "c1": Q(10, 1285),
        "c3": Q(355, 1285), "vc": Q(210, 1285),
    })
    return profile


def slot_parts(slot):
    require(type(slot) is str and len(slot) == 2,
            "slot name is not a regular coordinate")
    require(slot[0] in "abc" and slot[1] in "123456",
            "slot name is not a regular coordinate")
    return slot[0], int(slot[1])


def canonical_coefficient(profile, powered_side, power):
    require(powered_side == "c" and power == 3,
            "this verifier authorizes only POW3(c)")
    regular_total = sum(
        (profile[f"{powered_side}{index}"] for index in REGULAR), Q(0))
    tail_cost = profile[powered_side] - regular_total
    require(tail_cost >= 0, "powered-side regular mass exceeds its radical")
    require(profile[f"v{powered_side}"] >= 7 * tail_cost,
            "powered-side tail value is below seven times its mass")
    coefficient_cost = tail_cost + sum(
        (profile[f"{powered_side}{index}"]
         for index in REGULAR if index % power != 0), Q(0))
    coefficient_value = profile[f"v{powered_side}"] + sum(
        ((index % power) * profile[f"{powered_side}{index}"]
         for index in REGULAR), Q(0))
    require(coefficient_value >= coefficient_cost,
            "canonical coefficient violates W >= C")
    return coefficient_cost, coefficient_value


def group12_arms(profile, group_side="b", powered_side="c", power=3,
                 group=None, q4=None):
    require(group_side in DESCRIPTORS,
            "group side must be one of the two authorized represented sides")
    expected_group, expected_q4 = DESCRIPTORS[group_side]
    if group is None:
        group = expected_group
    if q4 is None:
        q4 = expected_q4
    require(type(group) is tuple and group == expected_group,
            "group is not the typed same-side (index 1,index 2) pair")
    require(type(q4) is tuple and q4 == expected_q4,
            "fourth-moment blocks do not match the fixed typed triple")
    selected = group + q4
    require(len(set(selected)) == 5, "selected blocks are not distinct")
    for slot in selected:
        side, _ = slot_parts(slot)
        require(side != powered_side,
                "selected block lies on the powered side")

    # The grouped polynomial has argument x*y^2 of exponent L.  A fourth
    # moment compares products of two such arguments, hence the closed guard
    # W + 2*theta >= 2*L.  Equality is a bounded-shift face, not a failure.
    group_side_1, group_power_1 = slot_parts(group[0])
    group_side_2, group_power_2 = slot_parts(group[1])
    require(group_side_1 == group_side_2 == group_side
            and (group_power_1, group_power_2) == (1, 2),
            "grouped character powers are not (chi,chi^2) on one side")

    holder_budget = Q(1, 4) + 3 * Q(1, 4)
    require(holder_budget == 1, "Hölder weights do not close")

    coefficient_cost, coefficient_value = canonical_coefficient(
        profile, powered_side, power)
    represented_radical = profile["a"] + profile["b"]
    retained_mass = sum((profile[slot] for slot in selected), Q(0))
    group_argument = (profile[f"{group_side}1"]
                      + 2 * profile[f"{group_side}2"])
    child_s = (coefficient_cost + represented_radical
               - retained_mass / 2)

    threshold = group_argument - coefficient_value / 2
    nonnegative_threshold = max(Q(0), threshold)
    balance = (represented_radical - child_s) / 2
    theta_star = max(nonnegative_threshold, balance)
    modulus_at_star = coefficient_value + 2 * theta_star
    require(modulus_at_star >= 2 * group_argument,
            "optimized sieve scale violates the grouped-energy guard")

    arms = (
        child_s,
        (child_s + represented_radical) / 2,
        child_s + threshold,
    )
    theorem_bound = max(arms)
    optimized_directly = max(child_s + theta_star,
                             represented_radical - theta_star)
    require(theorem_bound == optimized_directly,
            "three-arm elimination does not match constrained optimization")

    return {
        "C": coefficient_cost,
        "W": coefficient_value,
        "R": represented_radical,
        "P": retained_mass,
        "L": group_argument,
        "S": child_s,
        "threshold": threshold,
        "balance": balance,
        "theta": theta_star,
        "q": modulus_at_star,
        "guard_slack": modulus_at_star - 2 * group_argument,
        "arms": arms,
        "theorem": theorem_bound,
        "direct_R": represented_radical,
        "effective": min(represented_radical, theorem_bound),
        "holder_budget": holder_budget,
    }


def ordinary_pow3c_top4(profile):
    coefficient_cost, _ = canonical_coefficient(profile, "c", 3)
    represented = profile["a"] + profile["b"]
    slots = tuple(f"{side}{index}" for side in "ab" for index in REGULAR)
    held = tuple(sorted(slots, key=lambda slot: profile[slot], reverse=True)[:4])
    retained = sum((profile[slot] for slot in held), Q(0))
    child_s = coefficient_cost + represented - retained / 2
    return held, child_s, max(child_s, (child_s + represented) / 2)


def optimizer_grid_audit():
    values = (Q(0), Q(1, 10), Q(1, 4), Q(1, 2), Q(4, 5))
    cases = 0
    or_checks = 0
    for child_s in values:
        for represented in values:
            for group_argument in values:
                for coefficient_value in values:
                    threshold = group_argument - coefficient_value / 2
                    lower = max(Q(0), threshold)
                    balance = (represented - child_s) / 2
                    theta = max(lower, balance)
                    direct = max(child_s + theta, represented - theta)
                    arms = (child_s, (child_s + represented) / 2,
                            child_s + threshold)
                    require(direct == max(arms),
                            "optimizer grid found an arm-direction mismatch")
                    for claimed_d in values:
                        require((claimed_d <= max(arms))
                                == any(claimed_d <= arm for arm in arms),
                                "finite OR is not equivalent to max-of-arms")
                        or_checks += 1
                    cases += 1
    return cases, or_checks


def expect_failure(name, function):
    try:
        function()
    except AuditError:
        return name
    raise AuditError(f"mutation {name!r} was accepted")


def mutation_suite(target, survivor):
    passed = []
    passed.append(expect_failure(
        "duplicate-group-slot",
        lambda: group12_arms(target, group=("b1", "b1"))))
    passed.append(expect_failure(
        "cross-side-group",
        lambda: group12_arms(target, group=("a1", "b2"))))
    passed.append(expect_failure(
        "wrong-q4-block",
        lambda: group12_arms(target, q4=("a1", "a4", "b3"))))
    passed.append(expect_failure(
        "powered-side-q4-block",
        lambda: group12_arms(target, q4=("a1", "a4", "c4"))))
    passed.append(expect_failure(
        "wrong-powered-family",
        lambda: group12_arms(target, powered_side="a")))
    passed.append(expect_failure(
        "unknown-group-side",
        lambda: group12_arms(target, group_side="c")))
    passed.append(expect_failure(
        "descriptor-side-mismatch",
        lambda: group12_arms(target, group_side="a",
                             group=("b1", "b2"))))

    # A reversed sign or a missing factor two in q >= 2L can understate the
    # bound when the grouped-product guard, rather than balance, is active.
    child_s, represented = Q(1, 10), Q(1, 2)
    group_argument, coefficient_value = Q(4, 5), Q(1, 5)
    correct = max(child_s, (child_s + represented) / 2,
                  child_s + group_argument - coefficient_value / 2)
    reversed_sign = max(child_s, (child_s + represented) / 2,
                        child_s - group_argument + coefficient_value / 2)
    missing_two = max(child_s, (child_s + represented) / 2,
                      child_s + (group_argument - coefficient_value) / 2)
    passed.append(expect_failure(
        "reversed-guard-sign",
        lambda: require(reversed_sign == correct,
                        "reversing the guard sign changes the theorem")))
    passed.append(expect_failure(
        "missing-factor-two",
        lambda: require(missing_two == correct,
                        "dropping the factor two changes the theorem")))

    mutated = dict(survivor)
    mutated["c"] += Q(1, 1405)
    passed.append(expect_failure(
        "unresolved-powered-mass",
        lambda: group12_arms(mutated)))
    require(len(passed) == 10, "mutation count mismatch")
    return passed


def main():
    survivor_b = survivor_152prime_281()
    survivor_a = survivor_86_159()
    survivor_139 = survivor_139_257()
    target = target_profile()
    got_b = group12_arms(survivor_b, group_side="b")
    got_a = group12_arms(survivor_a, group_side="a")
    prior_b_at_a = group12_arms(survivor_a, group_side="b")
    got_139 = group12_arms(survivor_139, group_side="a")
    target_b = group12_arms(target, group_side="b")
    target_a = group12_arms(target, group_side="a")

    require(got_b["C"] == Q(45, 1405), "W152' C mismatch")
    require(got_b["W"] == Q(75, 1405), "W152' W mismatch")
    require(got_b["R"] == got_b["P"] == Q(970, 1405),
            "W152' represented/retained mass mismatch")
    require(got_b["L"] == Q(221, 1405), "W152' group argument mismatch")
    require(got_b["S"] == Q(530, 1405), "W152' S mismatch")
    require(got_b["threshold"] == Q(367, 2810),
            "W152' grouped-energy threshold mismatch")
    require(got_b["balance"] == Q(220, 1405),
            "W152' balancing scale mismatch")
    require(got_b["theta"] == got_b["balance"],
            "W152' guard unexpectedly binds")
    require(got_b["q"] == Q(515, 1405)
            and got_b["guard_slack"] == Q(73, 1405),
            "W152' Fourier modulus ledger mismatch")
    require(got_b["arms"] == (Q(530, 1405), Q(750, 1405),
                              Q(1427, 2810)),
            "W152' three arms mismatch")
    require(got_b["theorem"] == got_b["effective"] == Q(150, 281),
            "W152' optimized bound mismatch")
    require(survivor_b["D"] - got_b["effective"] == Q(2, 281),
            "W152' strict-cut margin mismatch")
    require(Q(20, 37) - got_b["effective"] == Q(70, 10397),
            "W152' margin below 20/37 mismatch")

    # The equality face q=2L is closed by the bounded-shift product count.
    theta_equality = got_b["threshold"]
    require(got_b["W"] + 2 * theta_equality == 2 * got_b["L"],
            "grouped-energy equality face is not reconstructed")

    require(got_a["C"] == Q(25, 795), "W86 C mismatch")
    require(got_a["W"] == Q(45, 795), "W86 W mismatch")
    require(got_a["R"] == got_a["P"] == Q(550, 795),
            "W86 represented/retained mass mismatch")
    require(got_a["L"] == Q(123, 795), "W86 group argument mismatch")
    require(got_a["S"] == Q(300, 795), "W86 S mismatch")
    require(got_a["threshold"] == Q(201, 1590)
            and got_a["balance"] == Q(125, 795),
            "W86 scale ledger mismatch")
    require(got_a["theta"] == got_a["balance"],
            "W86 guard unexpectedly binds")
    require(got_a["q"] == Q(295, 795)
            and got_a["guard_slack"] == Q(49, 795),
            "W86 Fourier modulus ledger mismatch")
    require(got_a["arms"] == (Q(300, 795), Q(425, 795),
                              Q(801, 1590)),
            "W86 GROUP12(a) arms mismatch")
    require(got_a["effective"] == Q(85, 159)
            and survivor_a["D"] - got_a["effective"] == Q(1, 159),
            "W86 GROUP12(a) cut mismatch")
    require(Q(20, 37) - got_a["effective"] == Q(35, 5883),
            "W86 margin below 20/37 mismatch")
    require(prior_b_at_a["theorem"] == survivor_a["D"],
            "W86 is not tight on the preceding GROUP12(b) average arm")

    require(got_139["C"] == Q(40, 1285)
            and got_139["W"] == Q(220, 1285),
            "W139 tail-aware coefficient ledger mismatch")
    require(got_139["R"] == got_139["P"] == Q(890, 1285),
            "W139 represented/retained mass mismatch")
    require(got_139["L"] == Q(197, 1285)
            and got_139["S"] == Q(485, 1285),
            "W139 group/S ledger mismatch")
    require(got_139["threshold"] == Q(87, 1285)
            and got_139["balance"] == Q(405, 2570),
            "W139 scale ledger mismatch")
    require(got_139["theta"] == got_139["balance"]
            and got_139["q"] == Q(625, 1285)
            and got_139["guard_slack"] == Q(231, 1285),
            "W139 grouped-energy guard mismatch")
    require(got_139["arms"] == (Q(485, 1285), Q(275, 514),
                                Q(572, 1285)),
            "W139 GROUP12(a) arms mismatch")
    require(got_139["effective"] == Q(275, 514)
            and survivor_139["D"] - got_139["effective"] == Q(3, 514),
            "W139 GROUP12(a) cut mismatch")
    require(Q(20, 37) - got_139["effective"] == Q(105, 19018),
            "W139 margin below 20/37 mismatch")
    pow3_held, _, pow3_bound = ordinary_pow3c_top4(survivor_139)
    require(set(pow3_held) == {"a1", "a4", "b1", "b4"}
            and pow3_bound == survivor_139["D"],
            "W139 ordinary POW3(c) top-four average is not tight")

    for label, target_got, expected_l, expected_third in (
            ("b", target_b, Q(2, 37), Q(28, 37)),
            ("a", target_a, Q(7, 37), Q(33, 37))):
        require(target_got["C"] == target_got["W"] == Q(13, 37),
                f"target GROUP12({label}) coefficient ledger mismatch")
        require(target_got["R"] == Q(24, 37)
                and target_got["P"] == Q(9, 37)
                and target_got["L"] == expected_l,
                f"target GROUP12({label}) represented/group ledger mismatch")
        require(target_got["S"] == Q(65, 74),
                f"target GROUP12({label}) S mismatch")
        require(target_got["arms"]
                == (Q(65, 74), Q(113, 148), expected_third),
                f"target GROUP12({label}) arms mismatch")
        require(target_got["effective"] == Q(24, 37),
                f"target GROUP12({label}) direct-R safety mismatch")
        require(target["D"] < target_got["effective"],
                f"GROUP12({label}) cuts the protected target")
    require(target_a["q"] == 2 * target_a["L"]
            and target_a["guard_slack"] == 0,
            "target GROUP12(a) equality face is not closed exactly")

    grid_cases, or_checks = optimizer_grid_audit()
    mutations = mutation_suite(target, survivor_b)

    print("GROUP12_AB_PROFILES_STANDALONE_PASS")
    for side in ("b", "a"):
        print(f"descriptor_GROUP12{side}=group{DESCRIPTORS[side][0]} "
              f"q4{DESCRIPTORS[side][1]}")
    print(f"W152prime_b C={got_b['C']} W={got_b['W']} R={got_b['R']} "
          f"P={got_b['P']} L={got_b['L']} S={got_b['S']} "
          f"arms={got_b['arms']} effective={got_b['effective']} "
          f"cut_margin={survivor_b['D'] - got_b['effective']}")
    print(f"W86_a C={got_a['C']} W={got_a['W']} R={got_a['R']} "
          f"P={got_a['P']} L={got_a['L']} S={got_a['S']} "
          f"arms={got_a['arms']} effective={got_a['effective']} "
          f"cut_margin={survivor_a['D'] - got_a['effective']}")
    print(f"W86_prior_b_tight={prior_b_at_a['theorem']}")
    print(f"W139_a C={got_139['C']} W={got_139['W']} R={got_139['R']} "
          f"P={got_139['P']} L={got_139['L']} S={got_139['S']} "
          f"arms={got_139['arms']} effective={got_139['effective']} "
          f"cut_margin={survivor_139['D'] - got_139['effective']} "
          f"ordinary_POW3c_tight={pow3_bound}")
    print(f"target_b arms={target_b['arms']} theorem={target_b['theorem']} "
          f"effective={target_b['effective']}")
    print(f"target_a arms={target_a['arms']} theorem={target_a['theorem']} "
          f"effective={target_a['effective']} guard_slack={target_a['guard_slack']}")
    print(f"holder_budget={got_b['holder_budget']} optimizer_cases={grid_cases} "
          f"or_checks={or_checks}")
    print(f"fail_closed_mutations={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
