#!/usr/bin/env python3
"""Pure-Fraction audit of the frozen top archimedean cover.

For a nonempty positive box A+B=C, write V_s for the logarithmic size of
the full side monomial.  In scale-free form the limiting necessity is

    V_a <= V_c,  V_b <= V_c,
    (V_c <= V_a) OR (V_c <= V_b).

After normalizing the local c-box to top scale, this is the production root

    V_a = V_c = 1  OR  V_b = V_c = 1.

No project or search-generator module is imported.
"""

from fractions import Fraction


Q = Fraction
RNG = tuple(range(1, 7))


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def blank():
    p = {"D": Q(0), "a": Q(0), "b": Q(0), "c": Q(0),
         "va": Q(0), "vb": Q(0), "vc": Q(0)}
    p.update({f"{s}{i}": Q(0) for s in "abc" for i in RNG})
    return p


def profile(**entries):
    p = blank()
    p.update(entries)
    return p


def profiles():
    return {
        "W20": profile(
            D=Q(20, 37), a=Q(17, 37), a1=Q(7, 37), a3=Q(10, 37),
            b=Q(7, 37), b1=Q(2, 37), vb=Q(35, 37),
            c=Q(13, 37), c1=Q(5, 37), c4=Q(8, 37)),
        "W6": profile(
            D=Q(6, 11), a=Q(3, 11), a3=Q(1, 11), a4=Q(2, 11),
            b=Q(5, 11), b1=Q(2, 11), b3=Q(3, 11),
            c=Q(3, 11), c1=Q(1, 11), c5=Q(2, 11)),
        "W46": profile(
            D=Q(46, 85), a=Q(141, 425), a1=Q(33, 425),
            a2=Q(20, 425), a4=Q(88, 425),
            b=Q(149, 425), b1=Q(57, 425), b4=Q(92, 425),
            c=Q(135, 425), c1=Q(15, 425), c3=Q(120, 425)),
        "W79": profile(
            D=Q(79, 139), a=Q(73, 278), a1=Q(5, 278),
            a4=Q(67, 278), a5=Q(1, 278),
            b=Q(92, 278), b3=Q(91, 278), b5=Q(1, 278),
            c=Q(113, 278), c1=Q(112, 278), vc=Q(7, 278)),
        "W152": profile(
            D=Q(152, 281), a=Q(481, 1405), a1=Q(153, 1405),
            a2=Q(30, 1405), a4=Q(298, 1405),
            b=Q(489, 1405), b1=Q(177, 1405),
            b2=Q(10, 1405), b4=Q(302, 1405),
            c=Q(435, 1405), c1=Q(5, 1405), c2=Q(30, 1405),
            c3=Q(390, 1405), c4=Q(10, 1405)),
        "W152prime": profile(
            D=Q(152, 281), a=Q(493, 1405), a1=Q(189, 1405),
            a4=Q(304, 1405), b=Q(477, 1405), b1=Q(141, 1405),
            b2=Q(40, 1405), b4=Q(296, 1405),
            c=Q(435, 1405), c1=Q(5, 1405), c2=Q(30, 1405),
            c3=Q(390, 1405), c4=Q(10, 1405)),
        "W86": profile(
            D=Q(86, 159), a=Q(271, 795), a1=Q(83, 795),
            a2=Q(20, 795), a4=Q(168, 795),
            b=Q(279, 795), b1=Q(107, 795), b4=Q(172, 795),
            c=Q(245, 795), c2=Q(20, 795), c3=Q(220, 795),
            c4=Q(5, 795)),
        "W139": profile(
            D=Q(139, 257), a=Q(439, 1285), a1=Q(137, 1285),
            a2=Q(30, 1285), a4=Q(272, 1285),
            b=Q(451, 1285), b1=Q(173, 1285), b4=Q(278, 1285),
            c=Q(395, 1285), c1=Q(10, 1285), c3=Q(355, 1285),
            vc=Q(210, 1285)),
        "W13": profile(
            D=Q(13, 24), a=Q(1, 4), a4=Q(1, 4),
            b=Q(3, 8), b1=Q(3, 32), b2=Q(1, 24),
            b3=Q(11, 48), b5=Q(1, 96),
            c=Q(3, 8), c1=Q(3, 32), c2=Q(1, 24),
            c3=Q(11, 48), c5=Q(1, 96)),
    }


def side_value(p, side):
    return (sum((i * p[f"{side}{i}"] for i in RNG), Q(0))
            + p[f"v{side}"])


def arch_status(p):
    va, vb, vc = (side_value(p, side) for side in "abc")
    addends_below_result = va <= vc and vb <= vc
    result_below_one_addend = vc <= va or vc <= vb
    scale_free = addends_below_result and result_below_one_addend

    # Production labels use the *localized/small* side.  local_sig=a means
    # the other addend b is large; local_sig=b means addend a is large.
    branch0_local_a = vb == vc == 1
    branch1_local_b = va == vc == 1
    production = branch0_local_a or branch1_local_b
    return {
        "values": (va, vb, vc),
        "a_le_c": va <= vc,
        "b_le_c": vb <= vc,
        "root_or": result_below_one_addend,
        "scale_free": scale_free,
        "production": production,
        "branches": tuple(i for i, hit in enumerate(
            (branch0_local_a, branch1_local_b)) if hit),
        "a_gap": max(Q(0), va - vc),
        "b_gap": max(Q(0), vb - vc),
    }


def normalized_equivalence_audit():
    grid = tuple(Q(i, 12) for i in range(13))
    checks = 0
    for va in grid:
        for vb in grid:
            vc = Q(1)
            scale_free = (va <= vc and vb <= vc
                          and (vc <= va or vc <= vb))
            production = (va == vc or vb == vc)
            require(scale_free == production,
                    "normalized production root is not the scale-free cover")
            checks += 1
    return checks


def main():
    ps = profiles()
    statuses = {name: arch_status(p) for name, p in ps.items()}

    expected_values = {
        "W20": (Q(1), Q(1), Q(1)),
        "W6": (Q(1), Q(1), Q(1)),
        "W46": (Q(1), Q(1), Q(15, 17)),
        "W79": (Q(1), Q(1), Q(119, 278)),
        "W152": (Q(1), Q(1), Q(255, 281)),
        "W152prime": (Q(1), Q(1), Q(255, 281)),
        "W86": (Q(1), Q(1), Q(48, 53)),
        "W139": (Q(1), Q(1), Q(1)),
        "W13": (Q(1), Q(11, 12), Q(11, 12)),
    }
    for name, expected in expected_values.items():
        require(statuses[name]["values"] == expected,
                f"{name} side-value reconstruction mismatch")
        require(sum((ps[name][side] for side in "abc"), Q(0)) == 1,
                f"{name} radical scale is not one")

    for name in ("W20", "W6", "W139"):
        require(statuses[name]["scale_free"]
                and statuses[name]["production"],
                f"{name} is missing from the frozen arch cover")
        require(statuses[name]["branches"] == (0, 1),
                f"{name} should lie on both equality branches")
    require(ps["W139"]["c"]
            - sum((ps["W139"][f"c{i}"] for i in RNG), Q(0))
            == Q(30, 1285)
            and ps["W139"]["vc"] == Q(210, 1285),
            "W139 exact-seven tail ledger mismatch")

    # These are genuine LP witnesses for the arch-omitted experimental tree,
    # but not profiles of a nonempty positive A+B=C box.
    for name in ("W46", "W79", "W152", "W152prime", "W86"):
        require(not statuses[name]["scale_free"]
                and not statuses[name]["production"],
                f"{name} unexpectedly satisfies the source arch cover")
        require(statuses[name]["a_gap"] > 0
                and statuses[name]["b_gap"] > 0,
                f"{name} should have two oversized addends")

    w13 = statuses["W13"]
    require(statuses["W79"]["a_gap"] == Q(159, 278)
            and statuses["W79"]["b_gap"] == Q(159, 278),
            "W79 ARCH-order gaps mismatch")
    require(not w13["a_le_c"] and w13["b_le_c"] and w13["root_or"],
            "W13 should fail only the universal V_a<=V_c direction")
    require(w13["a_gap"] == Q(1, 12), "W13 arch gap mismatch")

    checks = normalized_equivalence_audit()
    print("ARCH_FACES_STANDALONE_PASS")
    for name in ps:
        st = statuses[name]
        print(f"{name} values={st['values']} scale_free={st['scale_free']} "
              f"production={st['production']} branches={st['branches']} "
              f"a_gap={st['a_gap']} b_gap={st['b_gap']}")
    print(f"normalized_equivalence_checks={checks}")
    print("branch0=local_sig_a=>Vb=Vc=1")
    print("branch1=local_sig_b=>Va=Vc=1")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
