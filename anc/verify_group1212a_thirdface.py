#!/usr/bin/env python3
"""Standalone exact audit of all 28 powered-a double-GROUP12 clauses."""

import itertools
from fractions import Fraction


Q = Fraction
RNG = tuple(range(1, 7))
POOL = tuple(f"b{i}" for i in range(3, 7)) + tuple(
    f"c{i}" for i in range(3, 7))


class AuditError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def blank():
    p = {"D": Q(0), "a": Q(0), "b": Q(0), "c": Q(0)}
    p.update({f"{s}{i}": Q(0) for s in "abc" for i in RNG})
    p.update({f"v{s}": Q(0) for s in "abc"})
    return p


def target():
    p = blank()
    p.update({"D": Q(20, 37), "a": Q(17, 37), "a1": Q(7, 37),
              "a3": Q(10, 37), "b": Q(7, 37), "b1": Q(2, 37),
              "c": Q(13, 37), "c1": Q(5, 37), "c4": Q(8, 37)})
    return p


def face_110_203():
    p = blank()
    p.update({
        "D": Q(110, 203),
        "a": Q(229, 609), "a1": Q(2, 87), "a2": Q(50, 609),
        "a3": Q(55, 203),
        "b": Q(167, 609), "b1": Q(52, 609), "b2": Q(2, 203),
        "b5": Q(109, 609),
        "c": Q(71, 203), "c1": Q(27, 203), "c4": Q(44, 203),
    })
    return p


def face_46_85():
    p = blank()
    p.update({
        "D": Q(46, 85), "a": Q(27, 85), "a1": Q(3, 85),
        "a3": Q(24, 85),
        "b": Q(141, 425), "b1": Q(33, 425), "b2": Q(4, 85),
        "b4": Q(88, 425),
        "c": Q(149, 425), "c1": Q(57, 425), "c4": Q(92, 425),
    })
    return p


def canonical(singletons):
    require(type(singletons) is tuple and len(singletons) == 2,
            "two singleton slots are required")
    require(len(set(singletons)) == 2 and set(singletons) <= set(POOL),
            "singleton set is invalid")
    expected = tuple(sorted(singletons, key=lambda z: (z[0], z[1])))
    require(singletons == expected, "singleton tuple is not canonical")
    return singletons


def evaluate(p, singletons):
    singletons = canonical(singletons)
    regular_a = sum((p[f"a{i}"] for i in RNG), Q(0))
    tail_a = p["a"] - regular_a
    require(tail_a >= 0 and p["va"] >= 7 * tail_a,
            "powered-side tail ledger failed")
    C = p["a"] - p["a3"] - p["a6"]
    W = p["va"] + p["a1"] + 2*p["a2"] + p["a4"] + 2*p["a5"]
    R = p["b"] + p["c"]
    retained = ("b1", "b2", "c1", "c2") + singletons
    P = sum((p[z] for z in retained), Q(0))
    Lb = p["b1"] + 2*p["b2"]
    Lc = p["c1"] + 2*p["c2"]
    S = C + R - P/2
    theta = max(Q(0), (R-S)/2, Lb-W/2, Lc-W/2)
    q = W + 2*theta
    require(q >= 2*Lb and q >= 2*Lc,
            "one of the two grouped fourth-moment guards failed")
    arms = (S, (S+R)/2, S+Lb-W/2, S+Lc-W/2)
    require(max(arms) == max(S+theta, R-theta),
            "four-arm elimination disagrees with direct optimization")
    return {"C": C, "W": W, "R": R, "P": P, "Lb": Lb, "Lc": Lc,
            "S": S, "theta": theta, "q": q, "arms": arms,
            "bound": max(arms), "effective": min(R, max(arms))}


def optimizer_grid():
    vals = (Q(0), Q(1, 10), Q(1, 4), Q(1, 2), Q(4, 5))
    cases = 0
    checks = 0
    for S in vals:
        for R in vals:
            for Lb in vals:
                for Lc in vals:
                    for W in vals:
                        theta = max(Q(0), (R-S)/2, Lb-W/2, Lc-W/2)
                        direct = max(S+theta, R-theta)
                        arms = (S, (S+R)/2, S+Lb-W/2, S+Lc-W/2)
                        require(direct == max(arms), "optimizer grid mismatch")
                        for D in vals:
                            require((D <= max(arms))
                                    == any(D <= arm for arm in arms),
                                    "OR/max equivalence failed")
                            checks += 1
                        cases += 1
    return cases, checks


def expect_failure(name, fn):
    try:
        fn()
    except AuditError:
        return name
    raise AuditError(f"mutation {name!r} was accepted")


def main():
    t = target()
    target_records = []
    for combo in itertools.combinations(POOL, 2):
        singletons = tuple(sorted(combo, key=lambda z: (z[0], z[1])))
        got = evaluate(t, singletons)
        require(t["D"] <= got["bound"],
                f"descriptor {singletons} cuts the target")
        target_records.append((got["bound"], singletons))
    require(len(target_records) == 28, "descriptor count mismatch")

    f2 = face_110_203()
    got2 = evaluate(f2, ("b5", "c4"))
    require((got2["C"], got2["W"], got2["R"], got2["P"],
             got2["Lb"], got2["Lc"], got2["S"])
            == (Q(64, 609), Q(38, 203), Q(380, 609), Q(380, 609),
                Q(64, 609), Q(27, 203), Q(254, 609)),
            "110/203 face ledger mismatch")
    require(got2["arms"]
            == (Q(254, 609), Q(317, 609), Q(87, 203), Q(278, 609)),
            "110/203 face arms mismatch")
    require(f2["D"] - got2["bound"] == Q(13, 609),
            "110/203 face cut mismatch")

    f3 = face_46_85()
    got3 = evaluate(f3, ("b4", "c4"))
    require((got3["C"], got3["W"], got3["R"], got3["P"],
             got3["Lb"], got3["Lc"], got3["S"])
            == (Q(3, 85), Q(3, 85), Q(58, 85), Q(58, 85),
                Q(73, 425), Q(57, 425), Q(32, 85)),
            "46/85 face ledger mismatch")
    require(got3["arms"]
            == (Q(32, 85), Q(9, 17), Q(451, 850), Q(419, 850)),
            "46/85 face arms mismatch")
    require(f3["D"] - got3["bound"] == Q(9, 850),
            "46/85 face cut mismatch")

    mutations = [
        expect_failure("duplicate-singleton", lambda: evaluate(t, ("b4", "b4"))),
        expect_failure("outside-pool", lambda: evaluate(t, ("b2", "c4"))),
        expect_failure("noncanonical", lambda: evaluate(t, ("c4", "b4"))),
    ]
    cases, checks = optimizer_grid()
    print("GROUP1212A_THIRDFACE_STANDALONE_PASS")
    print(f"target_descriptors={len(target_records)} minimum={min(target_records)}")
    print(f"face_110over203={got2} saving={f2['D']-got2['bound']}")
    print(f"face_46over85={got3} saving={f3['D']-got3['bound']}")
    print(f"optimizer_cases={cases} or_checks={checks}")
    print(f"fail_closed_mutations={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError, KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
