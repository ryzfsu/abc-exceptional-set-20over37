#!/usr/bin/env python3
"""Standalone exact audit of all 28 powered-b double-GROUP12 clauses."""

import itertools
from fractions import Fraction


Q = Fraction
RNG = tuple(range(1, 7))
POOL = tuple(f"a{i}" for i in range(3, 7)) + tuple(
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
    p.update({
        "D": Q(20, 37), "a": Q(17, 37), "a1": Q(7, 37),
        "a3": Q(10, 37), "b": Q(7, 37), "b1": Q(2, 37),
        "vb": Q(35, 37), "c": Q(13, 37), "c1": Q(5, 37),
        "c4": Q(8, 37),
    })
    return p


def reflected_face_46_85():
    p = blank()
    p.update({
        "D": Q(46, 85),
        "a": Q(141, 425), "a1": Q(33, 425), "a2": Q(4, 85),
        "a4": Q(88, 425),
        "b": Q(27, 85), "b1": Q(3, 85), "b3": Q(24, 85),
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
    regular_b = sum((p[f"b{i}"] for i in RNG), Q(0))
    tail_b = p["b"] - regular_b
    require(tail_b >= 0 and p["vb"] >= 7 * tail_b,
            "powered-side tail ledger failed")
    C = p["b"] - p["b3"] - p["b6"]
    W = p["vb"] + p["b1"] + 2*p["b2"] + p["b4"] + 2*p["b5"]
    R = p["a"] + p["c"]
    retained = ("a1", "a2", "c1", "c2") + singletons
    P = sum((p[z] for z in retained), Q(0))
    La = p["a1"] + 2*p["a2"]
    Lc = p["c1"] + 2*p["c2"]
    S = C + R - P/2
    theta = max(Q(0), (R-S)/2, La-W/2, Lc-W/2)
    modulus = W + 2*theta
    require(modulus >= 2*La and modulus >= 2*Lc,
            "one of the two grouped fourth-moment guards failed")
    arms = (S, (S+R)/2, S+La-W/2, S+Lc-W/2)
    require(max(arms) == max(S+theta, R-theta),
            "four-arm elimination disagrees with direct optimization")
    return {"C": C, "W": W, "R": R, "P": P, "La": La, "Lc": Lc,
            "S": S, "theta": theta, "modulus": modulus, "arms": arms,
            "bound": max(arms), "effective": min(R, max(arms))}


def optimizer_grid():
    values = (Q(0), Q(1, 10), Q(1, 4), Q(1, 2), Q(4, 5))
    cases = checks = 0
    for S in values:
        for R in values:
            for La in values:
                for Lc in values:
                    for W in values:
                        theta = max(Q(0), (R-S)/2, La-W/2, Lc-W/2)
                        direct = max(S+theta, R-theta)
                        arms = (S, (S+R)/2, S+La-W/2, S+Lc-W/2)
                        require(direct == max(arms), "optimizer grid mismatch")
                        for D in values:
                            require((D <= max(arms))
                                    == any(D <= arm for arm in arms),
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


def main():
    protected = target()
    target_records = []
    for combo in itertools.combinations(POOL, 2):
        singletons = tuple(sorted(combo, key=lambda z: (z[0], z[1])))
        got = evaluate(protected, singletons)
        require(protected["D"] <= got["bound"],
                f"descriptor {singletons} cuts the target")
        target_records.append((got["bound"], singletons))
    require(len(target_records) == 28, "descriptor count mismatch")
    require(min(target_records) == (Q(26, 37), ("a3", "c4")),
            f"unexpected target minimum: {min(target_records)}")

    face = reflected_face_46_85()
    got = evaluate(face, ("a4", "c4"))
    require((got["C"], got["W"], got["R"], got["P"],
             got["La"], got["Lc"], got["S"])
            == (Q(3, 85), Q(3, 85), Q(58, 85), Q(58, 85),
                Q(73, 425), Q(57, 425), Q(32, 85)),
            "reflected 46/85 face ledger mismatch")
    require(got["arms"]
            == (Q(32, 85), Q(9, 17), Q(451, 850), Q(419, 850)),
            "reflected 46/85 face arms mismatch")
    require(face["D"] - got["bound"] == Q(9, 850),
            "reflected 46/85 face cut mismatch")

    mutations = [
        expect_failure("duplicate-singleton",
                       lambda: evaluate(protected, ("a4", "a4"))),
        expect_failure("outside-pool",
                       lambda: evaluate(protected, ("a2", "c4"))),
        expect_failure("noncanonical",
                       lambda: evaluate(protected, ("c4", "a4"))),
    ]
    cases, checks = optimizer_grid()
    print("GROUP1212B_REFLECTEDFACE_STANDALONE_PASS")
    print(f"target_descriptors={len(target_records)} minimum={min(target_records)}")
    print(f"reflected_face_46over85={got} saving={face['D']-got['bound']}")
    print(f"optimizer_cases={cases} or_checks={checks}")
    print(f"fail_closed_mutations={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (AuditError, ValueError, ZeroDivisionError,
            KeyError, TypeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
