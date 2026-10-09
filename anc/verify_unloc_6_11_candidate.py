#!/usr/bin/env python3
"""Exact canary for the existing UNLOC-k row at the 6/11 obstruction.

The formulas are reconstructed from docs/891 section 4 and
tmp/exceptions-D-40over77-direct-20260711/
GENERAL_FLOCK_UNLOCALIZED_HOSTILE_AUDIT.md section 6.  Only the Python
standard library is used.  This checks exponent algebra and descriptor
scope; it does not independently reprove ANHCS4 or the power sieve.
"""

from fractions import Fraction as F


SIDES = {"a": ("b", "c"), "b": ("a", "c")}
RNG = tuple(range(1, 7))


class ScopeError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise ScopeError(message)


def blank_profile():
    return {name: F(0) for name in (
        ["a", "b", "c"]
        + [f"{side}{i}" for side in "abc" for i in RNG]
        + [f"v{side}" for side in "abc"]
    )}


def profile_6_11():
    profile = blank_profile()
    profile.update({
        "a": F(3, 11), "a3": F(1, 11), "a4": F(2, 11),
        "b": F(5, 11), "b1": F(2, 11), "b3": F(3, 11),
        "c": F(3, 11), "c1": F(1, 11), "c5": F(2, 11),
    })
    return profile


def profile_20_37():
    profile = blank_profile()
    profile.update({
        "a": F(17, 37), "a1": F(7, 37), "a3": F(10, 37),
        "b": F(7, 37), "b1": F(2, 37), "vb": F(35, 37),
        "c": F(13, 37), "c1": F(5, 37), "c4": F(8, 37),
    })
    return profile


def tau(profile, side):
    return profile[side] - sum(profile[f"{side}{i}"] for i in RNG)


def validate_descriptor(sig, power, retained):
    require(sig in SIDES, "UNLOC quotient side must be addend a or b")
    require(power in range(2, 7), "UNLOC power must lie in [2,6]")
    require(type(retained) is tuple and 1 <= len(retained) <= 4,
            "UNLOC retains one to four represented exact blocks")
    require(len(set(retained)) == len(retained), "retained blocks repeat")
    represented = frozenset(
        f"{side}{i}" for side in SIDES[sig] for i in RNG)
    require(all(block in represented for block in retained),
            "retained block is not on a represented side")


def unloc(profile, sig, power, retained):
    """Return C,R,P,S,H,G for the sign-repaired universal UNLOC row."""
    validate_descriptor(sig, power, retained)
    other, cside = SIDES[sig]
    coefficient_cost = tau(profile, sig) + sum(
        profile[f"{sig}{i}"] for i in RNG if i % power)
    represented_cost = profile[other] + profile[cside]
    retained_mass = sum(profile[block] for block in retained)
    generic = coefficient_cost + represented_cost - retained_mass / 2
    sieve_max = max(generic, (generic + represented_cost) / 2)
    # The direct divisor-incidence/pair row D<=R is load-bearing.
    bound = min(represented_cost, sieve_max)
    equivalent = represented_cost - max(F(0), represented_cost - generic) / 2
    require(bound == equivalent, "UNLOC piecewise identity failed")
    return {
        "C": coefficient_cost,
        "R": represented_cost,
        "P": retained_mass,
        "S": generic,
        "H": sieve_max,
        "G": bound,
    }


def expect_scope_failure(function):
    try:
        function()
    except ScopeError:
        return
    raise AssertionError("invalid descriptor was accepted")


def main():
    p6 = profile_6_11()
    descriptor6 = ("b", 3, ("a3", "a4", "c1", "c5"))
    comp6 = unloc(p6, *descriptor6)
    expected6 = {
        "C": F(2, 11), "R": F(6, 11), "P": F(6, 11),
        "S": F(5, 11), "H": F(1, 2), "G": F(1, 2),
    }
    require(comp6 == expected6, f"6/11 ledger mismatch: {comp6}")
    require(F(6, 11) - comp6["G"] == F(1, 22),
            "6/11 UNLOC saving is not 1/22")

    # Even without retaining b's exact-seven core, the same existing row
    # strictly cuts the historical 20/37 witness.  A zero fourth block may
    # be omitted; using three retained blocks is legal.
    p20 = profile_20_37()
    descriptor20 = ("a", 3, ("b1", "c1", "c4"))
    comp20 = unloc(p20, *descriptor20)
    require(comp20 == {
        "C": F(7, 37), "R": F(20, 37), "P": F(15, 37),
        "S": F(39, 74), "H": F(79, 148), "G": F(79, 148),
    }, f"20/37 ledger mismatch: {comp20}")
    require(F(20, 37) - comp20["G"] == F(1, 148),
            "20/37 UNLOC saving is not 1/148")

    # The deliberately narrower family installed in the current exact tree
    # uses only powered side b.  It kills 6/11 but leaves the target witness
    # feasible, so the latter can still certify sharpness of that subsystem.
    descriptor20_b = ("b", 3, ("a1", "a3", "c1", "c4"))
    comp20_b = unloc(p20, *descriptor20_b)
    require(comp20_b == {
        "C": F(7, 37), "R": F(30, 37), "P": F(30, 37),
        "S": F(22, 37), "H": F(26, 37), "G": F(26, 37),
    }, f"20/37 powered-b ledger mismatch: {comp20_b}")
    require(F(20, 37) <= comp20_b["G"],
            "powered-b-only row spuriously cuts the target witness")

    expect_scope_failure(lambda: unloc(p6, "c", 3, ("a3",)))
    expect_scope_failure(lambda: unloc(p6, "b", 7, ("a3",)))
    expect_scope_failure(lambda: unloc(
        p6, "b", 3, ("a1", "a2", "a3", "a4", "a5")))
    expect_scope_failure(lambda: unloc(p6, "b", 3, ("b1", "a3")))
    expect_scope_failure(lambda: unloc(p6, "b", 3, ("a3", "a3")))

    print("UNLOC_6_11_EXACT_PASS")
    print(f"descriptor_6_11={descriptor6} components={comp6} saving=1/22")
    print(f"descriptor_20_37={descriptor20} components={comp20} saving=1/148")
    print(f"descriptor_20_37_powered_b={descriptor20_b} components={comp20_b}")
    print("scope_mutations=5 PASS")


if __name__ == "__main__":
    main()
