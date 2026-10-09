#!/usr/bin/env python3
"""Independent exact verifier for the 20/37 disjunctive proof tree.

This verifier deliberately uses only the Python standard library.  In
particular, it does not import the search program, scan_lib, NumPy, SciPy,
or an LP solver.  Every accepted row is reconstructed below from its
mathematical formula with fractions.Fraction arithmetic.

Accepted dynamic families are exactly:

  * PS23 for a nonempty selected mask T subset {1,...,6,tail};
  * regular-block CS4 with four distinct held regular roots;
  * global unlocalized POW3 rows with four distinct retained regular roots:
    every b- and c-powered descriptor, and the exact target-safe a-powered
    subset;
  * the homogeneous ARCH value cover, two fixed GROUP12(c) clauses, all 120
    target-safe GROUP12(a,c;three-singleton) clauses, and all 28 target-safe
    double-group GROUP1212(a;two-singleton) clauses;
  * Proposition 5.1 UN with regular free masks R_1,R_2 subset {1,...,6},
    not both empty, and a nonempty modulus mask T which may contain tail.

All other labels and all free-tail UN labels are rejected fail-closed.
"""

import argparse
import json
import math
import re
from fractions import Fraction


Q = Fraction
TARGET = Q(20, 37)
RNG = tuple(range(1, 7))
SIDES = {"a": ("b", "c"), "b": ("a", "c"), "c": ("a", "b")}
VARS = tuple(
    ["D", "a", "b", "c"]
    + [f"{s}{i}" for s in "abc" for i in RNG]
    + [f"v{s}" for s in "abc"]
    + [f"m{s}" for s in "abc"]
)
VAR_SET = frozenset(VARS)
ZERO = {v: Q(0) for v in VARS}
EXPECTED_SYSTEM = (
    "base+ARCH-value-cover+HB3+13geom+DET+Spacing+allPS23+CS4regular"
    "+POW3abc-regular(a-target-safe)"
    "+GROUP12c(a/b)+GROUP12ab(c;all3)+GROUP1212ab(all2) grouped rows"
    "+extended-UN(regular-free)"
)

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


class VerificationError(Exception):
    pass


def fail(message):
    raise VerificationError(message)


def require(condition, message):
    if not condition:
        fail(message)


_Q_RE = re.compile(r"(?:0|-?[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
_UINT_RE = re.compile(r"(?:0|[1-9][0-9]*)\Z")
_SLOT_RE = re.compile(r"[abc][1-6]\Z")


def parse_q(value, context):
    require(type(value) is str, f"{context}: rational must be a string")
    require(_Q_RE.fullmatch(value) is not None,
            f"{context}: noncanonical rational {value!r}")
    out = Q(value)
    require(str(out) == value, f"{context}: rational is not reduced: {value!r}")
    return out


def parse_uint(value, context):
    require(type(value) is str and _UINT_RE.fullmatch(value) is not None,
            f"{context}: invalid unsigned integer {value!r}")
    return int(value)


def add_expr(*scaled_exprs):
    """Return sum(scale * expr) with exact coefficients and zeros removed."""
    out = {}
    for expr, scale in scaled_exprs:
        scale = Q(scale)
        for variable, coefficient in expr.items():
            require(variable in VAR_SET, f"unknown variable in formula: {variable}")
            out[variable] = out.get(variable, Q(0)) + scale * Q(coefficient)
    return {v: c for v, c in out.items() if c}


def make_row(coeff, rhs=0, label=""):
    require(type(label) is str and label, "row has an empty/non-string label")
    clean = {}
    for variable, coefficient in coeff.items():
        require(variable in VAR_SET, f"{label}: unknown variable {variable!r}")
        coefficient = Q(coefficient)
        if coefficient:
            clean[variable] = coefficient
    return clean, Q(rhs), label


def upper_arm(bound_expr, label):
    """Encode D <= bound_expr as a homogeneous row coeff*x <= 0."""
    return make_row(add_expr(({"D": 1}, 1), (bound_expr, -1)), 0, label)


def value_expr(side):
    return {**{f"{side}{i}": Q(i) for i in RNG}, f"v{side}": Q(1)}


def p(index):
    return {f"{side}{index}": Q(1) for side in "abc"}


def mask_elements(mask):
    require(type(mask) is int and not isinstance(mask, bool), "mask is not an int")
    require(0 <= mask < 128, f"mask outside [0,127]: {mask}")
    return tuple(i for i in RNG if mask & (1 << (i - 1)))


def selected_root_value(side, mask):
    """Return (root enumeration cost, value mass) for a 7-bit T mask."""
    regular = mask_elements(mask)
    cost = {f"{side}{i}": Q(1) for i in regular}
    value = {f"{side}{i}": Q(i) for i in regular}
    if mask & 64:
        # tau_side = side - sum_{i<=6} side_i; tail value = v_side.
        cost = add_expr((cost, 1), ({side: 1}, 1),
                        ({f"{side}{i}": 1 for i in RNG}, -1))
        value = add_expr((value, 1), ({f"v{side}": 1}, 1))
    return cost, value


def free_gcd(m1, m2):
    exponents = mask_elements(m1) + mask_elements(m2)
    q = 0
    for exponent in exponents:
        q = math.gcd(q, exponent)
    require(q >= 1, "Proposition 5.1 free masks are both empty")
    return q


ROW_BY_LABEL = {}
BASE_LABELS = set()
CLAUSE_BY_ARM = {}
ARMS_BY_CLAUSE = {}
UN_CLAUSES_SEEN = set()
TERM_FAMILIES = (
    "base", "nonneg", "ARCH", "G", "DET", "SP", "PS", "CS4",
    "POW", "GROUP12", "UN"
)
BRANCH_FAMILIES = (
    "ARCH", "G", "DET", "SP", "PS", "CS4", "POW", "GROUP12", "UN"
)


def register_row(row, base=False):
    coeff, rhs, label = row
    old = ROW_BY_LABEL.get(label)
    if old is not None:
        require(old == row, f"label {label!r} reconstructed inconsistently")
    else:
        ROW_BY_LABEL[label] = row
    if base:
        BASE_LABELS.add(label)


def register_clause(key, arms):
    require(type(key) is str and key, "invalid clause key")
    require(type(arms) in (tuple, list) and len(arms) >= 2,
            f"{key}: clause must have at least two arms")
    labels = tuple(arm[2] for arm in arms)
    require(len(set(labels)) == len(labels), f"{key}: duplicate arm labels")
    old = ARMS_BY_CLAUSE.get(key)
    if old is not None:
        require(old == labels, f"{key}: inconsistent clause arm set")
    else:
        ARMS_BY_CLAUSE[key] = labels
    for arm in arms:
        register_row(arm)
        label = arm[2]
        old_key = CLAUSE_BY_ARM.get(label)
        require(old_key is None or old_key == key,
                f"arm {label!r} belongs to two clauses")
        CLAUSE_BY_ARM[label] = key


def build_base_rows():
    rows = [make_row({"a": 1, "b": 1, "c": 1}, 1, "L")]
    for side in "abc":
        rows.append(make_row(
            add_expr(({f"{side}{i}": 1 for i in RNG}, 1), ({side: 1}, -1)),
            0, f"roots<={side}"))
        rows.append(make_row(
            {side: 7, **{f"{side}{i}": -7 for i in RNG}, f"v{side}": -1},
            0, f"tail7-{side}"))
        rows.append(make_row(
            {**{f"{side}{i}": i for i in RNG}, f"v{side}": 1},
            1, f"val-{side}"))
        rows.append(make_row(
            {side: 7, **{f"{side}{i}": -(7 - i) for i in RNG}},
            1, f"rad-{side}"))
        for j, indices in enumerate(((2, 4, 6), (3, 6), (5,))):
            rows.append(make_row(
                {**{f"{side}{i}": 1 for i in indices}, f"m{side}": -1},
                0, f"fourier-{side}-{j}"))
    for y, z in (("a", "b"), ("a", "c"), ("b", "c")):
        rows.append(make_row({"D": 1, y: -1, z: -1}, 0, f"pair-{y}{z}"))
    rows.append(make_row(
        {"ma": 1, "mb": 1, "mc": 1,
         "a": -4, "b": -4, "c": -4, "D": 6},
        0, "fourier-sum"))
    rows.append(make_row(
        {"D": 1, "a": -1, "b": -1, "c": -1,
         "a3": 1, "b3": 1, "c3": 1},
        0, "HB3"))
    rows.append(make_row(
        add_expr((value_expr("a"), 1), (value_expr("c"), -1)),
        0, "ARCH:a<=c"))
    rows.append(make_row(
        add_expr((value_expr("b"), 1), (value_expr("c"), -1)),
        0, "ARCH:b<=c"))
    require(len(rows) == 29, f"internal error: expected 29 base rows, got {len(rows)}")
    for row in rows:
        register_row(row, base=True)


def build_arch_clause():
    """Scale-free positive A+B=C cover; valid at any trie depth."""
    arms = (
        make_row(add_expr((value_expr("c"), 1), (value_expr("a"), -1)),
                 0, "ARCH:max-a"),
        make_row(add_expr((value_expr("c"), 1), (value_expr("b"), -1)),
                 0, "ARCH:max-b"),
    )
    register_clause("ARCH:max", arms)


def build_geometry_clauses():
    clauses = []
    total_radical = {"a": Q(1), "b": Q(1), "c": Q(1)}

    def add(name, e1, constant1, e2, constant2):
        # min(e1+c1,e2+c2) <= L-D gives the two-arm upper disjunction.
        g1 = add_expr((total_radical, 1), (e1, -1))
        g2 = add_expr((total_radical, 1), (e2, -1))
        arm1 = make_row(add_expr(({"D": 1}, 1), (g1, -1)),
                        -Q(constant1), name + ":0")
        arm2 = make_row(add_expr(({"D": 1}, 1), (g2, -1)),
                        -Q(constant2), name + ":1")
        clauses.append((name, (arm1, arm2)))

    add("G0", add_expr((p(1), 1), (p(2), 1), (p(4), 1)), 0,
        add_expr((p(2), -1), (p(4), -3)), 1)
    for side in "abc":
        add(f"G1-{side}",
            add_expr((p(1), 1), (p(2), 1), ({f"{side}3": 1}, 1)), 0,
            add_expr((p(2), -1), ({f"{side}3": -2}, 1)), 1)
    for side, other in (("a", "b"), ("b", "c"), ("c", "a")):
        add(f"G2-{side}{other}",
            add_expr((p(1), 1), (p(2), 1),
                     ({f"{side}3": 1, f"{other}3": 1}, 1)), 0,
            add_expr((p(2), -1),
                     ({f"{side}3": -2, f"{other}3": -2}, 1)), 1)
    for side in "abc":
        y, z = tuple(s for s in "abc" if s != side)
        add(f"G3-{side}",
            add_expr((p(1), 1),
                     ({f"{side}3": 1, f"{y}2": 1, f"{z}2": 1}, 1)), 0,
            {f"{side}3": -2, f"{y}2": -1, f"{z}2": -1}, 1)
    for side in "abc":
        y, z = tuple(s for s in "abc" if s != side)
        add(f"G4-{side}",
            add_expr((p(1), 1),
                     ({f"{side}2": 1, f"{y}3": 1, f"{z}3": 1}, 1)), 0,
            {f"{side}2": -1, f"{y}3": -2, f"{z}3": -2}, 1)
    require(len(clauses) == 13,
            f"internal error: expected 13 geometry clauses, got {len(clauses)}")
    for key, arms in clauses:
        register_clause(key, arms)


def build_det_clauses():
    for k in (2, 4, 5, 6):
        base = add_expr(({side: 1 for side in "abc"}, 1),
                        ({f"{side}{k}": 1 for side in "abc"}, -1))
        arms = []
        for side in "abc":
            bound = add_expr((base, 1), ({f"{side}{k}": Q(2, k)}, 1))
            arms.append(upper_arm(bound, f"DET{k}:{side}"))
        register_clause(f"DET{k}", arms)


def build_spacing_clauses():
    count = 0
    for equation_side in "abc":
        other1, other2 = SIDES[equation_side]
        for y, z in ((other1, other2), (other2, other1)):
            for k in range(2, 7):
                base = {y: Q(1), z: Q(1), f"{z}{k}": Q(-1)}
                excess = add_expr((value_expr(equation_side), 1),
                                  (value_expr(z), -1),
                                  ({f"{z}{k}": 1}, 1))
                key = f"SP:{equation_side}:{y}:{z}:{k}"
                arms = (
                    upper_arm(base, key + ":0"),
                    upper_arm(add_expr((base, 1), (excess, 1)), key + ":1"),
                )
                register_clause(key, arms)
                count += 1
    require(count == 30, f"internal error: expected 30 spacing clauses, got {count}")


def build_nonnegative_rows():
    for variable in VARS:
        register_row(make_row({variable: -1}, 0, "nonneg:" + variable))


def build_static_system():
    build_base_rows()
    build_arch_clause()
    build_geometry_clauses()
    build_det_clauses()
    build_spacing_clauses()
    build_nonnegative_rows()
    require(len(BASE_LABELS) == 29,
            f"internal error: static base-label count is {len(BASE_LABELS)}")
    require(len(ARMS_BY_CLAUSE) == 1 + 13 + 4 + 30,
            f"internal error: static clause count is {len(ARMS_BY_CLAUSE)}")
    require(len(ROW_BY_LABEL) == 29 + 2 + 2 * 13 + 3 * 4 + 2 * 30 + 28,
            f"internal error: static row count is {len(ROW_BY_LABEL)}")


def construct_ps_clause(side, selected_mask):
    require(side in SIDES, f"PS: invalid modulus side {side!r}")
    require(1 <= selected_mask < 128,
            f"PS:{side}: selected mask must be nonempty and <128")
    cost, weight = selected_root_value(side, selected_mask)
    y, z = SIDES[side]
    pair = {y: Q(1), z: Q(1)}
    key = f"PS:{side}:{selected_mask}"
    bounds = (
        add_expr((cost, 1), (pair, Q(1, 2))),
        add_expr((cost, 1), (pair, 1), (weight, Q(-2, 3))),
    )
    return key, (
        upper_arm(bounds[0], key + ":half"),
        upper_arm(bounds[1], key + ":2W3"),
    )


def construct_cs4_clause(side, selected_mask, held):
    require(side in SIDES, f"CS4: invalid modulus side {side!r}")
    require(1 <= selected_mask < 128,
            f"CS4:{side}: selected mask must be nonempty and <128")
    require(type(held) is tuple and len(held) == 4,
            f"CS4:{side}:{selected_mask}: held set must contain four slots")
    require(len(set(held)) == 4,
            f"CS4:{side}:{selected_mask}: duplicate held slot")
    require(tuple(sorted(held)) == held,
            f"CS4:{side}:{selected_mask}: held slots are not canonical-sorted")
    allowed_sides = frozenset(SIDES[side])
    for slot in held:
        require(_SLOT_RE.fullmatch(slot) is not None,
                f"CS4:{side}:{selected_mask}: invalid held slot {slot!r}")
        require(slot[0] in allowed_sides,
                f"CS4:{side}:{selected_mask}: held slot lies on modulus side")
    cost, weight = selected_root_value(side, selected_mask)
    y, z = SIDES[side]
    pair = {y: Q(1), z: Q(1)}
    held_mass = {slot: Q(1) for slot in held}
    held_text = ",".join(held)
    key = f"CS4:{side}:{selected_mask}:{held_text}"
    bounds = (
        add_expr((cost, 1), (pair, 1), (weight, -1)),
        add_expr((cost, 1), (pair, 1), (held_mass, Q(-1, 2))),
    )
    return key, (
        upper_arm(bounds[0], key + ":W"),
        upper_arm(bounds[1], key + ":h2"),
    )


def construct_pow3_clause(side, held):
    """Reconstruct an allowed source-bound unlocalized POW-3 two-arm row."""
    require(side in "abc", f"POW3: forbidden powered side {side!r}")
    prefix = f"POW3{side}"
    require(type(held) is tuple and len(held) == 4,
            f"{prefix}: retained set must contain four slots")
    require(len(set(held)) == 4, f"{prefix}: duplicate retained slot")
    require(tuple(sorted(held)) == held,
            f"{prefix}: retained slots are not canonical-sorted")
    allowed_sides = frozenset(s for s in "abc" if s != side)
    for slot in held:
        require(_SLOT_RE.fullmatch(slot) is not None,
                f"{prefix}: invalid retained slot {slot!r}")
        require(slot[0] in allowed_sides,
                f"{prefix}: retained slot lies on powered side")
    if side == "a":
        target_mass_num = sum(
            POW3A_TARGET_MASS_NUM.get(slot, 0) for slot in held)
        require(target_mass_num <= 14,
                f"POW3a: descriptor is outside target-safe whitelist "
                f"(mass={target_mass_num}/37)")
    coefficient_cost = {
        side: Q(1), f"{side}3": Q(-1), f"{side}6": Q(-1)}
    represented_radical = {s: Q(1) for s in allowed_sides}
    retained_mass = {slot: Q(1) for slot in held}
    S = add_expr((coefficient_cost, 1), (represented_radical, 1),
                 (retained_mass, Q(-1, 2)))
    average = add_expr((S, Q(1, 2)), (represented_radical, Q(1, 2)))
    key = prefix + ":" + ",".join(held)
    return key, (
        upper_arm(S, key + ":S"),
        upper_arm(average, key + ":avg"),
    )


def construct_group12_clause(powered_side, group_side, other_index=4):
    """Reconstruct one of the two fixed powered-c grouped POW3 rows."""
    require((powered_side, group_side, other_index)
            in {("c", "a", 4), ("c", "b", 4)},
            f"GROUP12: forbidden powered/grouped pair "
            f"{(powered_side, group_side, other_index)!r}")
    represented = tuple(side for side in "abc" if side != powered_side)
    other_side = next(side for side in represented if side != group_side)
    coefficient_cost = {
        powered_side: Q(1), f"{powered_side}3": Q(-1),
        f"{powered_side}6": Q(-1)}
    coefficient_value = {
        f"v{powered_side}": Q(1), f"{powered_side}1": Q(1),
        f"{powered_side}2": Q(2), f"{powered_side}4": Q(1),
        f"{powered_side}5": Q(2),
    }
    represented_radical = {side: Q(1) for side in represented}
    held = tuple(sorted((
        f"{group_side}1", f"{group_side}2", f"{group_side}4",
        f"{other_side}1", f"{other_side}{other_index}",
    )))
    retained_mass = {slot: Q(1) for slot in held}
    child_s = add_expr(
        (coefficient_cost, 1), (represented_radical, 1),
        (retained_mass, Q(-1, 2)))
    average = add_expr(
        (child_s, Q(1, 2)), (represented_radical, Q(1, 2)))
    group_length = {
        f"{group_side}1": Q(1), f"{group_side}2": Q(2)}
    gate = add_expr(
        (child_s, 1), (group_length, 1),
        (coefficient_value, Q(-1, 2)))
    singles = "+".join((
        f"{group_side}4", f"{other_side}1",
        f"{other_side}{other_index}"))
    key = (f"GROUP12{powered_side}:"
           f"{group_side}1{group_side}2sq+{singles}")
    return key, (
        upper_arm(child_s, key + ":S"),
        upper_arm(average, key + ":avg"),
        upper_arm(gate, key + ":gate"),
    )


def construct_group12c_clause(group_side):
    """Compatibility wrapper for the two established POW3(c) rows."""
    return construct_group12_clause("c", group_side)


def canonical_group12a_c_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 3,
            "GROUP12a(c): singleton tuple must have length three")
    require(len(set(singletons)) == 3,
            "GROUP12a(c): duplicate singleton")
    require(set(singletons) <= set(GROUP12A_C_SINGLETON_POOL),
            "GROUP12a(c): singleton outside the authorized pool")
    canonical = (tuple(sorted(slot for slot in singletons if slot[0] == "c"))
                 + tuple(sorted(slot for slot in singletons if slot[0] == "b")))
    require(singletons == canonical,
            "GROUP12a(c): singleton descriptor is not canonical")
    return singletons


def construct_group12a_c_clause(singletons):
    """Reconstruct one of all C(10,3) powered-a single-group rows."""
    singletons = canonical_group12a_c_singletons(singletons)
    coefficient_cost = {"a": Q(1), "a3": Q(-1), "a6": Q(-1)}
    coefficient_value = {
        "va": Q(1), "a1": Q(1), "a2": Q(2),
        "a4": Q(1), "a5": Q(2)}
    represented_radical = {"b": Q(1), "c": Q(1)}
    retained_mass = {slot: Q(1)
                     for slot in (("c1", "c2") + singletons)}
    child_s = add_expr(
        (coefficient_cost, 1), (represented_radical, 1),
        (retained_mass, Q(-1, 2)))
    average = add_expr(
        (child_s, Q(1, 2)), (represented_radical, Q(1, 2)))
    group_length = {"c1": Q(1), "c2": Q(2)}
    gate = add_expr(
        (child_s, 1), (group_length, 1),
        (coefficient_value, Q(-1, 2)))
    key = "GROUP12a:c1c2sq+" + "+".join(singletons)
    return key, (
        upper_arm(child_s, key + ":S"),
        upper_arm(average, key + ":avg"),
        upper_arm(gate, key + ":gate"),
    )


def canonical_group12b_c_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 3,
            "GROUP12b(c): singleton tuple must have length three")
    require(len(set(singletons)) == 3,
            "GROUP12b(c): duplicate singleton")
    require(set(singletons) <= set(GROUP12B_C_SINGLETON_POOL),
            "GROUP12b(c): singleton outside the authorized pool")
    canonical = (tuple(sorted(slot for slot in singletons if slot[0] == "c"))
                 + tuple(sorted(slot for slot in singletons if slot[0] == "a")))
    require(singletons == canonical,
            "GROUP12b(c): singleton descriptor is not canonical")
    return singletons


def construct_group12b_c_clause(singletons):
    """Reconstruct one of all C(10,3) powered-b single-group rows."""
    singletons = canonical_group12b_c_singletons(singletons)
    coefficient_cost = {"b": Q(1), "b3": Q(-1), "b6": Q(-1)}
    coefficient_value = {
        "vb": Q(1), "b1": Q(1), "b2": Q(2),
        "b4": Q(1), "b5": Q(2)}
    represented_radical = {"a": Q(1), "c": Q(1)}
    retained_mass = {slot: Q(1)
                     for slot in (("c1", "c2") + singletons)}
    child_s = add_expr(
        (coefficient_cost, 1), (represented_radical, 1),
        (retained_mass, Q(-1, 2)))
    average = add_expr(
        (child_s, Q(1, 2)), (represented_radical, Q(1, 2)))
    group_length = {"c1": Q(1), "c2": Q(2)}
    gate = add_expr(
        (child_s, 1), (group_length, 1),
        (coefficient_value, Q(-1, 2)))
    key = "GROUP12b:c1c2sq+" + "+".join(singletons)
    return key, (
        upper_arm(child_s, key + ":S"),
        upper_arm(average, key + ":avg"),
        upper_arm(gate, key + ":gate"),
    )


def canonical_group1212a_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 2,
            "GROUP1212a: singleton tuple must have length two")
    require(len(set(singletons)) == 2,
            "GROUP1212a: duplicate singleton")
    require(set(singletons) <= set(GROUP1212A_SINGLETON_POOL),
            "GROUP1212a: singleton outside the authorized pool")
    canonical = tuple(sorted(singletons, key=lambda slot: (slot[0], slot[1])))
    require(singletons == canonical,
            "GROUP1212a: singleton descriptor is not canonical")
    return singletons


def construct_group1212a_clause(singletons):
    """Reconstruct one of all C(8,2) powered-a double-group rows."""
    singletons = canonical_group1212a_singletons(singletons)
    coefficient_cost = {"a": Q(1), "a3": Q(-1), "a6": Q(-1)}
    coefficient_value = {
        "va": Q(1), "a1": Q(1), "a2": Q(2),
        "a4": Q(1), "a5": Q(2)}
    represented_radical = {"b": Q(1), "c": Q(1)}
    retained_mass = {slot: Q(1) for slot in (
        ("b1", "b2", "c1", "c2") + singletons)}
    child_s = add_expr(
        (coefficient_cost, 1), (represented_radical, 1),
        (retained_mass, Q(-1, 2)))
    average = add_expr(
        (child_s, Q(1, 2)), (represented_radical, Q(1, 2)))
    gate_b = add_expr(
        (child_s, 1), ({"b1": 1, "b2": 2}, 1),
        (coefficient_value, Q(-1, 2)))
    gate_c = add_expr(
        (child_s, 1), ({"c1": 1, "c2": 2}, 1),
        (coefficient_value, Q(-1, 2)))
    key = "GROUP1212a:b1b2sq+c1c2sq+" + "+".join(singletons)
    return key, (
        upper_arm(child_s, key + ":S"),
        upper_arm(average, key + ":avg"),
        upper_arm(gate_b, key + ":gate-b"),
        upper_arm(gate_c, key + ":gate-c"),
    )


def canonical_group1212b_singletons(singletons):
    require(type(singletons) is tuple and len(singletons) == 2,
            "GROUP1212b: singleton tuple must have length two")
    require(len(set(singletons)) == 2,
            "GROUP1212b: duplicate singleton")
    require(set(singletons) <= set(GROUP1212B_SINGLETON_POOL),
            "GROUP1212b: singleton outside the authorized pool")
    canonical = tuple(sorted(singletons, key=lambda slot: (slot[0], slot[1])))
    require(singletons == canonical,
            "GROUP1212b: singleton descriptor is not canonical")
    return singletons


def construct_group1212b_clause(singletons):
    """Reconstruct one of all C(8,2) powered-b double-group rows."""
    singletons = canonical_group1212b_singletons(singletons)
    coefficient_cost = {"b": Q(1), "b3": Q(-1), "b6": Q(-1)}
    coefficient_value = {
        "vb": Q(1), "b1": Q(1), "b2": Q(2),
        "b4": Q(1), "b5": Q(2)}
    represented_radical = {"a": Q(1), "c": Q(1)}
    retained_mass = {slot: Q(1) for slot in (
        ("a1", "a2", "c1", "c2") + singletons)}
    child_s = add_expr(
        (coefficient_cost, 1), (represented_radical, 1),
        (retained_mass, Q(-1, 2)))
    average = add_expr(
        (child_s, Q(1, 2)), (represented_radical, Q(1, 2)))
    gate_a = add_expr(
        (child_s, 1), ({"a1": 1, "a2": 2}, 1),
        (coefficient_value, Q(-1, 2)))
    gate_c = add_expr(
        (child_s, 1), ({"c1": 1, "c2": 2}, 1),
        (coefficient_value, Q(-1, 2)))
    key = "GROUP1212b:a1a2sq+c1c2sq+" + "+".join(singletons)
    return key, (
        upper_arm(child_s, key + ":S"),
        upper_arm(average, key + ":avg"),
        upper_arm(gate_a, key + ":gate-a"),
        upper_arm(gate_c, key + ":gate-c"),
    )


def construct_un_clause(side, free1, free2, selected_mask):
    """Reconstruct Proposition 5.1 (5.6), and no stronger extension."""
    require(side in SIDES, f"UN: invalid modulus side {side!r}")
    # Proposition 5.1 has R_y,R_z subset [6].  Bit 6 (tail) is forbidden
    # in the counted-side free masks, while T on the modulus side may use it.
    require(0 <= free1 < 64 and 0 <= free2 < 64,
            f"UN:{side}: counted free masks must be subsets of [6]")
    require(free1 != 0 or free2 != 0,
            f"UN:{side}: Proposition 5.1 requires a nonempty free union")
    require(1 <= selected_mask < 128,
            f"UN:{side}: modulus mask T must be nonempty and <128")
    y, z = SIDES[side]
    cost, weight = selected_root_value(side, selected_mask)
    free_y, value_y = selected_root_value(y, free1)
    free_z, value_z = selected_root_value(z, free2)
    # The <64 assertions above ensure selected_root_value did not add tails.
    q = free_gcd(free1, free2)
    fixed_yz = add_expr(({y: 1, z: 1}, 1),
                        (free_y, -1), (free_z, -1))
    base_bound = add_expr((fixed_yz, 1), (cost, 1))
    positive_part_argument = add_expr(
        (value_y, Q(1, q)), (value_z, Q(1, q)), (weight, -1))
    key = f"UN:{side}:{free1}:{free2}:{selected_mask}"
    UN_CLAUSES_SEEN.add((side, free1, free2, selected_mask))
    return key, (
        upper_arm(base_bound, key + ":00"),
        upper_arm(add_expr((base_bound, 1), (positive_part_argument, 1)),
                  key + ":10"),
    )


def ensure_row_label(label):
    require(type(label) is str and label, "row label is empty/non-string")
    if label in ROW_BY_LABEL:
        return ROW_BY_LABEL[label]
    parts = label.split(":")
    if parts[0] == "PS" and len(parts) == 4:
        side = parts[1]
        selected_mask = parse_uint(parts[2], label)
        require(parts[3] in ("half", "2W3"), f"unknown PS arm: {label}")
        key, arms = construct_ps_clause(side, selected_mask)
        register_clause(key, arms)
    elif parts[0] == "CS4" and len(parts) == 5:
        side = parts[1]
        selected_mask = parse_uint(parts[2], label)
        held = tuple(parts[3].split(","))
        require(parts[4] in ("W", "h2"), f"unknown CS4 arm: {label}")
        key, arms = construct_cs4_clause(side, selected_mask, held)
        register_clause(key, arms)
    elif parts[0] in ("POW3a", "POW3b", "POW3c") and len(parts) == 3:
        held = tuple(parts[1].split(","))
        require(parts[2] in ("S", "avg"), f"unknown POW3 arm: {label}")
        key, arms = construct_pow3_clause(parts[0][-1], held)
        register_clause(key, arms)
    elif parts[0] == "GROUP12c" and len(parts) == 3:
        descriptor_to_side = {
            "a1a2sq+a4+b1+b4": "a",
            "b1b2sq+b4+a1+a4": "b",
        }
        require(parts[1] in descriptor_to_side,
                f"unknown GROUP12c descriptor: {label}")
        require(parts[2] in ("S", "avg", "gate"),
                f"unknown GROUP12 arm: {label}")
        key, arms = construct_group12c_clause(descriptor_to_side[parts[1]])
        register_clause(key, arms)
    elif parts[0] == "GROUP12a" and len(parts) == 3:
        descriptor = parts[1].split("+")
        require(len(descriptor) == 4 and descriptor[0] == "c1c2sq",
                f"unknown GROUP12a descriptor: {label}")
        require(parts[2] in ("S", "avg", "gate"),
                f"unknown GROUP12a arm: {label}")
        key, arms = construct_group12a_c_clause(tuple(descriptor[1:]))
        register_clause(key, arms)
    elif parts[0] == "GROUP12b" and len(parts) == 3:
        descriptor = parts[1].split("+")
        require(len(descriptor) == 4 and descriptor[0] == "c1c2sq",
                f"unknown GROUP12b descriptor: {label}")
        require(parts[2] in ("S", "avg", "gate"),
                f"unknown GROUP12b arm: {label}")
        key, arms = construct_group12b_c_clause(tuple(descriptor[1:]))
        register_clause(key, arms)
    elif parts[0] == "GROUP1212a" and len(parts) == 3:
        descriptor = parts[1].split("+")
        require(len(descriptor) == 4
                and descriptor[:2] == ["b1b2sq", "c1c2sq"],
                f"unknown GROUP1212a descriptor: {label}")
        require(parts[2] in ("S", "avg", "gate-b", "gate-c"),
                f"unknown GROUP1212a arm: {label}")
        key, arms = construct_group1212a_clause(tuple(descriptor[2:]))
        register_clause(key, arms)
    elif parts[0] == "GROUP1212b" and len(parts) == 3:
        descriptor = parts[1].split("+")
        require(len(descriptor) == 4
                and descriptor[:2] == ["a1a2sq", "c1c2sq"],
                f"unknown GROUP1212b descriptor: {label}")
        require(parts[2] in ("S", "avg", "gate-a", "gate-c"),
                f"unknown GROUP1212b arm: {label}")
        key, arms = construct_group1212b_clause(tuple(descriptor[2:]))
        register_clause(key, arms)
    elif parts[0] == "UN" and len(parts) == 6:
        side = parts[1]
        free1 = parse_uint(parts[2], label)
        free2 = parse_uint(parts[3], label)
        selected_mask = parse_uint(parts[4], label)
        require(parts[5] in ("00", "10"), f"unknown UN arm: {label}")
        key, arms = construct_un_clause(side, free1, free2, selected_mask)
        register_clause(key, arms)
    else:
        fail(f"unknown or forbidden row label: {label!r}")
    require(label in ROW_BY_LABEL,
            f"label was noncanonical or did not match reconstructed arm: {label!r}")
    return ROW_BY_LABEL[label]


def ensure_arm_label(label):
    ensure_row_label(label)
    require(label in CLAUSE_BY_ARM,
            f"path label is not a disjunction arm: {label!r}")
    return CLAUSE_BY_ARM[label]


def label_family(label):
    """Classify an already reconstructed row, rejecting any stray family."""
    require(label in ROW_BY_LABEL, f"cannot classify unknown row {label!r}")
    if label in BASE_LABELS:
        return "base"
    if label.startswith("nonneg:"):
        return "nonneg"
    # Test the grouped families before the one-letter geometry prefix.
    # Otherwise every GROUP12/GROUP1212 label is silently counted as G.
    for family, prefix in (
            ("ARCH", "ARCH:max-"), ("GROUP12", "GROUP12"),
            ("G", "G"),
            ("DET", "DET"), ("SP", "SP:"),
            ("PS", "PS:"), ("CS4", "CS4:"), ("POW", "POW3"),
            ("UN", "UN:")):
        if label.startswith(prefix):
            return family
    fail(f"accepted row has an unclassified family: {label!r}")


def empty_term_census():
    return {
        family: {
            "labels": set(),
            "occurrences": 0,
            "max_leaf_weight_sum": Q(0),
        }
        for family in TERM_FAMILIES
    }


def empty_branch_census():
    return {
        family: {
            "branch_nodes": 0,
            "clauses": set(),
            "arm_labels": set(),
            "arm_edge_occurrences": 0,
        }
        for family in BRANCH_FAMILIES
    }


def exact_zero_vector():
    return {variable: Q(0) for variable in VARS}


def validate_certificate(cert, index, term_census):
    context = f"certificate[{index}]"
    require(type(cert) is dict,
            f"{context}: certificate must be an object")
    require(set(cert) == {"kind", "path", "rhs", "terms"},
            f"{context}: unexpected/missing certificate keys {set(cert)}")
    kind = cert["kind"]
    require(kind in ("upper", "infeas"), f"{context}: invalid kind {kind!r}")
    path = cert["path"]
    require(type(path) is list, f"{context}: path must be a list")
    for depth, label in enumerate(path):
        require(type(label) is str, f"{context}.path[{depth}]: label is not a string")
        ensure_arm_label(label)
    path_set = set(path)
    rhs_declared = parse_q(cert["rhs"], context + ".rhs")
    terms = cert["terms"]
    require(type(terms) is list and terms,
            f"{context}: terms must be a nonempty list")
    coefficients = exact_zero_vector()
    rhs = Q(0)
    multiplier_sum = Q(0)
    relaxation_weight = Q(0)
    family_weights = {family: Q(0) for family in TERM_FAMILIES}
    term_labels = set()
    for term_index, term in enumerate(terms):
        tctx = f"{context}.terms[{term_index}]"
        require(type(term) is list and len(term) == 2,
                f"{tctx}: term must be [label,multiplier]")
        label, multiplier_text = term
        require(type(label) is str, f"{tctx}: label is not a string")
        require(label not in term_labels, f"{context}: duplicate term label {label!r}")
        term_labels.add(label)
        multiplier = parse_q(multiplier_text, tctx + ".multiplier")
        require(multiplier > 0, f"{tctx}: multiplier must be strictly positive")
        row_coeff, row_rhs, _ = ensure_row_label(label)
        family = label_family(label)
        term_census[family]["labels"].add(label)
        term_census[family]["occurrences"] += 1
        family_weights[family] += multiplier
        if family != "nonneg":
            # Nonnegativity rows have exact zero RHS and carry no analytic
            # box-reduction relaxation.  Every other row is conservatively
            # charged one common rho in the finite-eta ledger.
            relaxation_weight += multiplier
        if label not in BASE_LABELS and not label.startswith("nonneg:"):
            require(label in path_set,
                    f"{context}: scope leak, row {label!r} is absent from path")
        for variable, coefficient in row_coeff.items():
            coefficients[variable] += multiplier * coefficient
        rhs += multiplier * row_rhs
        multiplier_sum += multiplier
    require(rhs == rhs_declared,
            f"{context}: combined RHS {rhs} != declared RHS {rhs_declared}")
    if kind == "upper":
        expected = exact_zero_vector()
        expected["D"] = Q(1)
        require(coefficients == expected,
                f"{context}: upper coefficients do not equal e_D")
        require(rhs <= TARGET,
                f"{context}: upper RHS {rhs} exceeds target {TARGET}")
    else:
        require(coefficients == ZERO,
                f"{context}: infeasibility coefficients are not zero")
        require(multiplier_sum == 1,
                f"{context}: infeasibility multiplier normalization is not one")
        require(rhs < 0,
                f"{context}: infeasibility RHS is not negative")
    for family, weight in family_weights.items():
        term_census[family]["max_leaf_weight_sum"] = max(
            term_census[family]["max_leaf_weight_sum"], weight)
    return tuple(path), kind, relaxation_weight, rhs, index, len(terms)


def new_trie_node():
    return {"children": {}, "certificate": None}


def build_certificate_trie(certificate_paths):
    root = new_trie_node()
    for index, record in enumerate(certificate_paths):
        path = record[0]
        node = root
        for depth, label in enumerate(path):
            require(node["certificate"] is None,
                    f"certificate[{index}] descends below an already certified prefix")
            node = node["children"].setdefault(label, new_trie_node())
        require(node["certificate"] is None,
                f"duplicate certificate path at certificate[{index}]")
        require(not node["children"],
                f"certificate[{index}] is a prefix of an earlier certificate")
        node["certificate"] = index
    return root


def validate_trie_coverage(node, branch_census, depth=0):
    children = node["children"]
    certificate = node["certificate"]
    if certificate is not None:
        require(not children,
                f"certified trie node at depth {depth} has descendants")
        return 1, 0, depth
    require(children, f"uncovered trie prefix at depth {depth}")
    child_labels = set(children)
    clause_keys = {ensure_arm_label(label) for label in child_labels}
    require(len(clause_keys) == 1,
            f"mixed clauses at trie depth {depth}: {sorted(clause_keys)}")
    clause_key = next(iter(clause_keys))
    expected_labels = set(ARMS_BY_CLAUSE[clause_key])
    require(child_labels == expected_labels,
            f"incomplete OR at depth {depth} for {clause_key}: "
            f"got {sorted(child_labels)}, expected {sorted(expected_labels)}")
    family = label_family(next(iter(child_labels)))
    require(family in BRANCH_FAMILIES,
            f"non-branch family {family!r} at trie depth {depth}")
    require(all(label_family(label) == family for label in child_labels),
            f"mixed row families inside clause {clause_key}")
    branch_census[family]["branch_nodes"] += 1
    branch_census[family]["clauses"].add(clause_key)
    branch_census[family]["arm_labels"].update(child_labels)
    branch_census[family]["arm_edge_occurrences"] += len(child_labels)
    leaves = 0
    internal = 1
    maximum_depth = depth
    for child in children.values():
        child_leaves, child_internal, child_depth = validate_trie_coverage(
            child, branch_census, depth + 1)
        leaves += child_leaves
        internal += child_internal
        maximum_depth = max(maximum_depth, child_depth)
    return leaves, internal, maximum_depth


def validate_report(report):
    require(type(report) is dict, "report root must be an object")
    expected_top = {
        "target", "system", "search_flags", "complete", "elapsed_s", "stats",
        "certificates", "survivors", "open_stack",
    }
    require(set(report) == expected_top,
            f"unexpected/missing top-level keys: {set(report)}")
    require(report["target"] == str(TARGET),
            f"wrong target: {report['target']!r}")
    require(report["system"] == EXPECTED_SYSTEM,
            f"wrong proof system: {report['system']!r}")
    flags = report["search_flags"]
    require(type(flags) is dict and set(flags) == {
        "no_prop", "spacing_first", "spacing_meta", "prop_forms", "regular_free",
        "pow3b_regular", "pow3a_target_safe", "pow3c_regular",
        "arch_value_cover", "group12c_ab12", "group12a_c12_all3",
        "group12b_c12_all3", "group1212a_all2", "group1212b_all2"
    }, f"unexpected/missing search flags: {flags!r}")
    require(flags["no_prop"] is False, "UN proposition search was disabled")
    require(type(flags["spacing_first"]) is bool,
            "spacing_first flag is not Boolean")
    require(flags["spacing_meta"] is False,
            "spacing-meta reports are outside this verifier's label semantics")
    require(flags["prop_forms"] == ["UN"],
            f"forbidden proposition forms in report: {flags['prop_forms']!r}")
    require(flags["regular_free"] is True,
            "report did not restrict counted-side free masks to [6]")
    require(flags["pow3b_regular"] is True,
            "report did not enable the regular retained-block POW3b family")
    require(flags["pow3a_target_safe"] is True,
            "report did not enable the target-safe POW3a family")
    require(flags["pow3c_regular"] is True,
            "report did not enable the regular retained-block POW3c family")
    require(flags["arch_value_cover"] is True,
            "report did not enable the homogeneous ARCH value cover")
    require(flags["group12c_ab12"] is True,
            "report did not enable both fixed GROUP12c clauses")
    require(flags["group12a_c12_all3"] is True,
            "report did not enable all target-safe GROUP12a(c;all3) clauses")
    require(flags["group12b_c12_all3"] is True,
            "report did not enable all target-safe GROUP12b(c;all3) clauses")
    require(flags["group1212a_all2"] is True,
            "report did not enable all target-safe GROUP1212a(all2) clauses")
    require(flags["group1212b_all2"] is True,
            "report did not enable all target-safe GROUP1212b(all2) clauses")
    require(report["complete"] is True, "report is not marked complete")
    elapsed = report["elapsed_s"]
    require(type(elapsed) in (int, float) and not isinstance(elapsed, bool)
            and math.isfinite(elapsed) and elapsed >= 0,
            f"invalid elapsed_s: {elapsed!r}")
    require(report["survivors"] == [], "report has survivors")
    require(report["open_stack"] == [], "report has an open search stack")

    stats = report["stats"]
    expected_stats = {
        "nodes", "upper_exact", "infeas_exact", "bad_cert", "survivors",
        "open", "max_depth",
    }
    require(type(stats) is dict and set(stats) == expected_stats,
            f"unexpected/missing stats: {stats!r}")
    for key, value in stats.items():
        require(type(value) is int and value >= 0,
                f"stats.{key} must be a nonnegative integer")
    require(stats["bad_cert"] == 0, "report records bad certificates")
    require(stats["survivors"] == 0, "report records surviving leaves")
    require(stats["open"] == 0, "report records open leaves")

    certificates = report["certificates"]
    require(type(certificates) is list and certificates,
            "report certificates must be a nonempty list")
    term_census = empty_term_census()
    certificate_paths = [
        validate_certificate(certificate, index, term_census)
        for index, certificate in enumerate(certificates)
    ]
    upper_count = sum(record[1] == "upper" for record in certificate_paths)
    infeas_count = sum(record[1] == "infeas" for record in certificate_paths)
    require(stats["upper_exact"] == upper_count,
            "stats.upper_exact disagrees with certificate kinds")
    require(stats["infeas_exact"] == infeas_count,
            "stats.infeas_exact disagrees with certificate kinds")
    require(upper_count > 0,
            "tree has no upper certificate (unexpected for this target proof)")

    trie = build_certificate_trie(certificate_paths)
    branch_census = empty_branch_census()
    leaves, internal, maximum_depth = validate_trie_coverage(
        trie, branch_census)
    require(leaves == len(certificates),
            "trie leaf count disagrees with certificate count")
    require(stats["nodes"] == leaves + internal,
            f"stats.nodes={stats['nodes']} != exact trie nodes={leaves + internal}")
    require(stats["max_depth"] == maximum_depth,
            f"stats.max_depth={stats['max_depth']} != trie depth={maximum_depth}")

    # This is an explicit dependency gate: every UN label encountered above
    # has passed free1,free2 < 64 and nonempty-union checks.  selected_mask was
    # allowed up to 127, so Proposition 5.1's T may include the tail.
    for side, free1, free2, selected_mask in UN_CLAUSES_SEEN:
        require(side in SIDES and 0 <= free1 < 64 and 0 <= free2 < 64,
                "internal UN regular-free audit failed")
        require(free1 or free2, "internal UN nonempty-free audit failed")
        require(1 <= selected_mask < 128,
                "internal UN modulus-mask audit failed")

    rho_record = max(certificate_paths, key=lambda record: record[2])
    upper_rho_record = max(
        (record for record in certificate_paths if record[1] == "upper"),
        key=lambda record: record[2])
    infeas_records = [record for record in certificate_paths
                      if record[1] == "infeas"]
    upper_records = [record for record in certificate_paths
                     if record[1] == "upper"]
    worst_upper_record = max(upper_records, key=lambda record: record[3])
    worst_upper_rhs = worst_upper_record[3]
    max_terms_record = max(certificate_paths, key=lambda record: record[5])
    summary = {
        "certified_leaves": leaves,
        "internal_nodes": internal,
        "tree_nodes": leaves + internal,
        "max_depth": maximum_depth,
        "upper_certificates": upper_count,
        "infeas_certificates": infeas_count,
        "un_clauses_used": len(UN_CLAUSES_SEEN),
        "un_tail_modulus_clauses": sum(
            bool(selected_mask & 64)
            for _side, _free1, _free2, selected_mask in UN_CLAUSES_SEEN
        ),
        "rho_multiplier_max": rho_record[2],
        "rho_multiplier_max_certificate": rho_record[4],
        "rho_multiplier_max_kind": rho_record[1],
        "rho_multiplier_max_upper": upper_rho_record[2],
        "rho_multiplier_max_upper_certificate": upper_rho_record[4],
        "worst_upper_rhs": worst_upper_rhs,
        "worst_upper_rhs_certificate": worst_upper_record[4],
        "tight_target_leaves": sum(
            record[3] == TARGET for record in upper_records),
        "max_terms_per_leaf": max_terms_record[5],
        "max_terms_certificate": max_terms_record[4],
        "max_terms_certificate_kind": max_terms_record[1],
    }
    if infeas_records:
        require(all(record[2] > 0 for record in infeas_records),
                "infeasibility certificate has zero analytic relaxation weight")
        infeas_rho_record = max(infeas_records, key=lambda record: record[2])
        margin_record = min(infeas_records, key=lambda record: -record[3])
        ratio_record = min(
            infeas_records,
            key=lambda record: (-record[3] / record[2]))
        summary["infeas_min_abs_margin"] = -margin_record[3]
        summary["infeas_closest_rhs"] = margin_record[3]
        summary["infeas_min_margin_certificate"] = margin_record[4]
        summary["infeas_min_margin_over_rho_weight"] = (
            -ratio_record[3] / ratio_record[2])
        summary["infeas_min_ratio_certificate"] = ratio_record[4]
        summary["rho_multiplier_max_infeas"] = infeas_rho_record[2]
        summary["rho_multiplier_max_infeas_certificate"] = infeas_rho_record[4]
    else:
        summary["infeas_min_abs_margin"] = "NONE"
        summary["infeas_closest_rhs"] = "NONE"
        summary["infeas_min_margin_certificate"] = "NONE"
        summary["infeas_min_margin_over_rho_weight"] = "NONE"
        summary["infeas_min_ratio_certificate"] = "NONE"
        summary["rho_multiplier_max_infeas"] = "NONE"
        summary["rho_multiplier_max_infeas_certificate"] = "NONE"
    for family in BRANCH_FAMILIES:
        census = branch_census[family]
        summary[f"branch_{family}"] = (
            f"nodes:{census['branch_nodes']},"
            f"distinct_clauses:{len(census['clauses'])},"
            f"distinct_arm_labels:{len(census['arm_labels'])},"
            f"arm_edge_occurrences:{census['arm_edge_occurrences']}"
        )
    for family in TERM_FAMILIES:
        census = term_census[family]
        summary[f"terms_{family}"] = (
            f"distinct_labels:{len(census['labels'])},"
            f"occurrences:{census['occurrences']},"
            f"max_leaf_weight_sum:{census['max_leaf_weight_sum']}"
        )
    return summary


def reject_json_constant(token):
    fail(f"nonstandard JSON numeric constant: {token}")


def reject_duplicate_object_pairs(pairs):
    """Strict JSON object hook: reject duplicate keys at every nesting level."""
    out = {}
    for key, value in pairs:
        require(key not in out, f"duplicate JSON object key: {key!r}")
        out[key] = value
    return out


def load_json_strict(handle):
    return json.load(
        handle,
        parse_constant=reject_json_constant,
        object_pairs_hook=reject_duplicate_object_pairs,
    )


def expect_verification_failure(name, function):
    try:
        function()
    except VerificationError:
        return name
    fail(f"mutation {name!r} was incorrectly accepted")


def copy_certificate(certificate):
    copied = dict(certificate)
    copied["path"] = list(certificate["path"])
    copied["terms"] = [list(term) for term in certificate["terms"]]
    return copied


def run_fail_closed_mutation_suite(report):
    """Adversarial unit mutations after a full report has already passed."""
    passed = []

    bad_status = dict(report)
    bad_status["complete"] = False
    passed.append(expect_verification_failure(
        "incomplete-status", lambda: validate_report(bad_status)))

    bad_open = dict(report)
    bad_open["open_stack"] = [{"forged": True}]
    passed.append(expect_verification_failure(
        "nonempty-open-stack", lambda: validate_report(bad_open)))

    bad_flags = dict(report)
    bad_flags["search_flags"] = dict(report["search_flags"])
    bad_flags["search_flags"]["regular_free"] = False
    passed.append(expect_verification_failure(
        "regular-free-flag-disabled", lambda: validate_report(bad_flags)))

    bad_pow3c_flags = dict(report)
    bad_pow3c_flags["search_flags"] = dict(report["search_flags"])
    bad_pow3c_flags["search_flags"]["pow3c_regular"] = False
    passed.append(expect_verification_failure(
        "pow3c-flag-disabled", lambda: validate_report(bad_pow3c_flags)))

    bad_arch_flags = dict(report)
    bad_arch_flags["search_flags"] = dict(report["search_flags"])
    bad_arch_flags["search_flags"]["arch_value_cover"] = False
    passed.append(expect_verification_failure(
        "arch-flag-disabled", lambda: validate_report(bad_arch_flags)))

    bad_group_flags = dict(report)
    bad_group_flags["search_flags"] = dict(report["search_flags"])
    bad_group_flags["search_flags"]["group12c_ab12"] = False
    passed.append(expect_verification_failure(
        "group12-flag-disabled", lambda: validate_report(bad_group_flags)))

    bad_group_a_flags = dict(report)
    bad_group_a_flags["search_flags"] = dict(report["search_flags"])
    bad_group_a_flags["search_flags"]["group12a_c12_all3"] = False
    passed.append(expect_verification_failure(
        "group12a-flag-disabled", lambda: validate_report(bad_group_a_flags)))

    bad_group_b_flags = dict(report)
    bad_group_b_flags["search_flags"] = dict(report["search_flags"])
    bad_group_b_flags["search_flags"]["group12b_c12_all3"] = False
    passed.append(expect_verification_failure(
        "group12b-flag-disabled", lambda: validate_report(bad_group_b_flags)))

    bad_group1212_flags = dict(report)
    bad_group1212_flags["search_flags"] = dict(report["search_flags"])
    bad_group1212_flags["search_flags"]["group1212a_all2"] = False
    passed.append(expect_verification_failure(
        "group1212a-flag-disabled",
        lambda: validate_report(bad_group1212_flags)))

    bad_group1212b_flags = dict(report)
    bad_group1212b_flags["search_flags"] = dict(report["search_flags"])
    bad_group1212b_flags["search_flags"]["group1212b_all2"] = False
    passed.append(expect_verification_failure(
        "group1212b-flag-disabled",
        lambda: validate_report(bad_group1212b_flags)))

    bad_target = dict(report)
    bad_target["target"] = "21/37"
    passed.append(expect_verification_failure(
        "wrong-target", lambda: validate_report(bad_target)))

    bad_system = dict(report)
    bad_system["system"] = report["system"] + "+FORGED"
    passed.append(expect_verification_failure(
        "wrong-system", lambda: validate_report(bad_system)))

    passed.append(expect_verification_failure(
        "duplicate-json-object-key",
        lambda: json.loads(
            '{"target":"20/37","target":"20/37"}',
            parse_constant=reject_json_constant,
            object_pairs_hook=reject_duplicate_object_pairs,
        )))

    passed.append(expect_verification_failure(
        "unknown-row-label", lambda: ensure_row_label("BOGUS:a:1")))
    passed.append(expect_verification_failure(
        "free-tail-UN-label", lambda: ensure_row_label("UN:a:64:1:1:00")))
    passed.append(expect_verification_failure(
        "double-empty-UN-label", lambda: ensure_row_label("UN:a:0:0:1:00")))
    passed.append(expect_verification_failure(
        "powered-side-POW3b-slot",
        lambda: ensure_row_label("POW3b:a1,a3,b1,c1:S")))
    passed.append(expect_verification_failure(
        "duplicate-POW3b-slot",
        lambda: ensure_row_label("POW3b:a1,a1,c1,c3:S")))
    passed.append(expect_verification_failure(
        "powered-side-POW3a-slot",
        lambda: ensure_row_label("POW3a:a1,b1,c1,c3:S")))
    passed.append(expect_verification_failure(
        "powered-side-POW3c-slot",
        lambda: ensure_row_label("POW3c:a1,b1,c1,c3:S")))
    passed.append(expect_verification_failure(
        "unsafe-POW3a-descriptor",
        lambda: ensure_row_label("POW3a:b1,b2,c1,c4:S")))
    passed.append(expect_verification_failure(
        "unknown-GROUP12-descriptor",
        lambda: ensure_row_label("GROUP12c:a1a3sq+a4+b1+b4:S")))
    passed.append(expect_verification_failure(
        "forbidden-GROUP12-side",
        lambda: construct_group12_clause("a", "b", 4)))
    passed.append(expect_verification_failure(
        "noncanonical-GROUP12a-singletons",
        lambda: ensure_row_label("GROUP12a:c1c2sq+b1+c4+b4:S")))
    passed.append(expect_verification_failure(
        "noncanonical-GROUP12b-singletons",
        lambda: ensure_row_label("GROUP12b:c1c2sq+a1+c4+a4:S")))
    passed.append(expect_verification_failure(
        "duplicate-GROUP1212a-singleton",
        lambda: ensure_row_label(
            "GROUP1212a:b1b2sq+c1c2sq+b4+b4:S")))
    passed.append(expect_verification_failure(
        "duplicate-GROUP1212b-singleton",
        lambda: ensure_row_label(
            "GROUP1212b:a1a2sq+c1c2sq+a4+a4:S")))
    passed.append(expect_verification_failure(
        "noncanonical-rational", lambda: parse_q("2/4", "mutation")))

    original = report["certificates"][0]

    bad_path = copy_certificate(original)
    bad_path["path"].append("UNKNOWN:ARM")
    passed.append(expect_verification_failure(
        "unknown-path-arm",
        lambda: validate_certificate(bad_path, -1, empty_term_census())))

    scope_leak = copy_certificate(original)
    leak_label = next(
        label for label in sorted(CLAUSE_BY_ARM)
        if label not in scope_leak["path"]
        and all(term[0] != label for term in scope_leak["terms"])
    )
    scope_leak["terms"].append([leak_label, "1"])
    passed.append(expect_verification_failure(
        "certificate-scope-leak",
        lambda: validate_certificate(scope_leak, -1, empty_term_census())))

    bad_multiplier = copy_certificate(original)
    old_multiplier = parse_q(bad_multiplier["terms"][0][1], "mutation.multiplier")
    bad_multiplier["terms"][0][1] = str(old_multiplier + 1)
    passed.append(expect_verification_failure(
        "tampered-multiplier",
        lambda: validate_certificate(bad_multiplier, -1, empty_term_census())))

    zero_multiplier = copy_certificate(original)
    zero_multiplier["terms"][0][1] = "0"
    passed.append(expect_verification_failure(
        "zero-multiplier",
        lambda: validate_certificate(zero_multiplier, -1, empty_term_census())))

    duplicate_term = copy_certificate(original)
    duplicate_term["terms"].append(list(duplicate_term["terms"][0]))
    passed.append(expect_verification_failure(
        "duplicate-certificate-term",
        lambda: validate_certificate(duplicate_term, -1, empty_term_census())))

    bad_rhs = copy_certificate(original)
    bad_rhs["rhs"] = str(parse_q(bad_rhs["rhs"], "mutation.rhs") + 1)
    passed.append(expect_verification_failure(
        "tampered-certificate-rhs",
        lambda: validate_certificate(bad_rhs, -1, empty_term_census())))

    # A one-child copy of the valid two-arm G0 clause is not an OR cover.
    incomplete_records = [(("G0:0",), "upper", Q(1), Q(0), -1, 1)]
    incomplete_trie = build_certificate_trie(incomplete_records)
    passed.append(expect_verification_failure(
        "missing-OR-arm",
        lambda: validate_trie_coverage(
            incomplete_trie, empty_branch_census())))

    incomplete_arch = build_certificate_trie([
        (("ARCH:max-a",), "upper", Q(1), Q(0), -11, 1),
    ])
    passed.append(expect_verification_failure(
        "missing-ARCH-arm",
        lambda: validate_trie_coverage(
            incomplete_arch, empty_branch_census())))

    incomplete_group = build_certificate_trie([
        (("GROUP12c:a1a2sq+a4+b1+b4:S",),
         "upper", Q(1), Q(0), -12, 1),
        (("GROUP12c:a1a2sq+a4+b1+b4:avg",),
         "upper", Q(1), Q(0), -13, 1),
    ])
    passed.append(expect_verification_failure(
        "missing-GROUP12-arm",
        lambda: validate_trie_coverage(
            incomplete_group, empty_branch_census())))

    incomplete_group_a = build_certificate_trie([
        (("GROUP12a:c1c2sq+c4+b1+b4:S",),
         "upper", Q(1), Q(0), -14, 1),
        (("GROUP12a:c1c2sq+c4+b1+b4:avg",),
         "upper", Q(1), Q(0), -15, 1),
    ])
    passed.append(expect_verification_failure(
        "missing-GROUP12a-arm",
        lambda: validate_trie_coverage(
            incomplete_group_a, empty_branch_census())))

    incomplete_group_b = build_certificate_trie([
        (("GROUP12b:c1c2sq+c4+a1+a4:S",),
         "upper", Q(1), Q(0), -19, 1),
        (("GROUP12b:c1c2sq+c4+a1+a4:avg",),
         "upper", Q(1), Q(0), -20, 1),
    ])
    passed.append(expect_verification_failure(
        "missing-GROUP12b-arm",
        lambda: validate_trie_coverage(
            incomplete_group_b, empty_branch_census())))

    incomplete_group1212 = build_certificate_trie([
        (("GROUP1212a:b1b2sq+c1c2sq+b4+c4:S",),
         "upper", Q(1), Q(0), -16, 1),
        (("GROUP1212a:b1b2sq+c1c2sq+b4+c4:avg",),
         "upper", Q(1), Q(0), -17, 1),
        (("GROUP1212a:b1b2sq+c1c2sq+b4+c4:gate-b",),
         "upper", Q(1), Q(0), -18, 1),
    ])
    passed.append(expect_verification_failure(
        "missing-GROUP1212a-arm",
        lambda: validate_trie_coverage(
            incomplete_group1212, empty_branch_census())))

    incomplete_group1212b = build_certificate_trie([
        (("GROUP1212b:a1a2sq+c1c2sq+a4+c4:S",),
         "upper", Q(1), Q(0), -21, 1),
        (("GROUP1212b:a1a2sq+c1c2sq+a4+c4:avg",),
         "upper", Q(1), Q(0), -22, 1),
        (("GROUP1212b:a1a2sq+c1c2sq+a4+c4:gate-a",),
         "upper", Q(1), Q(0), -23, 1),
    ])
    passed.append(expect_verification_failure(
        "missing-GROUP1212b-arm",
        lambda: validate_trie_coverage(
            incomplete_group1212b, empty_branch_census())))

    # Immediate children from two different valid clauses are not a legal
    # branch partition, even though both individual rows are sound.
    mixed_records = [
        (("G0:0",), "upper", Q(1), Q(0), -1, 1),
        (("DET2:a",), "upper", Q(1), Q(0), -2, 1),
    ]
    mixed_trie = build_certificate_trie(mixed_records)
    passed.append(expect_verification_failure(
        "mixed-OR-clauses",
        lambda: validate_trie_coverage(mixed_trie, empty_branch_census())))

    duplicate_leaf_records = [
        (("G0:0",), "upper", Q(1), Q(0), -3, 1),
        (("G0:0",), "upper", Q(1), Q(0), -4, 1),
    ]
    passed.append(expect_verification_failure(
        "duplicate-leaf",
        lambda: build_certificate_trie(duplicate_leaf_records)))

    prefix_leaf_records = [
        (("G0:0",), "upper", Q(1), Q(0), -5, 1),
        (("G0:0", "DET2:a"), "upper", Q(1), Q(0), -6, 1),
    ]
    passed.append(expect_verification_failure(
        "leaf-prefix-overlap",
        lambda: build_certificate_trie(prefix_leaf_records)))

    # These two mutations deliberately reach the post-replay consistency
    # gates, checking that header statistics cannot disagree with the exact
    # certificate trie even when every individual Farkas certificate is valid.
    bad_node_stats = dict(report)
    bad_node_stats["stats"] = dict(report["stats"])
    bad_node_stats["stats"]["nodes"] += 1
    passed.append(expect_verification_failure(
        "wrong-stats-node-count", lambda: validate_report(bad_node_stats)))

    bad_depth_stats = dict(report)
    bad_depth_stats["stats"] = dict(report["stats"])
    bad_depth_stats["stats"]["max_depth"] += 1
    passed.append(expect_verification_failure(
        "wrong-stats-depth", lambda: validate_report(bad_depth_stats)))

    require(len(passed) == 46,
            f"internal mutation-suite count mismatch: {len(passed)}")
    return passed


def main():
    parser = argparse.ArgumentParser(
        description="Pure-Fraction independent verifier for the 20/37 tree")
    parser.add_argument("report")
    parser.add_argument(
        "--mutation-tests", action="store_true",
        help="after acceptance, run adversarial fail-closed unit mutations")
    args = parser.parse_args()
    build_static_system()
    with open(args.report, "r", encoding="utf-8") as handle:
        report = load_json_strict(handle)
    summary = validate_report(report)
    print("EXACT_TREE_REPORT_CLEAN_PASS")
    for key, value in summary.items():
        print(f"{key}={value}")
    if args.mutation_tests:
        mutations = run_fail_closed_mutation_suite(report)
        print("FAIL_CLOSED_MUTATION_SUITE_PASS")
        print(f"mutation_tests={len(mutations)} names={','.join(mutations)}")


if __name__ == "__main__":
    try:
        main()
    except (VerificationError, ValueError, ZeroDivisionError, KeyError,
            TypeError, OSError, json.JSONDecodeError) as exc:
        raise SystemExit(f"VERIFY_FAIL: {exc}")
