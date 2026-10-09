#!/usr/bin/env python3
"""Exact generator/clean-verifier differential for a finished tree report.

This is intentionally a cross-implementation test: it imports the floating
search compiler only to reconstruct rows, and compares them against the
stdlib/Fraction clean verifier.  It checks every distinct row label actually
used in certificate paths or Farkas terms, plus the complete allowed POW3
descriptor universe.
It also checks ARCH, both fixed powered-c GROUP12 clauses, all 240 powered-a/b
single-group clauses, and all 56 powered-a/b double-group clauses.
"""

import argparse
import itertools

import dynamic_tree_ind as generator
import verify_tree_report_clean as clean


def generator_static_rows():
    rows = list(generator.BASE)
    for _key, arms in (generator.ARCH + generator.GEOMETRY
                       + generator.DET + generator.SPACING):
        rows.extend(arms)
    rows.extend(generator.row({variable: -1}, 0, "nonneg:" + variable)
                for variable in generator.VARS)
    return {row[2]: row for row in rows}


def generator_dynamic_clause(label):
    parts = label.split(":")
    if parts[0] == "PS" and len(parts) == 4:
        return generator.ps_clause(parts[1], int(parts[2]))
    if parts[0] == "CS4" and len(parts) == 5:
        return generator.cs4_clause(
            parts[1], int(parts[2]), tuple(parts[3].split(",")))
    if parts[0] in ("POW3a", "POW3b", "POW3c") and len(parts) == 3:
        return generator.pow3_clause(
            parts[0][-1], tuple(parts[1].split(",")))
    if parts[0] == "GROUP12c" and len(parts) == 3:
        descriptor_to_side = {
            "a1a2sq+a4+b1+b4": "a",
            "b1b2sq+b4+a1+a4": "b",
        }
        assert parts[1] in descriptor_to_side
        return generator.group12c_clause(descriptor_to_side[parts[1]])
    if parts[0] == "GROUP12a" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert len(descriptor) == 4 and descriptor[0] == "c1c2sq"
        return generator.group12a_c_clause(tuple(descriptor[1:]))
    if parts[0] == "GROUP12b" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert len(descriptor) == 4 and descriptor[0] == "c1c2sq"
        return generator.group12b_c_clause(tuple(descriptor[1:]))
    if parts[0] == "GROUP1212a" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert (len(descriptor) == 4
                and descriptor[:2] == ["b1b2sq", "c1c2sq"])
        return generator.group1212a_clause(tuple(descriptor[2:]))
    if parts[0] == "GROUP1212b" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert (len(descriptor) == 4
                and descriptor[:2] == ["a1a2sq", "c1c2sq"])
        return generator.group1212b_clause(tuple(descriptor[2:]))
    if parts[0] == "UN" and len(parts) == 6:
        return generator.prop_clause(
            "UN", parts[1], int(parts[2]), int(parts[3]), int(parts[4]))
    raise AssertionError("no generator compiler for label " + repr(label))


def check_clause(key, generator_arms):
    clean_labels = clean.ARMS_BY_CLAUSE[key]
    generator_labels = tuple(row[2] for row in generator_arms)
    assert generator_labels == clean_labels, (key, generator_labels, clean_labels)
    for generator_row in generator_arms:
        assert generator_row == clean.ROW_BY_LABEL[generator_row[2]], (
            key, generator_row, clean.ROW_BY_LABEL[generator_row[2]])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("report")
    args = parser.parse_args()

    clean.build_static_system()
    with open(args.report, "r", encoding="utf-8") as handle:
        report = clean.load_json_strict(handle)

    static = generator_static_rows()
    for label, generator_row in static.items():
        assert clean.ROW_BY_LABEL[label] == generator_row, (
            label, generator_row, clean.ROW_BY_LABEL[label])

    used = set()
    path_labels = set()
    term_labels = set()
    for certificate in report["certificates"]:
        path_labels.update(certificate["path"])
        term_labels.update(term[0] for term in certificate["terms"])
    used.update(path_labels)
    used.update(term_labels)

    checked_dynamic_clauses = set()
    for label in sorted(used):
        verifier_row = clean.ensure_row_label(label)
        if label in static:
            assert static[label] == verifier_row
            continue
        key, arms = generator_dynamic_clause(label)
        assert any(row[2] == label for row in arms), (label, key)
        if key not in checked_dynamic_clauses:
            check_clause(key, arms)
            checked_dynamic_clauses.add(key)

    pow_counts = {}
    rejected_pow3a = 0
    for side, represented in (("a", "bc"), ("b", "ac"), ("c", "ab")):
        count = 0
        slots = tuple(f"{other}{index}"
                      for other in represented for index in range(1, 7))
        for held in itertools.combinations(slots, 4):
            allowed = (side != "a" or sum(
                clean.POW3A_TARGET_MASS_NUM.get(slot, 0)
                for slot in held) <= 14)
            if not allowed:
                try:
                    generator.pow3_clause(side, held)
                except AssertionError:
                    pass
                else:
                    raise AssertionError(("generator accepted unsafe POW3a", held))
                try:
                    clean.construct_pow3_clause(side, held)
                except clean.VerificationError:
                    rejected_pow3a += 1
                    continue
                raise AssertionError(("unsafe POW3a accepted", held))
            generator_key, generator_arms = generator.pow3_clause(side, held)
            clean_key, clean_arms = clean.construct_pow3_clause(side, held)
            assert generator_key == clean_key
            assert tuple(generator_arms) == tuple(clean_arms), (side, held)
            count += 1
        pow_counts[side] = count
    assert pow_counts == {"a": 486, "b": 495, "c": 495}
    assert rejected_pow3a == 9

    group_keys = []
    for group_side in "ab":
        generator_key, generator_arms = generator.group12c_clause(group_side)
        clean_key, clean_arms = clean.construct_group12c_clause(group_side)
        assert generator_key == clean_key
        assert tuple(generator_arms) == tuple(clean_arms), group_side
        group_keys.append(generator_key)

    group12a_count = 0
    for combo in itertools.combinations(generator.GROUP12A_C_SINGLETON_POOL, 3):
        singletons = (tuple(sorted(slot for slot in combo if slot[0] == "c"))
                      + tuple(sorted(slot for slot in combo if slot[0] == "b")))
        generator_key, generator_arms = generator.group12a_c_clause(singletons)
        clean_key, clean_arms = clean.construct_group12a_c_clause(singletons)
        assert generator_key == clean_key
        assert tuple(generator_arms) == tuple(clean_arms), singletons
        group12a_count += 1
    assert group12a_count == 120

    group12b_count = 0
    for combo in itertools.combinations(generator.GROUP12B_C_SINGLETON_POOL, 3):
        singletons = (tuple(sorted(slot for slot in combo if slot[0] == "c"))
                      + tuple(sorted(slot for slot in combo if slot[0] == "a")))
        generator_key, generator_arms = generator.group12b_c_clause(singletons)
        clean_key, clean_arms = clean.construct_group12b_c_clause(singletons)
        assert generator_key == clean_key
        assert tuple(generator_arms) == tuple(clean_arms), singletons
        group12b_count += 1
    assert group12b_count == 120

    group1212a_count = 0
    for combo in itertools.combinations(generator.GROUP1212A_SINGLETON_POOL, 2):
        singletons = tuple(sorted(combo, key=lambda slot: (slot[0], slot[1])))
        generator_key, generator_arms = generator.group1212a_clause(singletons)
        clean_key, clean_arms = clean.construct_group1212a_clause(singletons)
        assert generator_key == clean_key
        assert tuple(generator_arms) == tuple(clean_arms), singletons
        group1212a_count += 1
    assert group1212a_count == 28

    group1212b_count = 0
    for combo in itertools.combinations(generator.GROUP1212B_SINGLETON_POOL, 2):
        singletons = tuple(sorted(combo, key=lambda slot: (slot[0], slot[1])))
        generator_key, generator_arms = generator.group1212b_clause(singletons)
        clean_key, clean_arms = clean.construct_group1212b_clause(singletons)
        assert generator_key == clean_key
        assert tuple(generator_arms) == tuple(clean_arms), singletons
        group1212b_count += 1
    assert group1212b_count == 28

    family_counts = {}
    for label in used:
        family = clean.label_family(label)
        family_counts[family] = family_counts.get(family, 0) + 1
    print("USED_ROW_COMPILER_DIFFERENTIAL_PASS")
    print(f"used_distinct_labels={len(used)} path={len(path_labels)} "
          f"terms={len(term_labels)}")
    print(f"used_dynamic_clauses={len(checked_dynamic_clauses)}")
    print(f"family_counts={dict(sorted(family_counts.items()))}")
    print(f"pow3_exhaustive_counts={pow_counts} clauses={sum(pow_counts.values())} "
          f"arms={2 * sum(pow_counts.values())} rejected_pow3a={rejected_pow3a}")
    print(f"fixed_group12c_clauses={tuple(group_keys)} arms=6")
    print(f"group12a_c_exhaustive_clauses={group12a_count} "
          f"arms={3 * group12a_count}")
    print(f"group12b_c_exhaustive_clauses={group12b_count} "
          f"arms={3 * group12b_count}")
    print(f"group1212a_exhaustive_clauses={group1212a_count} "
          f"arms={4 * group1212a_count}")
    print(f"group1212b_exhaustive_clauses={group1212b_count} "
          f"arms={4 * group1212b_count}")


if __name__ == "__main__":
    main()
