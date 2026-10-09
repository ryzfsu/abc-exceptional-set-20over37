#!/usr/bin/env python3
"""Upgrade report metadata and reinsert exact survivors after adding rows.

The input report is never overwritten.  Every path arm is reconstructed from
the current exact clause compiler, and the resulting serialized fixed rows are
checked against their labels before a fresh resumable report is written.
"""

import argparse
import json

import dynamic_tree_ind as rows


STATIC = {}
for _key, arms in rows.ARCH + rows.GEOMETRY + rows.DET + rows.SPACING:
    for arm in arms:
        STATIC[arm[2]] = arm


def dynamic_clause(label):
    parts = label.split(":")
    if parts[0] == "PS" and len(parts) == 4:
        return rows.ps_clause(parts[1], int(parts[2]))
    if parts[0] == "CS4" and len(parts) == 5:
        return rows.cs4_clause(parts[1], int(parts[2]),
                               tuple(parts[3].split(",")))
    if parts[0] in ("POW2a", "POW2b", "POW2c",
                    "POW3a", "POW3b", "POW3c") and len(parts) == 3:
        return rows.pow_clause(int(parts[0][3]), parts[0][-1],
                               tuple(parts[1].split(",")))
    if parts[0] == "MIX3c" and len(parts) == 3:
        return rows.mix3c_fiveblock_clause()
    if parts[0] == "GROUP12c" and len(parts) == 3:
        descriptor_to_side = {
            "a1a2sq+a4+b1+b4": "a",
            "b1b2sq+b4+a1+a4": "b",
        }
        assert parts[1] in descriptor_to_side, label
        return rows.group12c_clause(descriptor_to_side[parts[1]])
    if parts[0] == "GROUP12a" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert len(descriptor) == 4 and descriptor[0] == "c1c2sq", label
        return rows.group12a_c_clause(tuple(descriptor[1:]))
    if parts[0] == "GROUP12b" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert len(descriptor) == 4 and descriptor[0] == "c1c2sq", label
        return rows.group12b_c_clause(tuple(descriptor[1:]))
    if parts[0] == "GROUP1212a" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert (len(descriptor) == 4
                and descriptor[:2] == ["b1b2sq", "c1c2sq"]), label
        return rows.group1212a_clause(tuple(descriptor[2:]))
    if parts[0] == "GROUP1212b" and len(parts) == 3:
        descriptor = parts[1].split("+")
        assert (len(descriptor) == 4
                and descriptor[:2] == ["a1a2sq", "c1c2sq"]), label
        return rows.group1212b_clause(tuple(descriptor[2:]))
    if parts[0] in rows.FORMS and len(parts) == 6:
        return rows.prop_clause(parts[0], parts[1], int(parts[2]),
                                int(parts[3]), int(parts[4]))
    raise AssertionError(f"unknown dynamic arm label: {label}")


def reconstruct_arm(label):
    if label in STATIC:
        return STATIC[label]
    key, arms = dynamic_clause(label)
    matches = [arm for arm in arms if arm[2] == label]
    assert len(matches) == 1, (key, label, [arm[2] for arm in arms])
    return matches[0]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input_report")
    parser.add_argument("output_report")
    args = parser.parse_args()
    assert args.input_report != args.output_report

    with open(args.input_report, encoding="utf-8") as handle:
        report = json.load(handle)
    assert report["stats"]["bad_cert"] == 0
    if report["complete"]:
        assert report["survivors"] == [] and report["open_stack"] == []

    restored = []
    for survivor in report["survivors"]:
        assert survivor["kind"] == "NO_VIOLATED_CLAUSE", survivor
        path = survivor["path"]
        fixed = [reconstruct_arm(label) for label in path]
        assert [arm[2] for arm in fixed] == path
        restored.append({
            "fixed": [rows.row_to_json(arm) for arm in fixed],
            "path": path,
        })

    report["open_stack"].extend(restored)
    report["survivors"] = []
    report["stats"]["survivors"] = 0
    # A survivor was previously counted as a processed terminal node.  Once
    # it is restored to the frontier it is no longer processed; the resumed
    # search will increment the node count again when it pops this leaf.
    report["stats"]["nodes"] -= len(restored)
    report["stats"]["open"] = len(report["open_stack"])
    report["system"] = (
        "base+ARCH-value-cover+HB3+13geom+DET+Spacing+allPS23+CS4regular"
        "+POW3abc-regular(a-target-safe)"
        "+GROUP12c(a/b)+GROUP12ab(c;all3)+GROUP1212ab(all2) grouped rows"
        "+extended-UN(regular-free)")
    report["search_flags"].pop("pow2abc_regular", None)
    report["search_flags"]["group12c_ab12"] = True
    report["search_flags"].pop("group12a_c12", None)
    report["search_flags"].pop("group12a_c12_b45", None)
    report["search_flags"]["group12a_c12_all3"] = True
    report["search_flags"]["group12b_c12_all3"] = True
    report["search_flags"]["group1212a_all2"] = True
    report["search_flags"]["group1212b_all2"] = True
    report["search_flags"].pop("group12c_b12", None)
    report["search_flags"].pop("mix3c_fiveblock", None)
    report["search_flags"]["arch_value_cover"] = True
    report["search_flags"]["pow3c_regular"] = True

    with open(args.output_report, "w", encoding="utf-8") as handle:
        json.dump(report, handle, indent=2, sort_keys=True)
    print(f"RESTORED_SURVIVORS={len(restored)} OPEN={len(report['open_stack'])} "
          f"COMPLETE={report['complete']}")


if __name__ == "__main__":
    main()
