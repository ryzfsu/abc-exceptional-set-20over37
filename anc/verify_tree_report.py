#!/usr/bin/env python3
"""Exact replay and OR-coverage audit for a dynamic_tree_ind JSON report.

No floating-point value from the search is trusted.  This first verifier
reuses the exact row constructors from dynamic_tree_ind; the separate
audit_clause_compiler.py checks those constructors against the closed-form
families in Fraction arithmetic.
"""

import argparse
import json
from fractions import Fraction as F

import dynamic_tree_ind as rows


TARGET = F(20, 37)
ZERO = {v: F(0) for v in rows.VARS}


row_by_label = {}
clause_by_arm = {}
arms_by_clause = {}
base_labels = set()


def register_row(r, is_base=False):
    d, rhs, label = r
    assert label and label not in row_by_label
    row_by_label[label] = (d, rhs, label)
    if is_base:
        base_labels.add(label)


def register_clause(key, arms):
    labels = tuple(a[2] for a in arms)
    old = arms_by_clause.get(key)
    if old is not None:
        assert old == labels
        return
    arms_by_clause[key] = labels
    for arm in arms:
        register_row(arm)
        clause_by_arm[arm[2]] = key


for r in rows.BASE:
    register_row(r, is_base=True)
for key, aa in rows.ARCH + rows.GEOMETRY + rows.DET + rows.SPACING:
    register_clause(key, aa)
for v in rows.VARS:
    register_row(rows.row({v: -1}, 0, "nonneg:" + v))


def ensure_dynamic(label):
    if label in row_by_label:
        return
    p = label.split(":")
    if p[0] == "PS" and len(p) == 4:
        register_clause(*rows.ps_clause(p[1], int(p[2])))
    elif p[0] == "CS4" and len(p) == 5:
        held = tuple(p[3].split(",")) if p[3] else ()
        register_clause(*rows.cs4_clause(p[1], int(p[2]), held))
    elif p[0] in ("POW3a", "POW3b", "POW3c") and len(p) == 3:
        held = tuple(p[1].split(",")) if p[1] else ()
        register_clause(*rows.pow3_clause(p[0][-1], held))
    elif p[0] == "GROUP12c" and len(p) == 3:
        descriptor_to_side = {
            "a1a2sq+a4+b1+b4": "a",
            "b1b2sq+b4+a1+a4": "b",
        }
        assert p[1] in descriptor_to_side
        assert p[2] in ("S", "avg", "gate")
        register_clause(*rows.group12c_clause(descriptor_to_side[p[1]]))
    elif p[0] == "GROUP12a" and len(p) == 3:
        descriptor = p[1].split("+")
        assert len(descriptor) == 4 and descriptor[0] == "c1c2sq"
        assert p[2] in ("S", "avg", "gate")
        register_clause(*rows.group12a_c_clause(tuple(descriptor[1:])))
    elif p[0] == "GROUP12b" and len(p) == 3:
        descriptor = p[1].split("+")
        assert len(descriptor) == 4 and descriptor[0] == "c1c2sq"
        assert p[2] in ("S", "avg", "gate")
        register_clause(*rows.group12b_c_clause(tuple(descriptor[1:])))
    elif p[0] == "GROUP1212a" and len(p) == 3:
        descriptor = p[1].split("+")
        assert (len(descriptor) == 4
                and descriptor[:2] == ["b1b2sq", "c1c2sq"])
        assert p[2] in ("S", "avg", "gate-b", "gate-c")
        register_clause(*rows.group1212a_clause(tuple(descriptor[2:])))
    elif p[0] == "GROUP1212b" and len(p) == 3:
        descriptor = p[1].split("+")
        assert (len(descriptor) == 4
                and descriptor[:2] == ["a1a2sq", "c1c2sq"])
        assert p[2] in ("S", "avg", "gate-a", "gate-c")
        register_clause(*rows.group1212b_clause(tuple(descriptor[2:])))
    elif p[0] in rows.FORMS and len(p) == 6:
        register_clause(*rows.prop_clause(p[0], p[1], int(p[2]),
                                          int(p[3]), int(p[4])))
    else:
        raise AssertionError(f"unknown row label: {label}")
    assert label in row_by_label


def check_cert(cert):
    path = set(cert["path"])
    coeff = dict(ZERO)
    rhs = F(0)
    mu_sum = F(0)
    for label, smu in cert["terms"]:
        ensure_dynamic(label)
        mu = F(smu)
        assert mu > 0
        d, brhs, _ = row_by_label[label]
        if label not in base_labels and not label.startswith("nonneg:"):
            assert label in path, ("scope leak", label)
        for v, a in d.items():
            coeff[v] += mu * a
        rhs += mu * brhs
        mu_sum += mu
    assert rhs == F(cert["rhs"])
    if cert["kind"] == "upper":
        assert coeff == {**ZERO, "D": F(1)}
        assert rhs <= TARGET
    elif cert["kind"] == "infeas":
        assert coeff == ZERO
        assert mu_sum == 1
        assert rhs < 0
    else:
        raise AssertionError(cert["kind"])


def build_trie(certs):
    root = {"children": {}, "cert": None}
    for i, cert in enumerate(certs):
        node = root
        for label in cert["path"]:
            ensure_dynamic(label)
            node = node["children"].setdefault(
                label, {"children": {}, "cert": None})
        assert node["cert"] is None
        node["cert"] = i
    return root


def check_coverage(node):
    children = node["children"]
    if node["cert"] is not None:
        assert not children, "certified leaf has descendants"
        return 1, 0
    assert children, "uncovered prefix"
    labels = set(children)
    for label in labels:
        ensure_dynamic(label)
    keys = {clause_by_arm[label] for label in labels}
    assert len(keys) == 1, ("mixed clauses at node", keys)
    key = next(iter(keys))
    assert labels == set(arms_by_clause[key]), (
        "missing/extra OR arms", key, labels, arms_by_clause[key])
    leaves = 0
    internals = 1
    for child in children.values():
        l, n = check_coverage(child)
        leaves += l
        internals += n
    return leaves, internals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("report")
    args = ap.parse_args()
    report = json.load(open(args.report))
    assert report["target"] == str(TARGET)
    assert report["complete"] is True
    assert report["stats"]["bad_cert"] == 0
    assert report["stats"]["survivors"] == 0
    assert report["stats"]["open"] == 0
    assert report["survivors"] == []
    certs = report["certificates"]
    for cert in certs:
        check_cert(cert)
    trie = build_trie(certs)
    leaves, internal = check_coverage(trie)
    assert leaves == len(certs)
    print("EXACT_TREE_REPORT_PASS")
    print(f"certified_leaves={leaves} internal_nodes={internal} "
          f"search_nodes={report['stats']['nodes']}")


if __name__ == "__main__":
    main()
