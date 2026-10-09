#!/usr/bin/env python3
"""Exact audit of the 6/11 candidate returned by the regular-free tree."""

from fractions import Fraction as F

import verify_witness_ind_20_37 as audit


def survivor():
    p = {"D": F(6, 11)}
    for side in "abc":
        p[side] = F(0)
        p[f"v{side}"] = F(0)
        for index in audit.RNG:
            p[f"{side}{index}"] = F(0)
    p.update({
        "a": F(3, 11), "a3": F(1, 11), "a4": F(2, 11),
        "b": F(5, 11), "b1": F(2, 11), "b3": F(3, 11),
        "c": F(3, 11), "c1": F(1, 11), "c5": F(2, 11),
    })
    return p


audit.P = survivor()
audit.TARGET = audit.P["D"]
audit.DEN = 11
values = audit.verify_base_geometry()
hb3, det, ps_min, ps_arg, cs_min, cs_arg = audit.verify_static_and_moment(values)
scale, minima, argmins = audit.exact_scan_extended_un_cs_rm()
side_values = {side: audit.side_scalars(side)[2] for side in "abc"}
spacing = {}
for equation_side in "abc":
    other1, other2 = audit.SIDES[equation_side]
    for y, z in ((other1, other2), (other2, other1)):
        for k in range(2, 7):
            spacing[(equation_side, y, z, k)] = (
                audit.P[y] + audit.P[z] - audit.P[f"{z}{k}"]
                + max(F(0), side_values[equation_side] - side_values[z]
                      + audit.P[f"{z}{k}"]))
spacing_arg = min(spacing, key=spacing.get)
spacing_min = spacing[spacing_arg]

print("EXACT_6_11_CANDIDATE_AUDIT_PASS")
print(f"D={audit.P['D']} gap_over_20_37={audit.P['D'] - F(20, 37)}")
print(f"values={side_values}; HB3={hb3}; DET={det}")
print(f"PS23 minimum={ps_min} at {ps_arg}")
print(f"CS4 minimum={cs_min} at {cs_arg}")
print(f"Spacing minimum={spacing_min} at {spacing_arg}")
for name in minima:
    value = F(minima[name], scale)
    relation = "CUT" if value < audit.P["D"] else "PASS"
    print(f"{name} minimum={value} at {argmins[name]} [{relation}]")
