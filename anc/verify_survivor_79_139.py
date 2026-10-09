#!/usr/bin/env python3
"""Independent exact replay of the proposed 79/139 S_ind survivor."""

from fractions import Fraction as F

import verify_witness_ind_20_37 as audit


def survivor():
    p = {"D": F(79, 139)}
    for s in "abc":
        p[s] = F(0)
        p[f"v{s}"] = F(0)
        for i in audit.RNG:
            p[f"{s}{i}"] = F(0)
    p.update({
        "a": F(73, 278), "a1": F(5, 278),
        "a4": F(67, 278), "a5": F(1, 278),
        "b": F(92, 278), "b3": F(91, 278), "b5": F(1, 278),
        "c": F(113, 278), "c1": F(112, 278), "vc": F(7, 278),
    })
    return p


audit.P = survivor()
audit.TARGET = audit.P["D"]
audit.DEN = 278
vals = audit.verify_base_geometry()
hb3, det, ps_min, ps_arg, cs_min, cs_arg = audit.verify_static_and_moment(vals)
scale, minima, argmins = audit.exact_scan_extended_un_cs_rm()
vals2 = {s: audit.side_scalars(s)[2] for s in "abc"}
spacing = {}
for e in "abc":
    o1, o2 = audit.SIDES[e]
    for y, z in ((o1, o2), (o2, o1)):
        for k in range(2, 7):
            spacing[(e, y, z, k)] = (
                audit.P[y] + audit.P[z] - audit.P[f"{z}{k}"]
                + max(F(0), vals2[e] - vals2[z] + audit.P[f"{z}{k}"]))
spacing_arg = min(spacing, key=spacing.get)
spacing_min = spacing[spacing_arg]
assert spacing_min < audit.P["D"]

print("EXACT_79_139_SURVIVOR_PASS")
print(f"D={audit.P['D']} gap_over_20_37={audit.P['D'] - F(20,37)}")
print(f"HB3={hb3}; DET={det}")
print(f"PS23 minimum={ps_min} at {ps_arg}")
print(f"CS4(exact-seven-safe) minimum={cs_min} at {cs_arg}")
print(f"Spacing CUTS survivor: minimum={spacing_min} at {spacing_arg}")
for name in minima:
    print(f"{name} minimum={F(minima[name], scale)} at {argmins[name]}")
