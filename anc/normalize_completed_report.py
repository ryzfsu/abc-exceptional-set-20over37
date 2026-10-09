#!/usr/bin/env python3
"""Recompute exact trie statistics for a completed search report.

This writes a fresh report and leaves the raw generator output untouched.
Acceptance is still delegated to verify_tree_report_clean.py.
"""

import argparse
import copy
import json

from shard_merge_tree import trie_stats


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input_report")
    parser.add_argument("output_report")
    args = parser.parse_args()
    assert args.input_report != args.output_report

    with open(args.input_report, encoding="utf-8") as handle:
        raw = json.load(handle)

    assert raw["complete"] is True
    assert raw["open_stack"] == []
    assert raw["survivors"] == []
    assert raw["stats"]["bad_cert"] == 0

    certificates = raw["certificates"]
    leaves, internal, max_depth = trie_stats(certificates)
    assert leaves == len(certificates)
    upper = sum(cert["kind"] == "upper" for cert in certificates)
    infeas = sum(cert["kind"] == "infeas" for cert in certificates)
    assert upper + infeas == leaves

    normalized = copy.deepcopy(raw)
    normalized["stats"] = {
        "nodes": leaves + internal,
        "upper_exact": upper,
        "infeas_exact": infeas,
        "bad_cert": 0,
        "survivors": 0,
        "open": 0,
        "max_depth": max_depth,
    }
    with open(args.output_report, "w", encoding="utf-8") as handle:
        json.dump(normalized, handle, indent=2, sort_keys=True)

    print(json.dumps({
        "input": args.input_report,
        "output": args.output_report,
        "raw_stats": raw["stats"],
        "normalized_stats": normalized["stats"],
        "leaves": leaves,
        "internal": internal,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
