#!/usr/bin/env python3
"""Split an exact-tree frontier and merge independently completed shards.

The search reports are only work queues.  Mathematical acceptance is always
delegated to verify_tree_report_clean.py after the merge.
"""

import argparse
import copy
import json


def load(path):
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def dump(path, obj):
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(obj, handle, indent=2, sort_keys=True)


def split_report(source, prefix, nshards):
    report = load(source)
    assert not report["complete"]
    assert not report["survivors"]
    assert report["stats"]["bad_cert"] == 0
    frontier = report["open_stack"]
    assert frontier and nshards >= 2
    pieces = [frontier[i::nshards] for i in range(nshards)]
    assert all(pieces)
    outputs = []
    for i, piece in enumerate(pieces):
        shard = copy.deepcopy(report)
        shard["open_stack"] = piece
        shard["complete"] = False
        shard["elapsed_s"] = 0.0
        shard["stats"]["nodes"] = 0
        shard["stats"]["open"] = len(piece)
        path = f"{prefix}.{i}.json"
        dump(path, shard)
        outputs.append(path)
    meta = {
        "source": source,
        "base_certificate_count": len(report["certificates"]),
        "frontier_count": len(frontier),
        "shards": outputs,
    }
    dump(prefix + ".meta.json", meta)
    print(json.dumps(meta, indent=2, sort_keys=True))


def trie_stats(certificates):
    root = {"children": {}, "cert": False}
    seen = set()
    for cert in certificates:
        path = tuple(cert["path"])
        assert path not in seen
        seen.add(path)
        node = root
        for label in path:
            assert not node["cert"]
            node = node["children"].setdefault(
                label, {"children": {}, "cert": False})
        assert not node["cert"] and not node["children"]
        node["cert"] = True

    def walk(node, depth=0):
        if node["cert"]:
            assert not node["children"]
            return 1, 0, depth
        assert node["children"]
        leaves = 0
        internal = 1
        max_depth = depth
        for child in node["children"].values():
            ll, ii, dd = walk(child, depth + 1)
            leaves += ll
            internal += ii
            max_depth = max(max_depth, dd)
        return leaves, internal, max_depth

    return walk(root)


def merge_reports(source, output, shard_paths):
    original = load(source)
    assert original["complete"] is False
    assert original["survivors"] == []
    assert original["stats"]["bad_cert"] == 0
    base = original["certificates"]
    frontier = [tuple(item["path"]) for item in original["open_stack"]]
    assert frontier and len(frontier) == len(set(frontier))
    for i, left in enumerate(frontier):
        for right in frontier[i + 1:]:
            assert not (left == right[:len(left)] or
                        right == left[:len(right)])
    owner = {path: None for path in frontier}
    merged = list(base)
    elapsed = float(original.get("elapsed_s", 0.0))
    final_system = None
    final_flags = None
    for shard_index, path in enumerate(shard_paths):
        shard = load(path)
        assert shard["complete"] is True
        assert shard["open_stack"] == [] and shard["survivors"] == []
        assert shard["stats"]["bad_cert"] == 0
        assert shard["target"] == original["target"]
        assert shard["certificates"][:len(base)] == base
        used_roots = set()
        for cert in shard["certificates"][len(base):]:
            cert_path = tuple(cert["path"])
            matches = [root for root in frontier
                       if cert_path[:len(root)] == root]
            assert len(matches) == 1
            used_roots.add(matches[0])
        assert used_roots
        for root in used_roots:
            assert owner[root] is None
            owner[root] = shard_index
        if final_system is None:
            final_system = shard["system"]
            final_flags = shard["search_flags"]
        else:
            assert shard["system"] == final_system
            assert shard["search_flags"] == final_flags
        merged.extend(shard["certificates"][len(base):])
        elapsed += float(shard.get("elapsed_s", 0.0))
    assert all(shard_index is not None for shard_index in owner.values())
    leaves, internal, max_depth = trie_stats(merged)
    assert leaves == len(merged)
    out = copy.deepcopy(original)
    out.update({
        "system": final_system,
        "search_flags": final_flags,
        "complete": True,
        "elapsed_s": elapsed,
        "certificates": merged,
        "survivors": [],
        "open_stack": [],
    })
    upper = sum(c["kind"] == "upper" for c in merged)
    infeas = sum(c["kind"] == "infeas" for c in merged)
    out["stats"] = {
        "nodes": leaves + internal,
        "upper_exact": upper,
        "infeas_exact": infeas,
        "bad_cert": 0,
        "survivors": 0,
        "open": 0,
        "max_depth": max_depth,
    }
    dump(output, out)
    print(json.dumps({"output": output, "leaves": leaves,
                      "internal": internal, "max_depth": max_depth},
                     indent=2, sort_keys=True))


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    ps = sub.add_parser("split")
    ps.add_argument("source")
    ps.add_argument("prefix")
    ps.add_argument("nshards", type=int)
    pm = sub.add_parser("merge")
    pm.add_argument("source")
    pm.add_argument("output")
    pm.add_argument("shards", nargs="+")
    args = parser.parse_args()
    if args.command == "split":
        split_report(args.source, args.prefix, args.nshards)
    else:
        merge_reports(args.source, args.output, args.shards)


if __name__ == "__main__":
    main()
