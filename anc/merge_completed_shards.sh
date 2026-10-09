#!/usr/bin/env bash
set -euo pipefail

# Merge nested shards from their immutable parent frontiers.  Each level
# removes its shared certificate prefix exactly once and recomputes trie
# statistics before the next level is admitted.

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group4_shard.0sub.0leaf.0.json \
  dynamic_tree_arch_group4_shard.0sub.0leaf.0final.json \
  dynamic_tree_arch_group4_shard.0sub.0leaf.0root.0.json \
  dynamic_tree_arch_group4_shard.0sub.0leaf.0root.1.json

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group4_shard.0sub.0.json \
  dynamic_tree_arch_group4_shard.0sub.0final.json \
  dynamic_tree_arch_group4_shard.0sub.0leaf.0final.json \
  dynamic_tree_arch_group4_shard.0sub.0leaf.1.json

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group4_shard.0sub.1.json \
  dynamic_tree_arch_group4_shard.0sub.1final.json \
  dynamic_tree_arch_group4_shard.0sub.1leaf.0.json \
  dynamic_tree_arch_group4_shard.0sub.1leaf.1.json

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group4_shard.0.json \
  dynamic_tree_arch_group4_shard.0final.json \
  dynamic_tree_arch_group4_shard.0sub.0final.json \
  dynamic_tree_arch_group4_shard.0sub.1final.json

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group4_shard.1sub.1.json \
  dynamic_tree_arch_group4_shard.1sub.1final.json \
  dynamic_tree_arch_group4_shard.1sub.1leaf.0.json \
  dynamic_tree_arch_group4_shard.1sub.1leaf.1.json

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group4_shard.1base.json \
  dynamic_tree_arch_group4_shard.1final.json \
  dynamic_tree_arch_group4_shard.1sub.0.json \
  dynamic_tree_arch_group4_shard.1sub.1final.json

python3 shard_merge_tree.py merge \
  dynamic_tree_arch_group_checkpoint.json \
  dynamic_tree_arch_group_full_merged.raw.json \
  dynamic_tree_arch_group4_shard.0final.json \
  dynamic_tree_arch_group4_shard.1final.json

python3 normalize_completed_report.py \
  dynamic_tree_arch_group_full_merged.raw.json \
  dynamic_tree_arch_group_full_merged.normalized.json
