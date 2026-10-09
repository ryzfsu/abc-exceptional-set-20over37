# Reproducing the unconditional `20/37` certificate

Date: 20260719

This package contains the exact finite certificate of the paper
used in the proof of

\[
N_1(X)\ll_\varepsilon X^{20/37+\varepsilon},
\]

together with the programs that check it.

## Resource discipline

The reports are compressed because the JSON trie is large.  Copy this
directory to a dedicated local directory under `/tmp` before decompressing
or verifying it.  Do not perform the sustained read/write workload on the
NFS-backed repository.

## Exact replay

From a local copy of this directory, run:

```bash
set -euo pipefail

sha256sum -c MANIFEST.sha256
xz -dc final-report.raw.json.xz > raw-report.json
sha256sum -c RAW_REPORT.sha256

python3 normalize_completed_report.py raw-report.json final-report.json
sha256sum -c NORMALIZED_REPORT.sha256

./run_verification.sh final-report.json | tee REPLAY_VERIFICATION.stdout
cmp FROZEN_VERIFICATION.stdout REPLAY_VERIFICATION.stdout
```

The two report checksum checks prove that decompression recovers the exact
merged raw bytes and that deterministic normalization reproduces the exact
promoted report bytes.  The stdout comparison proves that a fresh execution
reproduces the frozen verifier transcript byte for byte.  Only the raw report
is stored because the normalized report differs only in recomputed trie
statistics; `NORMALIZED_REPORT.sha256` freezes the latter as an exact object
without duplicating the large certificate payload.

`verify_tree_report_clean.py` is the promotion authority.  It uses only the
Python standard library and independently reconstructs every allowed row
from typed labels, replays every rational Farkas certificate, and proves
full-arm coverage of the prefix-free certificate trie.  It also rejects all
46 report mutations.  The generator-linked verifier and compiler
differential are additional checks, not substitutes for the clean verifier.

`verify_witness_clean.py` independently exhausts the frozen row universe at
the exact `20/37` witness and rejects all 19 witness mutations.  The remaining
standalone scripts reproduce the discovery canaries and grouped-row faces.

## Provenance boundary

The package contains the compact merged raw and normalized reports, not the
intermediate search shards. The merged report is mathematically
self-contained: acceptance does not trust the generator.
