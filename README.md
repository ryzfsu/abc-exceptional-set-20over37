# Cubic sieves, a primitive-ratio cut and a 20/37 bound for the abc exceptional set

Ruiyi Zhang

Let `N_1(X)` count the abc triples `(a,b,c)` in `[1,X]^3` with `rad(abc) < c`.
The manuscript proves

    N_1(X) <<_eps X^{20/37+eps}.

The previous bound proved in full was `X^{13/20+eps}`. The proof keeps the anatomic
reduction of Bernert, Browning, Lichtman and Teräväinen and adds five families of rows:
an archimedean cover, a row from Heath-Brown's uniform bound for diagonal cubic curves,
spacing clauses, cubic-sieve rows and moment rows. An exact Farkas certificate with
394,633 leaves gives the exponent `20/37` for the box count; on each leaf the multipliers
sum to at most `586/201`.

## Contents

- `main.tex`, `main.pdf` (41 pages)
- `anc/` - the certificate and the checking programs whose SHA-256 values are printed in
  the paper (Table C.2), with `MANIFEST.sha256`. See `anc/REPRODUCTION.md`.
- `anc/replay_output/` - a fresh run of `run_verification.sh`, byte-identical to
  `anc/FROZEN_VERIFICATION.stdout`, and its environment.
- `SHA256SUMS`

## Build

    pdflatex main.tex
    pdflatex main.tex

## Checks

Python 3 with NumPy and SciPy, and xz. The decompressed report is about 1 GB.

    cd anc
    sha256sum -c MANIFEST.sha256
    xz -dc final-report.raw.json.xz > raw-report.json
    sha256sum -c RAW_REPORT.sha256
    python3 normalize_completed_report.py raw-report.json final-report.json
    sha256sum -c NORMALIZED_REPORT.sha256
    ./run_verification.sh final-report.json > REPLAY_VERIFICATION.stdout
    cmp FROZEN_VERIFICATION.stdout REPLAY_VERIFICATION.stdout
