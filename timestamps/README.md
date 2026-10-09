# Timestamps

[OpenTimestamps](https://opentimestamps.org) proofs for the assets of release `v1`.
Each proof commits to the SHA-256 of the file below.

| file | SHA-256 |
|---|---|
| `abc-exceptional-set-20over37-v1.pdf` | `f60d9040e771674db9fa403b0d933367dc548f63f75455366ba2906659f058ca` |
| `abc-exceptional-set-20over37-v1.tar.gz` | `28872252416322a4929c41df83fe820da905835cd618317c134970eff832c7b6` |

To verify, download the release asset into this directory and run

    pip install opentimestamps-client
    ots verify timestamps/<file>.ots
