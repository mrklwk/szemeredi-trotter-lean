# Third-party notices

The original proof development and original project material in this snapshot
are licensed under AGPL-3.0-only, as approved by Mark Lewko on 2026-10-06.
The mathematical paper is not included and is not covered by that grant.

## Official Comparator launcher

`scripts/verify-comparator.sh` is copied without modification from
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate) commit
`2891de4c48955af824969a263d31b25e7a9a1406`, path
`scripts/verify-comparator.sh`. This file retains its upstream Apache-2.0
license, reproduced in `third_party/PalomarTemplate.LICENSE`. No upstream
copyright or attribution notice has been removed. Its exact hash and source URL
are recorded in `verification/upstream-pins.json`.

## External dependencies and verification executables

Lean, mathlib and the other packages are external pinned dependencies, not
vendored into this source snapshot. Their own license files remain in their
downloaded distributions and checkouts. Dependency revisions are recorded in
`lake-manifest.json`. The Lean distribution bundles the Comparator and proof
checkers; the distribution is retained with its upstream notices.

The pinned mathlib, plausible, LeanSearchClient, importGraph, proofwidgets,
aesop, Qq and batteries checkouts carry Apache-2.0 license texts. Cli carries
the MIT license, including its copyright notice. Exact license-file hashes are
recorded in `verification/dependency-licenses.json`; no dependency source or
binary is included in this repository's source archive.

The Apache-2.0 script remains Apache-2.0 within this AGPLv3 project. GNU's
[license compatibility guidance](https://www.gnu.org/licenses/license-compatibility.en.html)
states that GNU licenses of version 3 or later can incorporate Apache-2.0
material while preserving its notices. The Apache Software Foundation's
[compatibility guidance](https://www.apache.org/licenses/GPL-compatibility.html)
also explains the one-way Apache-2.0 to GPLv3 compatibility. These sources were
checked during preparation; upstream notices are preserved rather than replaced.

## License text

The unmodified AGPL-3.0-only license text comes from SPDX license-list-data
commit `31ba1a50e5397e00a304dbadc76531740e89ee48`,
`text/AGPL-3.0-only.txt`. Its source URL and hash are recorded alongside the
other upstream pins.
