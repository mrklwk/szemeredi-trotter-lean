# Verification evidence in this candidate

The two Linux subdirectories contain unchanged command-output logs and portable
summaries of archived runs. Their logs retain the original recorded SHA-256
values. The summaries remove machine-local interpreter/cache locations and label
that transformation. No run was repeated while preparing this candidate.

The initial run at `d80ac90c2a9c4316f9d2052300b607c14804cb36` had no
project build directory. The repeat at
`eb95d6f0e79c65cf770a7b1e30e0eeaee0cd16f1` reused one. Both used Lean
4.35.0-rc2, compiler `11acb17ec6b07a8f9e9173e6845197929540936b`, and mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Commands, exit codes, dependency
revisions, theorem axiom output and kernel acceptance are retained.

`unchanged-proof-inputs.json` is the historical comparison from documentation
base `d416282b3692a57c27baa034a0758d6abe22f3cf` to the repeat run. It does
not claim that every script in this candidate is unchanged: the source checker
now prints to stdout by default and accepts an explicit report destination.
`preparation.json` records that difference and confirms all 43 Lean files are
unchanged. The source checker is lexical; semantic agreement is tested by the
actual Comparator, not inferred from its regular expressions.

The root license, third-party license and official Comparator launcher are
unchanged. `upstream-pins.json` uses repository-relative names for included
files; `dependency-licenses.json` records external license hashes. The portable
license-check summary preserves the result and exact detector version while
omitting its machine-local invocation path.

Private operational records, personal correspondence and unrelated project
material are not part of this source candidate. Its approved repository destination is `mrklwk/szemeredi-trotter-lean`. The
author and responsible maintainer are confirmed in the metadata. The exact
commit is determined by the containing Git snapshot. That public snapshot
still needs the complete Palomar preflight before intake.
