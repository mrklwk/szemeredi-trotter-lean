# Explicit Szemerédi–Trotter bounds over arbitrary fields

This proof-only Lean project establishes four explicit bounds for ordinary
point-line incidences. Let $K$ be a field, $P$ a finite set of points of $K^2$,
and $L$ a finite set of distinct affine lines in $K^2$. Write $m=\lvert P\rvert$,
$n=\lvert L\rvert$, and $I=\lvert\{(x,\ell)\in P\times L:x\in\ell\}\rvert$. The proved upper bounds are:

| Declaration in `Solution.lean` | Hypotheses beyond the configuration | Upper bound for `I` |
| --- | --- | --- |
| `IncidenceBounds.arbitrary_charZero` | $K$ has characteristic zero | $3(mn)^{2/3}+m+n$ |
| `IncidenceBounds.arbitrary_charP` | $K$ has characteristic $p>0$ | $3(mn)^{2/3}+m+n+\frac{2mn}{p}$ |
| `IncidenceBounds.subcritical` | $K$ has characteristic $p>0$ and $mn\le p^3$ | $3(mn)^{2/3}+m+n$ |
| `IncidenceBounds.prime_field` | $K=\mathbb{F}_p$, with $p$ prime (`ZMod p` in Lean) | $3(mn)^{2/3}+m+n+\frac{mn}{p}$ |

In positive characteristic, $p$ denotes the characteristic, not the cardinality
of the field. The first three results allow arbitrary fields, including infinite
fields and extension fields. The fourth result is stated over the prime field
`ZMod p`; its coefficient one on $mn/p$ is not asserted for general extension
fields. There is no size restriction in that fourth statement.

## What the formal statements mean

Points have type `Finset (K × K)`. Lines have type
`Finset (AffineSubspace K (K × K))`, with the explicit hypothesis
`∀ l ∈ L, Module.finrank K l.direction = 1`. This is the usual affine-line
condition, not an assumed incidence inequality. It includes vertical lines
and excludes empty and zero-dimensional affine subspaces. `Finset` removes
duplicates, so different descriptions of the same geometric line cannot be
counted repeatedly.

The incidence count in every public theorem is written directly as
`((P ×ˢ L).filter (fun z => z.1 ∈ z.2)).card`. Cardinalities are cast to
`ℝ`, and the exponent is `((2 : ℝ) / 3)`, not natural-number division.
Empty point or line sets are included. The positive-characteristic results
include characteristic two. The subcritical boundary is inclusive: $mn\le p^3$.
No finite, perfect, algebraically closed, generic-position or nonempty-field
configuration hypothesis is added to the general statements.

## Mathematical source and proof outline

The main source is the author's
[A Szemerédi–Trotter Theorem in Arbitrary Fields, arXiv:2609.27023v2](https://arxiv.org/abs/2609.27023v2).
This development adapts its polynomial-method incidence argument and tracks
explicit constants. The v2 comparison target is
$3(mn)^{2/3}+2m+n+\frac{2mn}{p}$, with the last term absent in characteristic
zero. The general theorems above save one $m$ term; the other two statements
record additional refinements. These stronger constants should not be
attributed verbatim to the cited v2 text.

The proof constructs the relevant polynomial spaces, controls exceptional
factors and multiplicities, counts incidences after slope normalization, and
optimizes the resulting degree bound. A generic coordinate map
$(x,y)\mapsto(tx+y,x)$ into the rational-function field $K(t)$ removes vertical
directions while preserving distinct points, distinct lines and incidences.
That step gives the improved linear term without assuming the original field
has a spare slope. A separate argument gives the subcritical range.

For a finite field of cardinality $q$, the auxiliary development proves the
finite-plane estimate $I\le\frac{mn}{q}+\sqrt{qmn}$ directly by line counts, pair
counts and a variance/Cauchy–Schwarz argument. This is the familiar numerical
bound associated with [Le Anh Vinh's finite-field incidence theorem](https://arxiv.org/abs/0711.4427);
the Lean proof does not assume that theorem. Over `ZMod p`, combining this
estimate with the subcritical theorem gives the prime-field result, including
the transition at $mn=p^3$.

These results are relevant to researchers in incidence geometry and additive
combinatorics who need explicit estimates and a checked account of the field
and characteristic dependence. This project does not claim that the leading
constant 3 is optimal or establish a priority claim for the refinements.
Applications from the paper are not formalized.

## Proof boundary and reproducibility

`Challenge.lean` states the four results independently. Its four deliberate
`sorry` holes are specification markers, not proofs. `Solution.lean` never
imports it. The complete proof development has no `sorry`, `admit`, or custom
axioms. Each final theorem uses only `propext`, `Classical.choice`, and
`Quot.sound`. `comparator.json` selects exactly the four declarations above.

The pinned environment is:

- Lean `leanprover/lean4:v4.35.0-rc2`, compiler commit
  `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- All other immutable dependency revisions are in `lake-manifest.json`.
- `scripts/verify-comparator.sh` is the unchanged official launcher from
  PalomarTemplate `2891de4c48955af824969a263d31b25e7a9a1406`.

With the pinned compiler and dependencies already available, use:

```sh
lean --version
python3 scripts/check-sources.py
lake exe cache get
lake --no-cache --wfail build
lake env lean -DwarningAsError=true Solution.lean
bash scripts/verify-comparator.sh
```

The last command requires Linux, `bwrap`, `python3`, and the bundled
`leanexport`, `leanchecker`, `nanoda_bin` and `con-ron` executables.
`scripts/check-sources.py` is a lexical precheck, including a regex comparison
of statement-header text. It does not compare elaborated Lean terms or establish
semantic identity; that is the role of Comparator. By default it prints JSON
without changing repository files. To save a report explicitly, use
`python3 scripts/check-sources.py --report build/source-check.json`.

`python3 scripts/verify-linux.py` records the build, axiom check and official
Comparator sequence with commands, exit codes, source hashes and logs.
It expects its environment to have been prepared separately.

## Verification and review status

This proof-only snapshot derives from audited release
`27d27da3c9c52c51ae8429020f39bc965eacb956`. Its 42 proof modules are
byte-identical to that release. Migration changed the environment from Lean
4.34.1 to 4.35.0-rc2; the Challenge's introductory status comment was refreshed.
The earlier source and audit evidence remain preserved.

The archived Linux run at `d80ac90c2a9c4316f9d2052300b607c14804cb36`
started without a project build directory. The source check, full build,
explicit final-theorem axiom check, and official Comparator all exited 0.
The Comparator accepted the proof using Lean, NanoDa and con-ron. The repeat
run at `eb95d6f0e79c65cf770a7b1e30e0eeaee0cd16f1` also passed; its
project build directory already existed. The 43 Lean files and seven
build/check inputs at documentation base
`d416282b3692a57c27baa034a0758d6abe22f3cf` match that repeat run byte for
byte. See `verification/` for checked logs, hashes and portable run summaries. The first run
differs from the base only in the Challenge status comment among Lean files.

Separate agent audits of the earlier mathematical checkpoints inspected the
statements, definitions and dependency proofs and performed fresh kernel
replay. These checks support the mathematical interpretation above. They do
not constitute human peer review or a Palomar editorial review. This release preparation changes documentation and the source-checker output
policy, while preserving Lean sources and the official Comparator launcher.
It does not record a new compiler run. The checker revision has separate local
packaging tests; it is not one of the byte-identical inputs described above.

The author and responsible maintainer are recorded in `formalization.yaml`,
with AI contributions disclosed separately. This release is prepared for
publication as `mrklwk/szemeredi-trotter-lean`. Palomar verification and editorial
review remain pending. Its current
[agent instructions](https://submit.palomar-registry.org/llms.txt)
require the complete reusable mechanical workflow to pass on the exact public
commit before intake. The recorded standalone Comparator pass is separate
supporting evidence. Permanent registration requires a later decision on the
actual returned review.

The supplied run summaries omit machine-local filesystem locations. The
underlying command-output logs are unchanged, and their recorded hashes match.
Private operational records and correspondence are excluded from this package.
The source-checker revision has not been rerun on Linux; its local behavior
checks do not replace the recorded proof verification or final preflight.

## License and provenance

Original proof code and project material are licensed under **AGPL-3.0-only**;
see `LICENSE`. The paper is excluded from this repository and its license
grant. Third-party material retains its upstream license; see
`THIRD_PARTY_NOTICES.md`. Earlier repository snapshots are not relicensed.

`formalization.yaml` uses the legacy identifier `AGPL-3.0`, matching the exact
output of Palomar's pinned licensee 10.0.0 detector. The recorded license check
passes with that spelling. This compatibility spelling does not broaden the
actual grant to later license versions; the license text is unchanged.

The author supplied the mathematical source and directed the work. Claude and
Codex developed the formal proofs; Codex assembled the refined bounds and
package. The metadata distinguishes the mathematical source author, confirmed
human formalization roles, AI assistance, and review status. Exact session
model revisions are not reconstructed from incomplete records.

