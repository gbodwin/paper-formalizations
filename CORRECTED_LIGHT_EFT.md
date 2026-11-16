# Corrected Light Edge Fault Tolerant Graph Spanners

This edition follows the corrected November 2026 Dropbox paper. It preserves
the earlier formalized sampling/controller variants in their original namespaces
and adds the accepted construction and constants in `Corrected*` modules.

The main cloud endpoint is
`LightEFTSpanners.CorrectedCloud.corrected_theorem34_every_order`, in
`LightEFTSpanners/CorrectedCloudPaddingLowerBound.lean`. For real `c ≥ 2`, integer
`f ≥ 1`, real stretch `t ≥ 1`, and every prescribed order
`n ≥ 2 floor(c f)`, it constructs an actual graph on `Fin n` with positive input
edge weights. Every actual `f`-EFT `t`-spanner has competitive lightness at least
`lambda(floor(n/(c f)), t+1)/(4 c)` against every actual minimum
`floor(c f)`-fault connectivity preserver. The exact-order extension uses isolated
padding, consistent with the componentwise fault semantics. The original cloud
family is also available without padding.

`CorrectedLowCompetition.corrected_low_competition_real_every_order` gives
the lower bound `n/(32 f^2 t)` for every `n ≥ 2`, `f ≥ 1`, real `t ≥ 1`, and
competition budget at most `2 f - 1`. Its introduction specialization is
`n/(96 f^2 k)` uniformly for `0 < epsilon ≤ 1/k`. The small-order unit-edge
fallback and the cycle-family padding are both proved, so this statement has
no unbounded-order-only or epsilon-dependent-onset qualification.

The construction includes actual internal cliques, two cyclic matchings per
core tree edge, all-fault connectivity, certificate weight accounting, forced
cross-bundle retention, deletion of internal steps when projecting walks, and
the exact-order extremal supremum, including its weighted-girth boundary two.

`CorrectedSampling*` and `CorrectedVoting*` implement the accepted rate `1/f`,
accuracy `1/16`, vote threshold `1/8`, and Hoeffding exponent `N/128`. Their
high-probability events jointly assert actual output correctness and lightness.
The two-approximate seed interfaces retain the additive baseline two and take
an actual seed-validity and approximation certificate. `CorrectedIntro*`
provides the stretch substitution giving the introduction's exact lambda
argument and relative stretch error at most twice epsilon.

`CorrectedRuntime*` links the rational recursion to the corrected mathematical
output. The per-host represented-record machine has a separate finite-step
trace theorem. Instrumented graph loops have an explicitly stated unit-cost
loop metric. Seed construction, packing preparation, sorted-record preparation,
random generation, and concrete representation/bit costs have their stated
external-input roles; these interfaces do not certify an end-to-end bit-cost
implementation of the cited preparation algorithms.

## Reproduce the proof checks

Use the pinned `lean-toolchain` and `lake-manifest.json`, then restore the official
mathlib cache with `lake exe cache get`. Build and validate with:

```sh
LEAN_NUM_THREADS=1 python3 scripts/CorrectedLightEFTCheck.py \
  --state corrected-checks --lock /tmp/corrected-lean.lock
```

The default target is `CorrectedLightEFTSpanners`. The harness discovers the
actual source import closure, compiles one module at a time with strict flags,
replays each true leaf module individually, and audits actual declaring-module
ownership and recursively used types/bodies, including private and opaque
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Receipts bind source and dependency artifacts to the pinned compiler. Reuse is
permitted only when those inputs still match.

Use `--phase compile`, `--phase replay`, or `--phase audit` to resume one phase.
The corrected GitHub workflow performs fresh strict compilation and the complete
owner/axiom audit; local publication additionally records singleton kernel
replays. Historical checkpoint receipts are preserved separately and do not
certify this source snapshot.

Avoid invoking `leanchecker LightEFTSpanners`: its prefix expansion can launch
every module concurrently. The harness guards each exact leaf target and runs
replays sequentially. If an elaboration reaches Lean's memory cap, resume with
a higher `--memory-mb` value within the machine's available RAM; completed
source-bound checks remain reusable.

For a checkout without the large historical checkpoint artifacts:

```sh
git sparse-checkout set --no-cone '/*' '!/checkpoints/'
```

This excludes reproducible historical artifacts from the working directory and
preserves their Git history.
