# Reachability half-cover discharged; sourcewise premise remains

Tested mathematical source: `6231f1d25ebcf9753e92156ca6fa8dc31582d606`. This additive checkpoint is on `checkpoint/reachability-halfcover-20261016`, with CI skipped. No full-result or whole-paper acceptance is claimed.

The user reports independent acceptance of the preceding conditional reachability mathematics. That is recorded as reviewer source/log/hash reconciliation, not fresh execution. The old recursive TSV was unreadable to the reviewer; this checkpoint exports it without modifying or recompiling it.

## Audit exports

[Previous audit manifest](audit-export/manifest.json) lists 39 ordered chunks. Concatenating their bytes, without extra headers or separators, reconstructs exactly 7684562 bytes with SHA256 `b38d52b3426f791fbada083c8620dd7164ff15e9ff1571ba3363a2d3ac2f8d99`. Each chunk has its own hash and size. This export was completed and reconstruction verified before any Lean invocation in this checkpoint.

[New audit manifest](new-audit-export/manifest.json) provides the same reconstruction format for this checkpoint's recursive TSV. The raw originals are preserved. Only the first chunk contains the header; chunks end on row boundaries.

## Constructed theorem chain

1. `reachability_integer_paths` uses actual allowed simple paths. It buys paths of length at most l, applies the existing half-hitting lemma to the long-path vertex supports, selects hubs only for hit indices, and splits allowed walks using takeUntil/dropUntil. The previously proved two-orientation hub routing supplies the long-path arcs. Union and filter bounds give actual input-arc support and the integer-parameter budget
   `p*l + 2*C*(sqrt(n*p*(2*n/(l+1)+1))+n)`.
   Here `2*n/(l+1)` is natural-number division, hence the requested floor. No path-restricted/global-distance equality is assumed.
2. `reachability_integer` constructs simple paths internally on the subtype of reachable demands, using zero-cost optimal paths only to obtain simplicity and allowedness. The residual is the image of unserved reachable indices. Unreachable demands never enter it; their satisfaction implications are automatic. The residual has at most half the original demand cardinality. Deduplication and finite unions prevent overlapping arcs or repeated endpoints from inflating the bound.
3. `reachability_half_cover` applies the proved slack budget with threshold `Nat.sqrt n`. Above the threshold, `Nat.sqrt_lt'` gives `n < p^2`. The empty-vertex case supplies the empty arc set separately. The coefficient is `B=(1+6*C)*n^(2/3)`.
4. `reachability_complete_sourcewise` applies the existing amplification theorem and small constructor. `Nat.sqrt_le'` gives the small-side condition `(Nat.sqrt n)^2 ≤ n`, hence `p^2 ≤ n` below the threshold. Its output is an actual input-arc subset preserving reachability equivalently on every demand, bounded by
   `2*C*n + ((1+6*C)*n^(2/3))/(1-(1/2)^(2/3))*p^(2/3)`.

No supplied HalfCover, paths, hitting set, hub assignment, or successful preserver remains in the final statement. The sole substantive unproved construction premise is `BidirectionalSourcewiseBound K A C`, together with `0 ≤ C`: sourcewise reachability bounds for both A and its reversal. This is a conditional endpoint, not the unconditional reachability theorem. Empty demand sets, coincident endpoints, and unreachable pairs are allowed. Ambient graph/input-arc conventions are unchanged.

## Sequential validation

Official Lean 4.34.0 and pinned dependencies are reused incrementally from the accepted local build. Exact executable, source and object hashes and search paths are retained. No default Lake build, dependency update, CI execution, website edit or parallel worker was used.

The runner commands were `python checkpoints/reachability-halfcover-20261016/run.py ReachabilityHalfCover`, followed sequentially by `... replay` and `... audit`. Compilation and audit used `-j1 -DautoImplicit=false -DwarningAsError=true`; the individual kernel replay used official `leanchecker -v SlackSparsification.ReachabilityHalfCover`. The final compile emitted no warnings. A local `maxHeartbeats 800000` proof elaboration setting is recorded in source for the subtype/residual wrapper; this does not change the kernel or axioms.

All compiler/checker invocations went through the same exclusive lock. The supervisor now hashes submitted source bytes under that lock and records source path, size and SHA256 directly in each UUID/PID/timing receipt, preserving a matching snapshot beside it. The local runner supplies the source explicitly for replay as well; future CI checker calls resolve the source explicitly. The CLI supports `--submitted-source`, and the supervisor rejects ambiguous automatic checker-source resolution. No old receipt is rewritten.

Five attempts are preserved: two failed compilations, one successful final compilation, one successful individual replay and one successful recursive audit. Failure 1 was a deprecated `dif_pos` diagnostic. Failure 2 retained a deterministic elaboration timeout, a misplaced `omit` syntax error and the consequential unknown-constant diagnostic. Fixes use the supported name, correctly scope `omit`, and increase the local elaboration budget. Raw UUID logs and submitted snapshots remain intact.

`evidence/execution-reconciliation.json` verifies unique IDs, one lock inode, non-overlap, reaped children and receipt/source-snapshot hashes for all five attempts. The recursive audit traverses 146 actual-owner project roots, nine declarations owned by the new module, 18238 recursive constants and 14 opaque bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms. Explicit sourcewise hypotheses are not discharged by this audit.

## Remaining work and handoff

[SOURCEWISE-NEXT.md](SOURCEWISE-NEXT.md) records the investigated SCC contraction/internal-tree and minimal-DAG required-edge collision/light-heavy route. None of that sourcewise construction is claimed proved here. The earlier distance-preserver bound is insufficient to discharge it.

The prior directed CI acceptance and corrected 13-warning count remain intact, including the historical timing qualification. All old partials, failed attempts and accepted source commits remain preserved. Terminal checks show no Lean/Lake/checker process and a free universal lock. Paused for independent review.
