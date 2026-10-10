# Actual two-star swap crossing classification

Source: `/workspace/shared/minor-free-spanners/SwapBadPairChargeDraft.lean`
Canonical staging module: `verification/swap-charge-stage/MinorFreeSpanners/SwapBadPairCharge.lean`
SHA-256 (both): `d9a78ca543f52ce1e59e5a3d26419c9633584f4d8da938f95c44d6d630d79ef6`

The source contains 12 theorems and one finite-set definition (218 lines).
Frozen production was not edited. All 89 entries of the checkpoint13 source
manifest were rechecked byte-identical on 2026-10-10 at approximately 23:05 UTC.

## Checked scope

- Exact forward crossing-set updates at both exchanged stars, for the literal
  `twoStarLeafSwap`: erase the outgoing leaf from the old crossing set and
  insert the incoming leaf exactly when its actual host adjacency holds.
- Every unchanged third star retains its directed crossing set to every
  fixed center, including the reverse crossing direction to either exchanged
  center. The third-center exclusions are explicit.
- If `(b,d)` becomes bad, was not bad before, and the inserted leaf `v` is
  not adjacent to `d`, the old forward crossing count is exactly two and
  there exists `w` in `(L b).erase u` such that both `G.Adj u d` and
  `G.Adj w d`. The symmetric theorem is also checked.
- For any supplied finite set `D`, these exceptional third centers lie in
  the literal finite union over old remaining leaves `w` of the `D`-restricted
  actual common-neighbor slices of `u,w`. Their cardinality is at most the
  sum of these slice cardinalities, hence at most the sum of the full actual
  `G.commonNeighbors u w` cardinalities when the host is finite.
- Original-host mate-freeness of the old branch yields the real-valued
  upper bound `card(exceptional centers) ≤ card((L b).erase u) * q`.
- For a bad pair of selected centers in the actual full simple quotient,
  the quotient edge exists, its actual host crossing-edge fiber has size two,
  and its parallel-edge suppression surplus is one. This is proved directly
  through `selected_edge_fiber_card`, and instantiated for the literal swapped
  family whose validity follows from the genuine cross edges and bipartition.
- A bundled admissible-exchange theorem retains the old branchwise
  mate-freeness and the explicit mate-freeness of the union of the two old
  branches, as well as real cross edges and `C ⊆ B`. It proves new packing
  validity, branch mate-freeness, branch disjointness, and the local witness.
  Global unmatedness is never used to manufacture branch nonmates.

The underlying set-update/classification lemmas deliberately require only
what their local identities need. The stronger admissibility theorem and
quotient-fiber theorem explicitly carry the additional structural premises.

## Checks

- Strict canonical-stage compilation: passed, `-DwarningAsError=true`,
  `-DautoImplicit=false`, `-j1`, `LEAN_NUM_THREADS=1`.
- Separate strict source re-elaboration and all 12 theorem axiom audits:
  passed. Every theorem uses only `propext`, `Classical.choice`, `Quot.sound`.
- Successful combined strict/audit gate released the compiler lock by
  2026-10-10 23:05:33 UTC. Log: `verification/swap-charge-strict-audit.log`.
- Independent official `leanchecker` replay passed, exit 0, releasing the
  lock by 2026-10-10 23:07:06 UTC. Log:
  `verification/swap-charge-kernel-retry.log`. The first replay attempt only
  exposed an outside-stage import-resolution issue; symlinks to already-built
  frozen dependency oleans in the stage repaired that packaging issue.
- Literal scan found no `sorry`, `admit`, custom `axiom`, or `native_decide`.
- Draft and canonical staged source are byte-identical.
- The checks ran under bounded actual nonblocking
  `flock -n -E 75 /workspace/shared/formalization-compiler.lock`; no lock was
  held while editing. Earlier diagnostic errors were repaired before success.
- Gate script: `verification/check-swap-charge.sh` (`strict` and `replay`).

## Remaining work

This is a bounded local incidence classification, not a full minimum-bad-pair
exchange argument. No global cleaning theorem, strict minimum-score gain,
source-step error, or final density/main theorem is asserted. The source is
outside production and has not been published. All requested local strict, axiom-audit, and independent kernel-replay
gates passed. Integration into production and any broader exchange/cleaning
argument remain separate owner work.
