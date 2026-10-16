# Independent combined-gate acceptance (2026-10-16)

The agreed finite-graph main-result scope is accepted after independent source,
artifact, log, hash and theorem-to-endpoint review. No Lean compiler, kernel
checker or new CI run was launched by this review or publication correction.

## Immutable identities and artifact access resolution

- Tested source: `34bda2f53bb8bd31cb7fb8322bf1499dc002d459`.
- CI trigger: `9d6411e936844a597a1dd2c87f2bd9c04d879c57`.
- Original evidence commit: `bbc02cb41519607f45d12f82d3e04575b5e99097`.
- [Successful run 38839172392](https://github.com/gbodwin/paper-formalizations/actions/runs/38839172392), job `116775045664`, first attempt.
- Artifact `12020389413`: 2,583,872 downloaded ZIP bytes, 624 extracted files.
- Independently recomputed ZIP SHA256:
  `ea5bc1e1afee087c00ba8e9e07577b151599261d829559a985b96774ce1a0637`.

The reviewer retrieved the full artifact through the authorized connected GitHub
download tool and read its returned download URL successfully. The builder's
earlier 403 remains an accurate historical diagnostic; it was not bypassed or
removed. The independently computed archive hash matches the GitHub artifact
metadata and upload receipt. All 623 artifact manifest entries were checked
against bytes, lengths and hashes, with an exact file-set comparison.

## Independently reconciled evidence

- Source receipt's 1,386 tracked paths match the frozen Git tree; 100 relevant
  source, support, audit, documentation, pin and baseline files were fetched and
  checked by SHA256 and Git blob hash. Accepted proof bodies were unchanged.
- The 53-module dependency-ordered inventory is the 52-leaf source-derived union
  plus aggregate: 49 paper leaves and three support leaves.
- All 145 command receipts have unique UUIDs and child PIDs, a common lock inode,
  non-overlapping intervals, successful exits and reaped children. Submitted
  sources, options and explicit Lean search paths were reconciled.
- All 53 compilations and 52 singleton kernel replays are covered. The 29 strict
  compilations have no diagnostic output. The other 24 match their inherited
  diagnostic baselines after source-root normalization: 44 anchored warnings
  (36 earlier warnings plus eight ConsistentTiebreaking warnings).
- All 559 actual-owner roots have exact recursive type/body closure in 20,437
  distinct constants, including 2,466 private constants and 14 opaque bodies.
  No missing or extra closure rows were found. The only axioms are `propext`,
  `Classical.choice` and `Quot.sound`; the audit rejects unsafe/partial roots.
- All 46 audit chunks reconstruct the original 9,138,326-byte TSV exactly,
  SHA256 `d7a4dae278904a25ed7e5ddc3483f9b7894a25ec49b76d209b0fb3eb028a336b`.
- All nine dependency pins, the manifest and executable receipts match. The
  official Lean 4.34.0 archive digest was authenticated against Lean's GitHub
  release asset metadata (asset `563514501`):
  `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`.
  Required Lean commit: `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.

These are independent inspections of the completed run, not a claim of a new
execution or bit-for-bit reproducibility of all locally compiled objects.

## Scope accepted

The [frozen proof coverage map](https://github.com/gbodwin/paper-formalizations/blob/34bda2f53bb8bd31cb7fb8322bf1499dc002d459/A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/PROOF_COVERAGE.md)
maps the Main Lemma and all five principal bounds: distance O(n sqrt(p)),
reachability O(n + (np)^(2/3)), additive +2 O(n p^(1/3)), +4 O(n p^(2/7)),
and +6 O(n p^(1/4)). The formal statements are explicit inequalities with
constants. The subset +2 and bidirectional sourcewise premises are discharged.

Directed endpoints use finite loopless input arcs supported by an ambient simple
graph, with either or both orientations allowed. Distance weights are finite
nonnegative reals, including zero. Additive endpoints use finite undirected
unweighted simple graphs. Empty and unreachable cases are included in the final
complete endpoints. Indexed slack lemmas retain their documented path hypotheses,
which their complete wrappers construct.

Signed weights, arbitrary parallel-edge models, self-loop normalization, infinite
graphs, runtime/complexity claims and every incidental printed statement are not
part of this acceptance. The withdrawn earlier all-pairs +4 claim stays withdrawn.

Suitable completion wording: **Main results formally verified for finite graphs
under the documented model assumptions, with corrected proof steps and an
independently reconciled clean combined CI gate.**

## Publication-only corrections and preserved history

C3 in `CORRECTIONS.md` now records that the +4/+6 constructions are complete.
The original historical report and frozen coverage map intentionally retain their
then-pending language; this dated acceptance supersedes that status.

The prepared `reconcile_artifact.py` originally required raw and convenience log
copies to be byte-identical. Exactly one copy, `official-cache-get.log`, was written
through Python universal-newline handling. Its CRLF and lone CR bytes become LF.
The corrected comparison allows exactly that transformation for that label only;
the other 144 copies must remain byte-identical. All 145 comparisons were tested
against the downloaded artifact. Manifest validation still authenticates both raw
and convenience files before this comparison. No raw logs or artifact bytes were
rewritten. The full prepared reconciler was not rerun against a local Git checkout;
the independent review used separately fetched and hashed frozen Git content.

The original checkpoint `evidence-sha256.json` describes the files at evidence
commit `bbc02cb41519607f45d12f82d3e04575b5e99097`, including the original helper.
It remains unchanged as historical evidence. This publication-only revision of
the helper is separate from both that manifest and the artifact's own manifest.
All original versions remain available at the immutable evidence commit.

Publication must retain the Theorem 12 correction directly beside its display:
replace the H-distance equality by triangle inequality. The seven-vertex Lean
counterexample refutes that equality, not the final +4 bound. Theorem 5.2's
distance/reachability citation correction is distinct; it does not purport to
disprove a stronger distance theorem. Statement boxes should link exact endpoints,
assumptions, this acceptance and the successful run.
