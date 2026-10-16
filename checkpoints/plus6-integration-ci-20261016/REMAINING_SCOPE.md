# Remaining scope from existing records

This is a reconciliation of existing records, not authorization to start additional proof work.

The paper README and preserved `source/extremallog.tex` list five main graph applications: general directed/weighted distance preservation, directed reachability preservation, and undirected unweighted pairwise +2, +4, and +6. The old `PROOF_COVERAGE.md` is dated to checkpoint `2c4f35b` and is stale for later +4 and +6 work; its open-item rows must not override newer source/evidence.

Current source contains the complete +2 and +4 existence wrappers (`PlusTwoComplete.lean`, `PlusFourComplete.lean`). The conditional +6 reduction has accepted earlier CI evidence. The subset +2 existence theorem and the integration discharging its premise have passed the reported independent source/log/hash reviews. This exact-source integration CI and its subsequent independent evidence review are the immediate remaining validation steps.

The remaining main application families not supplied by these modules are the directed/weighted distance-preserver statements (Theorems 3–4 in the old coverage record) and the directed reachability application (Theorem 5.1). The cited source-restricted result 5.2 is recorded as a prior result, not an axiom; its intended treatment must remain explicit in any later work. The current SimpleGraph unweighted/undirected spanner results do not silently settle these broader graph models. The subset +2 result formerly listed as cited Theorem 10 is now established as an existence theorem at constant 16, and the integrated +6 theorem no longer assumes it.

All the present accepted statements are finite mathematical existence/size/distance results. No implementation-level polynomial runtime, executable graph algorithm, optimal constants, or new graph-model extension has been formalized or newly agreed here. Those are not additional requirements silently added by this gate. The retracted all-pairs +4 assertion is not restored. Website publication and optional extensions remain outside this task. This turn performs no further paper proof development.

References: the paper's preserved README, PROOF_COVERAGE.md and source/extremallog.tex; the subset construction and integration checkpoint READMEs; and the conditional CI acceptance record. No broader acceptance or whole-paper completion is inferred from one gate.
