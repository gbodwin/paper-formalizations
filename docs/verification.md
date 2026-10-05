# Verification record

Verified in the assistant's execution environment on 5 October 2026.
This proposed update has not yet been published to GitHub.

| Check | Result |
| --- | --- |
| Lean version | 4.34.0; release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib version | Commit `5ed2965256430c3649e86755f9576b54eca72435` |
| Dependency lock | Existing `lake-manifest.json`, unchanged |
| Full `lake build` | Passed; 1,174 jobs, including all 14 project modules |
| Module-index check | `lake exe mk_all --check --lib BodwinPapers` passed |
| Axiom audit | Passed for all 191 declarations under `BodwinPapers`, including generated declarations |
| Main theorem, Moore bound, and unconditional corollary axiom dependencies | Exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Kernel replay | All 13 proof modules covered: the 11 unchanged modules passed previously; new `Moore` and updated `Corollary` passed fresh individual rechecks |
| Source inspection | No proof-hole commands, new axiom declarations, unsafe declarations, or native-decision proof shortcuts in project proof source |
| Statement inspection | Inspected the new Moore and corollary theorem signatures and the girth, extremal, and distance definitions; no Moore hypothesis in `corollary_two` |
| Publication base | GitHub `main` commit `2dea98389f8a9c878dfe5c29a6002c391778f6bd` |
| New GitHub CI run | Pending approval and publication; no new GitHub write made |

The original blocking-set and exact-sampling modules are unchanged. Eleven new
proof modules connect the defined weighted greedy algorithm to its distance
and size guarantees, including the uniform Moore bound. The root module imports
every proof module.

## What the checks establish

The main theorem `vft_greedy_theorem_one` has only the finite input graph,
nonnegative real weights, and `k ≥ 1`, `f ≥ 1` as mathematical inputs. Its proof
constructs the blocking set and favorable sample; neither is assumed.

`extremalEdges_moore n r hr` proves `b(n,2r)^r ≤ 2^r*n^(r+1)` for every
`n` and `r ≥ 1`. `corollary_two` then proves the subgraph, weighted distance,
and `m^r ≤ 72^r*n^(r+1)*f^(r-1)` guarantees from the input graph, nonnegative
weights, and `r,f ≥ 1`, with no unproved extremal-bound premise. The earlier
conditional theorem is retained for modular reuse, but is no longer the final
corollary statement. No new package dependency or toolchain change was needed.

The standalone axiom-audit script now fails on an unapproved dependency instead
of only printing a selected list. The existing GitHub workflow already invokes
this script and also runs its own project-wide audit. Both allow only the three
standard axioms above. A Lean build by itself would not reject every admitted
proof; the axiom audit is therefore a required check.

Kernel replay uses Lean's own kernel on the compiled declarations in each
module, starting from that module's imported environment. It is a separate
recheck, not a different independently implemented verifier and not a fresh
reproof of every mathlib dependency.

## Resource and environment notes

The first all-at-once `leanchecker BodwinPapers` invocation exhausted the
container's 8 GiB memory limit. Its default behavior starts a task for each
matched module. Retrying each of the 12 proof modules in a separate sequential
process succeeded. The Moore update was subsequently checked by replaying
`BodwinPapers.VFTSpanners.Moore` and `BodwinPapers.VFTSpanners.Corollary`
in separate sequential processes; both exited successfully. The other eleven
proof modules are byte-for-byte unchanged from the earlier verification.
`scripts/KernelCheck.sh` documents the sequential route for every current module.

As in the earlier verification, the execution environment needed a temporary
filesystem-path compatibility shim because the process ID used for `/proc`
lookup did not match the mounted process namespace. The shim redirects only
the executable-path lookup to `/proc/self/exe`. It changes neither Lean's
kernel nor the proof terms and is excluded from the proposed repository update.

## Limits of the claim

The verified result is the complete VFT main argument and unconditional
Corollary 2 in the exact finite forms shown in `statement-map.md`. The
integer-power bound is proved; its real-exponent/Big-O restatement is not
separately formalized. The EFT extension, imported optimality lower bound,
and final EFT limitation construction remain outside this formalization.
An axiom-audit pass does not replace review of the mathematical statements.
