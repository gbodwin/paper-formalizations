# Verification record: full original-result extension

## 10 October 2026 continuation

The new modules extend the existing VFT proof to the actual EFT greedy
algorithm, EFT Theorem 1 and Corollary 2, the edge-blocking analog of Lemma 3,
the final limitation construction, both real-exponent corollaries, and exact
naive exhaustive fault-query counts. See [the statement map](statement-map.md)
for precise scope and the imported-background classification.

At this checkpoint:

- All new mathematical modules have passed individual Lean compilation.
- The limitation construction passed a standard-axiom audit and kernel replay;
  its subsequent `f=1` addition has compiled and is in the aggregate replay.
- The complete final-library build, defining-module axiom audit, and kernel
  replay are being rerun after integration. Remote CI is authoritative for
  the repository-wide checks on the published commit.
- No `sorry`, `admit`, custom axiom, unsafe declaration, or native-decision
  shortcut was introduced in the new proof sources.
- `verification/AllDeclarationsAudit.lean` provides a VFT-library-only audit;
  the root audit also includes selected EFT, real-bound, limitation, and
  runtime declarations.

The theorem assumptions have been reviewed: neither the upper bounds nor the
limitation construction takes its conclusion, a favorable sample, a blocking
set, or the cited 2018 optimality lower bound as an assumption. The limitation
constructs a genuine extremal graph before blowing it up.

The remaining material outside the formal theorem claim is external cited
lower bounds, historical/comparative claims, and an implementation-level
machine-cost analysis. The runtime module checks a full exhaustive query
schedule, not an assertion that every early-exit run traverses it.

## Historical verification: 5 October 2026 VFT-only snapshot

The record below predates the folder reorganization. The current library and
namespace are `VFTSpanners`, with sources under
`A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners`.
The old `BodwinPapers` names below describe the checks at the recorded commit.

The VFT formalization was published on 5 October 2026 in commit
[`831557faf3281ed40903932ca1288241139d9ab6`](https://github.com/gbodwin/paper-formalizations/commit/831557faf3281ed40903932ca1288241139d9ab6).
Its [GitHub CI run 37369463588](https://github.com/gbodwin/paper-formalizations/actions/runs/37369463588)
completed successfully. The results below refer to that exact proof snapshot.

A fresh reviewer independently fetched all 25 tracked files at this commit,
verified every Git blob hash and the complete tree hash
`a7e381c885cb45720c8d196f9baf3d9c228a8dd0`, and reproduced the build and
proof checks. Their review found no mathematical defect within the documented
VFT scope. The subsequent maintenance changes update this record and the
standalone audit; the mathematical proof modules are unchanged.

| Check | Result |
| --- | --- |
| Lean version | 4.34.0; release commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| mathlib version | Commit `5ed2965256430c3649e86755f9576b54eca72435` |
| Dependency lock | All nine dependency checkouts matched `lake-manifest.json`; tracked files were clean |
| Full `lake build` | Passed in CI and independent reproduction; 1,174 jobs, including all 14 project modules |
| Module-index check | `lake exe mk_all --check --lib BodwinPapers` passed |
| CI module-origin axiom audit | Passed for all 195 declarations defined in project modules |
| Independent module-origin axiom audit | Passed for the same 195 declarations |
| Updated standalone audit | Verified locally on the same proof snapshot; all 195 declarations passed |
| Audit regression checks | Temporary fixtures containing a private axiom and an axiom in another namespace were both rejected |
| Main theorem, Moore bound, and unconditional corollary axiom dependencies | Exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Kernel replay | Independent sequential replay of all 13 proof modules passed; this is a manual check, not enabled in CI |
| Source inspection | No proof holes, custom axiom declarations, unsafe declarations, or native-decision proof shortcuts in project proof source |
| Statement inspection | Elaborated theorem types and mathematical definitions matched the documented VFT statements; no Moore hypothesis in `corollary_two` |
| Published CI job | [`111962703324`](https://github.com/gbodwin/paper-formalizations/actions/runs/37369463588/job/111962703324), successful on the commit above |

## Audit coverage

At the published commit above, `scripts/AxiomAudit.lean` selected declarations
by their `BodwinPapers` name prefix and checked 191. CI already selected them
by their defining modules and checked 195. The four additional declarations
were `Sym2.diagSet.eq_1` and three private generated declarations associated
with `greedyEdges.match_1`. The independent reviewer checked all four and
found only permitted axiom dependencies.

The updated standalone script now also selects by defining module: a module
name must be `BodwinPapers` or have it as a name-component prefix. This covers
private/generated declarations and declarations added to other namespaces.
It checks each selected declaration's transitive axiom dependencies, fails
on any dependency outside `propext`, `Classical.choice`, and `Quot.sound`,
and fails if no project declarations were selected. Its coverage now matches
CI's audit on this snapshot. A successful Lean build alone would not reject
every admitted proof; the axiom audit remains a required check.

## What the checks establish

The main theorem `vft_greedy_theorem_one` has only the finite input graph,
nonnegative real weights, and `k ≥ 1`, `f ≥ 1` as mathematical inputs. Its proof
constructs the blocking set and favorable sample; neither is assumed.

`extremalEdges_moore n r hr` proves `b(n,2r)^r ≤ 2^r*n^(r+1)` for every
`n` and `r ≥ 1`. `corollary_two` then proves the subgraph, weighted distance,
and `m^r ≤ 72^r*n^(r+1)*f^(r-1)` guarantees from the input graph, nonnegative
weights, and `r,f ≥ 1`, with no unproved extremal-bound premise. The earlier
conditional theorem remains for modular reuse; it is not the final corollary
statement.

Kernel replay uses Lean's own kernel on compiled declarations, starting from
each module's imported environment. It is a separate recheck, not a different
independently implemented verifier or a fresh rebuild of every mathlib
dependency. See `scripts/KernelCheck.sh` for the sequential reproduction command.

## Resource and environment notes

Sequential kernel replay avoids retaining all module environments at once;
the initial all-at-once invocation had exceeded the container's 8 GiB memory
limit. The independent reviewer successfully replayed all 13 proof modules in
separate sequential processes.

Local reproduction reused the installed Lean runtime and locked dependency
caches. The container required a temporary executable-path compatibility shim
because its process namespace did not match the mounted `/proc` namespace.
The reviewer inspected and recompiled that shim. It only redirects executable
path lookup to `/proc/self/exe`; it changes neither Lean's kernel nor its proof
terms, and is not part of the repository. GitHub CI passed on its own runner.

## Limits of the claim

The verified result is the complete VFT main argument and unconditional
Corollary 2 in the exact finite forms shown in `statement-map.md`. The
integer-power bound is proved; its real-exponent/Big-O restatement is not
separately formalized. The EFT extension, imported optimality lower bound,
and final EFT limitation construction remain outside this formalization.
An axiom-audit pass does not replace review of the mathematical statements.
