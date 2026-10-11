# Fresh independent audit of the corrected distance-preserver package

## Verdict

**QUALIFIED PASS for the corrected/partial mathematical package at commit `40db5842cc89370c32e0b6ba64e231969f771ef0`, tree `450b98266065a7f8d6e3514144b9f863f4742ba1`. No mathematical blocker was found. There is one minor stale-documentation finding (F1). The original paper is not completely formalized.**

The original unweighted near-threshold existential assertion with a square-root-logarithmic terminal deficit remains unresolved. The displayed uniform-dimension lower-bound rate is now proved; the historical `939a39a9` audit's old boundary does not describe this checkpoint. The printed Euclidean weight assignment is false and is replaced by a proved quadratic assignment. The RS prose convention, at-least-two-terminal restriction, finite-weight domains and positive-depth qualification remain explicit corrections.

This is a new source/semantics/verification audit. Prior component reviews were not treated as proof authority. The review covers both upper-bound spines, weighted and unweighted lower-bound spines, actual graph/metric definitions, original statements, quantifier order and nonvacuity. Detailed reasoning and precise domain distinctions are in `semantic-findings.md`; 42 exact source statement/definition extracts are in `statements/inspected-statements.json`, and 12 final theorem types were separately elaborated.

## Main findings

- Theorem 1 genuinely constructs a finite directed nonnegative-weight distance preserver, handling zero weights, loops, empty types, repeated demands and unreachable pairs. It internally constructs consistent shortest paths and the routing/counting reduction.
- Theorem 2 constructs an actual native-edist-preserving subgraph. Its extremal induced-matching quantity and the triangle-removal subquadratic consequence are proved, not assumed.
- Theorem 3 produces actual exact-N/exact-T graphs with positive symmetric finite edge weights for every fixed admissible range constant. Its explicit weighted little-o theorem fixes the target factor before the eventual size/witness quantifiers.
- Theorem 4's uniform statement has the advertised finite assumptions and common loss `exp(-(1004+7A)sqrt(log N))`. The planar, balanced small-dimension and elementary-sphere branches all discharge their premises internally. Actual lattice geometry supplies the sharp-direction branch; there is no retained caller geometry certificate.
- The corrected quarter-root corollary uses the sphere branch's loss 15, gains 16, and therefore retains the advertised extra `exp(sqrt(log N))`. Its eventual B/N0/N,T quantifier order is correct. The finite range may be empty near its coarse initial cutoff, already disclosed in the frozen detailed documentation; it is eventually nonempty.
- Theorem 6 chooses its dimension constant before all parameters. Carry-free encoding gives arbitrary exact natural layer size with actual native paths, ownership, incidence and the exact natural-power budget. Positive path depth and x=0 are handled explicitly.
- Generic positive-real weighted Lemma 7 chooses one epsilon before all endpoints and walk competitors, extends from finite simple paths to cyclic walks by strict positivity, and proves actual native weighted-distance forcing. Inner symmetry is correctly a separate conditional result.
- ConstructionEnvelope and SubdivisionBarrier remain restricted numerical-count-family and graph-shape obstructions. Neither refutes the unresolved arbitrary-graph existential claim.

## Finding F1: stale current-scope prose

The frozen paper README, lines 132–139 and 193–195, says that the displayed growing-dimension range remains unproved. These are unmarked current-scope paragraphs, not the linked historical development record, and contradict the opening/current inventory. This is an underreporting/documentation defect, not a flaw in a proof.

The owner's narrow proposed remedy was independently applied to an audit-owned copy of the frozen README. It applied cleanly and exactly matched the corrected live README SHA-256 `bf1f28341d61894baa0aaba8ff4e3a4a03f2c25e8c383233319e72507b1f6541`. The patch SHA-256 is `8062b9b6cc904ee84e002bac40da9deacdaa5598df278e9b5f06ba3bd6551da0`. The remedy is adequate but outside the audited frozen commit. The original existential gap must remain visible after applying it.

## Integrity and independent checks

- All 244 frozen manifest entries matched; manifest SHA-256 `ac9f03850cfa66abbdcf96e4a67dc2e52056dc9d71318bd65ef74cf99825cde6`.
- All 234 archived repository files matched the exact Git blobs/tree, and all 112 frozen paper sources matched the available working-source inputs. The two later modules and changed working aggregate were excluded.
- All 1,937 paper declarations were inventoried by defining module, including private/generated names. Only `propext`, `Classical.choice` and `Quot.sound` appeared.
- An independent traversal of checked types and bodies, including opaque/theorem values, reached 49,091 constants. It found no unsafe constants and no unapproved axiom. All 1,744 reached defining modules have separately recorded source and local artifact hashes. Mathlib is at `5ed2965256430c3649e86755f9576b54eca72435`, with no tracked modifications.
- Every one of the 12 main-result dependency closures contains neither unsafe nor partial declarations. The complete all-declarations inventory additionally contains two generated partial computational auxiliaries: `LinearDistancePreservers.DirectionEncoding.encode._unsafe_rec` in ExactLayerEncoding, and `LinearDistancePreservers.walkOfSequence._unsafe_rec` in WalkSequence. They are outside all 12 mathematical result closures; they are not custom axioms or admitted proofs.
- Eleven selected frozen source modules were freshly elaborated with Lean 4.34.0, `-j1` and `autoImplicit=false`: TheoremOne, TheoremTwo, TheoremThreeExact, UniformDimension, InducedMatchingRemoval, WeightedConstruction, QuadraticRepair, QuarterRootTheorem, TheoremSix, WeightedPerturbation and WeightedSuperquadratic. All passed.
- Six of those freshly produced modules passed separate official leanchecker replays: both upper bounds, TheoremThreeExact, UniformDimension, TheoremSix and WeightedPerturbation.
- Exact-commit CI run 38088408693/job 114319654377 was independently checked through GitHub and its full hash-bound log. The job and explicit index/audit/replay steps succeeded. The raw log confirms 3,689 build jobs, 1,937 paper declarations, and 146 distinct project module replays including exactly all 112 frozen paper modules. Static index comparison found no omission or extra frozen paper module.

Supplementary empty-kernel-environment replay and independent audit-only nonvacuity results are reported in the final verification supplement below and machine verdict. They are kept distinct from frozen-package source coverage.

## Limits and reproducibility

This is not a fresh local rebuild/replay of every paper and mathlib module. Whole-package build/replay evidence is the independently confirmed exact-commit CI, supplemented by the selected local checks, complete declaration/body audit and semantic/source review. This is a risk-based end-to-end proof-spine review, not a claim to have manually reread every line of every imported theorem. Lean's kernel and the three stated axioms remain the trusted foundation; the official replay is not an external foundational verifier.

The other three papers in the repository are outside this semantic audit. No GitHub/Site publication or frozen/shared-source modification was performed by this auditor. Public research-site linking remains held.

`COMMANDS.md` gives commands and retained initial audit-harness diagnostics; raw command outputs are in `raw/`. The failed initial harness attempts concerned overlay setup, name syntax and the distinction between a generated-declaration inventory and theorem proof dependencies, not frozen mathematical source failures. `verdict.json` and `artifact-manifest.json` bind the finished evidence.

## Final verification supplement

At 22:42:29 UTC, the last bounded audit window completed successfully:

- The entire checked dependency closure of `TheoremFourGeneral.uniform_dimension_lower_bound`, **45,841 constants**, passed the official `Lean.Kernel.Environment.replay` starting from an **empty kernel environment**. The driver explicitly rejected unsafe/partial proof dependencies and any axiom beyond the three permitted. This checks the imported proof bodies too, rather than trusting an already populated imported kernel environment. See `raw/fresh-closure-uniform.log`, `ReplayClosure.lean` and `raw/supplementary-batch.log`.
- The independent audit-only lemmas `audit_cap_ge_two` and `audit_quarter_root_eventual_nonempty` compiled. They show that log N>=64⁴ is sufficient for terminal count T=2 to satisfy the corrected cap, and that all sufficiently large natural N satisfy the finite conditions. They add no theorem to the frozen target. Two non-failing tactic-style warnings were retained in `raw/nonvacuity.log`.
- The pinned binary reports Lean 4.34.0, compiler commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.

All original qualifications and finding F1 remain unchanged. The final verdict is a qualified pass of the corrected partial package, not completion of the literal original paper.
