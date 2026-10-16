# Native component assignments and sampled hosts — 2026-10-16

Independent read-only review accepted budget source
6c8aaf1d6415589a8d9cfe904fe107fe9acd05ec and evidence
c108837c01ecb9971d3205c67f066bb9ddeaee87. This records supplied reconciliation,
not fresh reviewer execution or whole-paper acceptance.

NativeCandidateAssignments constructs forest assignments from explicit blocker
sets, proves multiplicity under 2*f+h <= q+1, proves exact component containment
and uniqueness, and partitions assigned candidate weights. Each actual forest
component is a tree on its own vertex subtype, not on the entire ambient V.
NativeHostSampling retains the component's original forest IDs in a sampled
native host, removes blocker pairs among retained candidates, and proves
candidate weight <= 4*f times sampled-host weight. Component seed weights sum
to at most the original forest weight. No high-girth or host-weight-to-tree-
weight upper estimate is assumed or claimed.

NativeSeedPositivity separately proves positive seed/minimum weight from
positive actual-edge weights and an actual nonloop edge. Zero-optimum budget
results remain valid without these hypotheses.

See checkpoints/light-eft-native-hosts-20261016/REPORT.md for bounded strict
validation and the review handoff. Native cycle-blocking/high-girth and the
per-host upper-weight step, full aggregate validation, the full weighted bound
and Theorem 34 remain open. All original identities and prior work are preserved.

## Preserved earlier checkpoint notes

# Native weighted seed-budget interface — 2026-10-16

Independent read-only review accepted seed-to-forest source
4a13e4864a819b39b0f9f0bf5a2f953adcb1c86e and evidence
03fd4d5b04530f1bc2309c9b68b210dd299e4f53. This records supplied evidence
reconciliation, not fresh reviewer execution or whole-paper acceptance.

NativeSeedBudget derives the sum of the q+1 original-ID forest weights at most
twice the seed weight from the constructed congestion bound and the existing
arbitrary-ID incidence identity. It chooses an attained minimum connectivity
preserver and constructs its budgeted forests, including zero optimum cases.
The existing host-counting argument yields unblocked original-ID hosts with
actual surviving walks under explicit 2*f+h <= q+1 coverage. A real-valued
budget corollary supplies the congestion input to the charging algebra.

No native per-host candidate-weight estimate, positive-denominator conclusion,
final lightness ratio or full weighted-multigraph bound is asserted. The simple
Sym2 host-weight theorem has not been silently applied to native edge IDs.
Full aggregate validation and Theorem 34 remain open. See
checkpoints/light-eft-native-budget-20261016/REPORT.md for strict bounded
validation and the review handoff. All prior work is preserved; CI is skipped.

## Preserved earlier checkpoint notes

# Native seed-to-forest interface — 2026-10-16

Independent read-only review accepted bridge source
8dfe637d3661379adf1471c5e6d052321bac3f0a and evidence
661d498bd12df7ebb5b8feb2e106a5d82783a29c, reconciling 407 manifest entries,
89 receipts and 31 chunks. This records the supplied review, not fresh execution.

NativeSeedDemand restores omitted-edge faults after using fault-set erasure to
obtain the seed demand. NativeEdgeDoubling uses E x Fin 2 on the actual vertex
subtype, proves even degrees and doubled fault thresholds, and projects copied
reachability back to original IDs with congestion at most two.
NativeSeedForests applies the existing Eulerian packing existence theorem to
this full-vertex doubled graph and selects native spanning forests inside the
projected members. Every omitted actual edge is connected in each of q+1 seed
forests, each original seed ID occurs at most twice, and all projection
inclusions and the copied packing are explicit. No full-vertex assumption on
arbitrary ambient V is made; no subdivision introduces new vertices.

See checkpoints/light-eft-native-seed-20261016/REPORT.md for bounded validation,
raw attempts and the review handoff. Full aggregate validation, the weighted
bound and Theorem 34 remain open. All prior sources and evidence are preserved.

## Preserved earlier checkpoint notes

# Native weighted walk/reachability integration — 2026-10-16

Independent read-only review accepted NativeWeightedFaults source
9f1150416b3f682c57f42058a6075de35b2323fe and evidence
c21b5fa89ee42e25455c20e1e3a1f1eaff7ea1e2. This records supplied reconciliation,
not fresh reviewer execution or whole-paper acceptance. The full 400-module
parent aggregate gate remains outstanding.

NativeWeightedReachability proves custom surviving edge-ID walk existence iff
native reachability after restriction and deletion of the same original IDs.
Explicit vertex-subtype equivalences preserve original vertices; self-loop
steps become reflexive native reachability and native adjacency lifts via an
actual surviving edge ID. This is an existence equivalence, not a weight
preservation claim for the forgotten-edge native graph.

The native FaultConnected contract is bridged at arbitrary strict thresholds;
its q+1 specialization is exactly at most q faults. Weighted connectivity
preservation transports this threshold. The existing HasNativeForestPacking
contract is equivalent to the finite-ID custom-walk formulation, retaining
native forest and disjointness requirements and the exact threshold 2*k.

See checkpoints/light-eft-native-bridge-20261016/REPORT.md for bounded strict
validation, sequential receipts, raw failed attempts and the review handoff.
No full weighted bound, Theorem 34 result, new CI or full aggregate gate is claimed.
All prior sources and evidence remain preserved.

## Preserved earlier checkpoint notes

# Native edge-ID weighted fault semantics — 2026-10-16

Independent review accepted threshold source 7e4c0a730d13655fc75a4629dd4056a21a9a7cce
and evidence 00a732e31cb1a5e7bd1f70e376d9bcbaf1a7b5f4 as a bounded result.
This records the supplied review, not fresh execution or whole-paper acceptance.

NativeWeightedFaults adds surviving weighted walks on Graph V E, actual edge-ID
fault deletion, an attained minimum connectivity-preserver weight, and edgewise
replacement implying walkwise and extended-distance EFT stretch. Parallel-edge
regressions show that deleting one ID leaves the other traversable at its own
weight. Original vertices are unchanged. Finite nonnegative weights are encoded
as NNReal; distance is ENNReal, with infinity exactly for unreachable pairs.

This is a semantic foundation for the weighted multigraph extension, not its
stretch/lightness upper theorem or a runtime result. Theorem 34 remains unproved,
not disproved. All prior proof files and evidence are preserved.

See checkpoints/light-eft-native-weighted-20261016/REPORT.md for the bounded
strict validation, failed attempts and independent-review handoff. No new CI
or whole-paper acceptance is claimed.

## Preserved earlier checkpoint notes

# Exact cloud-certificate threshold — 2026-10-16

The preserved 398-source checkpoint faaaad5a31de3fef117f023154405ea21f2af1aa
has successful exact CI 38338948024, completed 2026-10-13 04:20:35 UTC.
This supersedes the historical assembly note naming 353 as the latest verified
checkpoint; it is not a new full-398 local execution.

The additive BlowupCertificateThreshold module joins the preserved positive
large-cloud theorem and complete-base obstruction. For every complete base of
order at least three and every actual spanning tree, a nonempty finite cloud
I yields a q-fault connectivity preserver exactly when q < |I|. The q+1 and q
boundary corollaries make the strict threshold explicit. This does not establish
the original square-root-cloud denominator/lightness scaling or Theorem 34.
Every original proof body and prior partial remains preserved.

See checkpoints/light-eft-continuation-20261016/REPORT.md for bounded sequential
execution and the retained redundant draft. No optional runtime extension,
website change, full-399 build, new CI or whole-paper claim is made.
Independent review remains pending.

## Preserved earlier checkpoint notes

# Light EFT: literal Bernoulli samples and repeated draws

Active partial formalization. The actual flag-filter constructs an ordered sampled-edge list, and the batch controller invokes that same machine for every draw and returns the ordered list of its actual outputs. Exact finite-product laws transport these results to the original Bernoulli subset and independent repeated-draw laws. Loops are retained as in the original sample universe; raw duplicate cells remain faithfully represented by the machine.

Eleven reviewed sources and two additive strict/safety gates preserve all earlier proof and interpreter bodies under the 120-minute cap. Twenty actual cases exercise both literal controllers. Their atom bound is linear in the number of flags and draws. Uniform randomness generation, efficient seed/forest construction, canonical input enumeration, raw physical preparation and bit runtime remain separate.

The latest fully verified checkpoint at assembly is 353. Independent preservation, remote binding and terminal exact successor CI remain separate gates. This is not a whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: computable polynomial repetition schedule

Active partial formalization. This checkpoint replaces exact real-log evaluation by the explicit computable count 32*(s+5)*n+1 and proves the same adaptive failure bound n^(-s). It deliberately oversamples relative to the logarithmic schedule. A literal four-step atom program computes the count. The exact original-graph interpreter retains the same corrected stretch/lightness endpoint under this finite assignment law, with the same minimum-seed and forest witnesses.

Six reviewed sources and one additive strict/safety gate preserve every earlier theorem, interpreter, fixture and gate under the 120-minute cap. Eight actual count cases cover empty/singleton orders and different confidence parameters. This is an atom-model schedule and probability result. Efficient seed/forest construction, random sample generation, physical input preparation and bit runtime remain separate; the original logarithmic sample count is not claimed here.

Latest fully verified checkpoint at assembly is 330. Independent preservation/remote binding and terminal exact successor CI are separate gates. This is not a whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: actual original-edge preparation and full candidate execution

Active partial formalization. This checkpoint executes stable descending merge sort on the original edge list using actual first-match rational-weight lookups, filters seed edges and reads the original raw draw bank. The literal returned candidate records feed the actual weight-matrix, forest/component/host and changing-state selection interpreters. Neither the sorted edge list nor the prepared candidate bank is supplied. Stable ties and first matching undirected records preserve the original ordered greedy semantics.

The whole actual-output endpoint retains the original finite assignment law, corrected stretch (1+epsilon)(2k-1), competitive lightness 1+64f Lambda(n,(1+epsilon)(2k-1)+1)/h and failure at most n^(-s), under its explicit hypotheses. The execution bound uses only sums and sizes of the original inputs. Minimum seed/forest choice, finite-set orientations and random assignment sampling remain mathematical choices. Integer/rational operations are atoms, and fuel-expression evaluation plus physical bit runtime remain separate obligations.

Twenty-eight proof sources and five additive strict/safety gates preserve every earlier source, fixture and workflow gate with the 120-minute cap. Latest fully verified checkpoint at assembly is330. This successor requires independent preservation, remote binding and terminal exact-commit CI. It is not a whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: original weighted records and canonical assignment inputs

Active partial formalization. This checkpoint constructs the weight matrix by real first-match undirected lookup in the original rational-weight records, builds the forest/component/host candidate bank, and executes the same changing selected-edge state. The returned matrix is handed directly to the existing interpreter. Missing weights give zero; duplicate orientations use the first matching record. Sixteen actual interpreter cases cover matrix order, diagonals, reversed and duplicate edges, zero and negative rational values, and whole candidate execution.

Canonical finite weighted records represent the original weight function, and canonical keyed draw records represent the same original finite assignment law. The resulting actual-output theorem retains corrected stretch (1+epsilon)(2k-1), competitive lightness 1+64f Lambda(n,(1+epsilon)(2k-1)+1)/h, and failure at most n^(-s), under its exact hypotheses. No weight matrix, component catalogue, host list or draw-correspondence certificate is supplied to that theorem. Minimum seed and forest selection, finite-set orientations and assignment sampling remain mathematical choices. The transition bound is an atom-model bound; fuel-expression evaluation and physical bit complexity remain separate.

Fifteen proof sources and three additive strict/safety gates preserve every earlier source, fixture and workflow gate with the 120-minute cap. Latest independently audited exact green checkpoint is305. This successor still needs independent integration/remote binding and terminal exact CI; it is not a whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: actual forest-constructed output under the original assignment law

Active partial formalization. This 338-source checkpoint identifies the actual canonical roots and ordered records with the original forest-component indices. Component coverage, distinctness, vertex membership, mapped host edges and eligible catalogues are derived internally. The unchanged complete interpreter constructs the candidate bank from original forest lists and keyed draws, executes its changing selected-edge state, and returns exactly the original assignment-driven greedy output.

The same original finite assignment law now bounds failure of the actual returned graph. The mathematically chosen minimum seed and forest family give the corrected stretch (1+epsilon)(2k-1), competitive lightness coefficient 1+64f Lambda(n,(1+epsilon)(2k-1)+1)/h, and failure n^(-s), under the exact stated parameter and nonnegative-weight hypotheses. Raw keyed draws still represent the original assignment. Proof-side canonical representatives and graph-list representations identify mathematical objects; they are not claimed as efficient seed/forest or random-sampling algorithms. Fuel-expression evaluation, physical bit complexity and complete paper scope remain separate.

Eight reviewed proof sources are added, preserving all earlier machine and fixture bytes, gates and the 120-minute cap. Exact305 is fully green; later successors have separate CI. This successor requires independent remote binding and terminal exact CI. No new original-paper correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: original forests and draws through the changing-state candidate loop

Active partial formalization. This 330-source checkpoint executes canonical component and host discovery from original forest endpoint lists, looks up raw draw lists at internally computed labels, constructs each candidate budget and eligible-host record, and returns the ordered bank. The complete candidate controller consumes that same actual bank while updating its selected-edge list after each admission. Its exact output agrees with the original typed selection recursion. No generated component, host, eligible catalogue, candidate budget or prepared bank is supplied.

The same execution has a rational-atom instruction bound expressed in original forest edge-list sizes, raw draw counts and cells, candidate count and initial seed/input sizes. Returned host and bank sizes are proved internally. Original forests and draws remain input representations; correspondence with the paper's finite random assignment and the full probability endpoint still require their final join. Seed/forest construction, random generation, fuel-expression evaluation and physical bit complexity remain separate.

Eleven reviewed sources and thirty-two actual controller cases are added with all earlier proofs and gates preserved, including the 120-minute cap. Exact305 is fully green; later successors have separate CI. This successor requires its own independent remote binding and terminal exact CI. No new original-paper correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: original forest lists and raw draws to component inputs

Active partial formalization. This 319-source checkpoint traverses original forest endpoint lists, executes canonical component and host discovery for each, and copies that literal output while attaching the original forest index. It then performs actual first-match lookup in a raw keyed draw bank at the internally computed forest/root label and returns the precise component inputs expected by the existing preparation pipeline. Missing keys explicitly return empty draw lists. No component, host or eligible catalogue is supplied.

Original occurrence correspondence, complete forest-component coverage, distinct/exhaustive canonical index enumeration, numerical-label injectivity and exact typed component-input encoding are proved. The same execution has an original-input rational-atom count bound. Original forests and raw draws remain input representations; correct random assignment representation and the complete candidate pipeline still need their final join. Seed/forest construction, random generation, fuel-expression evaluation and physical bit complexity remain separate.

Fourteen reviewed sources and twenty-two whole-controller cases are added with all earlier proofs and gates preserved, including the 120-minute cap. Exact280 is fully green; later successors have separate CI. This successor requires its own independent remote binding and terminal exact CI. No new original-paper correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: original edges to canonical component hosts

Active partial formalization. This 305-source checkpoint composes actual canonical component discovery with literal original-edge host filtering. The same returned component records drive short-circuit endpoint membership scans; nonloop edges are retained in original order, including original duplicate occurrences. The resulting host edge sets equal the original mapped connected-component graphs. No component list, host edge list, matrix or reachability answer is supplied.

The complete controller has a rational-atom transition bound depending only on graph order and original endpoint-list length. Its output preserves the complete canonical component records. The typed theorem uses valid Fin n endpoints; one outside-label interpreter case is robustness evidence only. Joining this catalogue into the entire forest/candidate-bank caller remains separate, as do original seed/forest construction, random generation, fuel-expression evaluation and physical bit costs.

Ten new sources, fourteen actual cases and an independent exact-source review are included. All inherited proofs and gates remain, with the 120-minute cap. Exact267 is fully green; later successors have separate CI. This successor requires its own independent remote binding and terminal CI. No new original-paper correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: original edges to canonical connected components

Active partial formalization. This 295-source checkpoint constructs complete canonical component records from graph order and the original endpoint list. It builds the zero-weight record/matrix representation, generates all vertex indices, runs the real bounded distance controller, scans actual discovered vertices for their minimum, and retains exactly one root per component. No matrix, reachability bit, path, component list, representative or component-index enumeration is supplied.

The literal returned records are nonempty, disjoint and cover every original vertex. Their corresponding original connected-component indices are distinct and exhaust the finite type. The same execution has an input-only rational-atom transition bound, including all edge scans, matrix construction and real calls. It does not yet combine this canonical output with the earlier whole forest/candidate-bank caller. Original forest and seed construction, random generation, fuel-expression evaluation and physical bit costs remain open.

Fifteen new sources, twenty-eight actual cases and two independent exact-source reviews are included. Strict, safety, exact local replay, aggregate and index receipts are recorded separately. Every inherited proof and gate is preserved, including the 120-minute CI cap. Exact254 is fully green; later successors have separate CI. This successor requires its own remote binding and terminal CI. No new original-paper correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: component vertices to actual greedy execution

Active partial formalization. This 280-source checkpoint constructs the full endpoint relation of each represented component by actual nested vertex traversal, including diagonal pairs. The resulting component records, catalogue and stable candidate bank are newly constructed and consumed by the real changing-state candidate interpreter. No eligible-edge relation, candidate budget, eligible-host list or decision answer is supplied.

The exact original forest-assignment output follows from a complete distinct component-index enumeration and correct component vertex representations. The transition bound includes pair construction, catalogue and bank construction, matrix budget lookup and all actual voting/candidate calls, and depends only on original input sizes. Original component discovery, seed/forest construction, host/draw/matrix representations, random generation, fuel-expression evaluation and physical bit complexity remain outside this atom-model result.

Thirteen new sources have strict local checks, fourteen actual fixtures and independent exact-source review. New safety covers 628 declarations and eleven complete type/body closures; exact replays, full280 aggregate and all indexes are recorded separately. Earlier proof bodies and gates are preserved. Exact247 probability-output CI is fully green; later preparation successors have their separate CI receipts. This successor requires its own remote binding and terminal CI. No new mathematical correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: probability guarantee for the prepared-bank interpreter

Active partial formalization. This 267-source checkpoint attaches the original finite assignment law and joint high-probability EFT/lightness conclusion to the actual matrix/catalogue-to-candidate interpreter. Its returned graph has the original stretch and corrected competitive-lightness bound, with failure probability at most n^(-s), under the same chosen minimum seed and forest family.

The seed/forest choice is a mathematical existence theorem. Original incidence coverage, distinct original host indices, matrix/host/draw representations and input order remain explicit. The actual interpreter constructs candidate budgets and eligible host lists and executes the changing-state decisions; no eligible-list or decision answer is supplied. Constructing raw forest incidences, minimum seeds, random assignments, fuel-expression evaluation and a physical bit implementation remain separate.

Three new semantic sources pass local strict checks, exact kernel replays, independent source review and three full type/body safety closures. The full 267-source audit, indexes and preservation evidence are recorded separately. All earlier machine fixtures and proof bytes are preserved. This successor requires its own remote binding and terminal exact CI; earlier active runs remain separate. No new mathematical correction or whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: constructed candidate banks and original assignment execution

Active partial formalization. This 264-source checkpoint reads the original stored weight matrix, computes candidate budgets, scans incidence catalogues and constructs each eligible host list in stable order. The actual caller passes that same newly constructed bank to the candidate interpreter, which updates the selected-edge list using real host-vote returns. Its transition bound uses only original catalogue/draw lengths, initial selected-list size and graph order.

Distinct original host indices, complete incidence representations and the static original assignment bank derive the exact original sampled-greedy output. No candidate budget, eligible-host list, admission answer or adaptive schedule certificate is supplied. The original recursion's reverse-order correspondence remains explicit.

Ten new sources have strict local checks, fourteen actual interpreter fixtures and independent exact-source review. New defining-module safety covers 441 declarations and nine full type/body closures; exact replays, full 264 aggregate and index evidence are recorded separately. This successor requires its own remote binding and terminal CI. Exact 244 and its resource-only successor are already fully verified; 247 and 254 runs remain separate.

Forest-incidence generation, initial raw catalogue/matrix/draw representations, random generation, minimum-seed construction, fuel-expression evaluation and bit complexity remain outside this atom-model transition bound. There is no new mathematical correction and no whole-paper completion claim.

## Preserved earlier checkpoint notes

# Light EFT: constructed eligible host records

Active partial formalization. This254-source checkpoint scans actual stored incidence lists, constructs eligible host records in original order, and feeds that exact list to the host-vote interpreter. It returns the original indexed admission Boolean under explicit incidence completeness and original draw-bank representations. No eligible-host list or admission result is supplied. The input-only transition bound includes short-circuit scans, field copying, reversals and all actual host-vote calls.

Distinct original host indices remain explicit even when two hosts have identical data. Original incidence catalogues, host/draw endpoint lists, graph/weight representations and fuel-expression evaluation remain inputs or external work. Constructing the forest incidence catalogue, candidate budgets and the full prepared candidate loop, random generation, seed/packing algorithms and bit complexity remain separate. The inherited atom cost model has not changed. No new mathematical correction is asserted.

Seven new sources have strict local checks,14 actual interpreter fixtures and independent semantic review. Defining-module/full-type-body safety, exact source replay and full254 aggregate/index evidence are recorded separately. This successor needs independent integration review, remote binding and its own terminal CI. Exact244 is already fully verified;247 probability-output CI remains separate. This is not whole-paper completion.

## Preserved earlier checkpoint notes

# Light EFT: probability guarantees for actual stored output

The exact244 proof checkpoint is now fully verified: [run38305477187](https://github.com/gbodwin/paper-formalizations/actions/runs/38305477187) passed at2026-10-12 21:33:22UTC, with244 Light modules,3125 declarations and382 repository kernel replays. This247 successor retains the reviewed120-minute resource allowance from exactf918f01275644705c2345123c5d21bce970cacd6. Its own terminal CI is still pending. Cancelled229 and the separate resource-only run retain their own outcomes.

Active partial formalization. The new 247-source local checkpoint transports the
original finite fresh-assignment law to the actual interpreter's returned edge
list. The final theorem chooses a minimum connectivity seed and forest hosts
internally, and derives the joint fault-tolerance/lightness guarantee with
failure probability at most n^(-s). No reached-state accuracy event is supplied.

The domain is a finite simple graph on Fin n, globally nonnegative rational
weights positive on graph edges, positive f, h and k, positive rational epsilon,
and 2f+h <= q+1. The stretch is (1+epsilon)(2k-1), and the corrected competitive
lightness coefficient is 1+64f*lambda(n,stretch+1)/h. The original exact finite
assignment law and its logarithmic repetition count are retained.

Static representations of the seed, candidate order, eligible host identifiers
and finite draw bank remain inputs. The minimum seed/forest choice is a
mathematical existence result, not a polynomial implementation. Random sampling,
raw input preparation, seed/packing runtime, bit complexity, fuel evaluation,
weighted multigraph extensions and the previously recorded unresolved paper
qualifications remain separate. No new mathematical correction is asserted.

The three new theorem sources have strict checks, exact-source kernel replays,
three full type/body safety closures and independent source review. They change
no interpreter transitions; the 23 actual execution fixtures are retained from
the exact [244 parent](https://github.com/gbodwin/paper-formalizations/tree/c2968852fd003113e0d912e614f6985f6c91e5f8).
The exact244 terminal receipt is included; the earlier229 cancellation remains separately recorded.
The full local aggregate covers 247 modules and 3,129 own declarations.
Publication, remote binding and terminal247 CI remain separate pending gates.

## Preserved earlier checkpoint notes

# Light EFT: actual fixed-assignment greedy execution

Active partial formalization. This 244-source checkpoint traverses literal host
records, counts actual returned sample votes, and executes candidate admissions
and selected-list updates. The same run returns the original real-weight
empirical-voting graph for the supplied original finite assignment, with a fixed
controller-transition bound in original stored input lengths and graph order.
No distance, vote, admission or subroutine transition answer is supplied.

The original assignment tape is independent of the selected state. Its static
record-bank representation therefore derives the full evolving-state schedule;
no adaptive tape lookup or precomputed admission premise is needed for that
model. Constructing the stored input lists, random generation, eligibility,
seed/packing, raw graph encoding, rational bit costs and fuel-expression
evaluation remain separate. The weighted multigraph main extension, Theorem34
repair, literal Theorem10 qualifications and whole-paper completion remain open.
No new mathematical correction to the paper is asserted.

Fifteen new sources, twenty-three actual interpreter cases and their scoped
independent source reviews are bound in the verification evidence. The exact229
parent is [3076daee](https://github.com/gbodwin/paper-formalizations/tree/3076daee4e7d73e4a7e8a02f0a80f3ed4c57092d).
Its [CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/38301896259)
had passed clean build, strict new checks, indexes and the declaration audit and
was in kernel replay when this status was written. Successor244 terminal CI is
an independent pending gate; the full local results are recorded in
verification/stored-candidate-local-gates.json.

## Preserved earlier checkpoint notes

# Active 229-source stored-edge sample-vote candidate

Parent: exact full-green 217 commit 9058082e0ea704d89918c50229e24506dbe1e43d,
run 38244148164 (217 own sources, 2,201 own declarations, 355 repository replays).

Twelve new modules construct the membership records from actual stored edge
lists, construct the entire list of sample matrices and execute the inherited
vote on that same list. They prove exact empirical-estimate refinement and an
explicit polynomial transition bound in the represented input lengths.
All twelve strict checks and official kernel replays, sixteen actual interpreter
cases, 588-declaration/eleven-full-closure safety and two independent source
reviews pass. All five paper indexes also pass. All 273 inherited dependencies were freshly restored. The complete 229-source
root and 2,788-declaration reference audit pass. Production preservation review,
publication binding and terminal successor CI are pending.

The full theorem/input/cost scope is in THIRTYSIXTH_SCOPE.md. This remains a
partial paper: raw source preparation, outer host/candidate and selected-set
updates, randomness, physical bit costs, seed/packing, weighted multigraph
coverage and the documented lower-bound repair/quantifier boundaries remain.

## Preserved previous checkpoint record

## Represented sample-matrix and voting controller (217 modules)

The complete per-host caller now executes on literal stored sample records.
Each cell supplies a rational weight and four membership bits. Actual loops
build the clipped matrix T union (S intersect (E minus Q)), exclude diagonal
cells, and perform both row and matrix reversals one cell at a time. The caller
then runs each transition of the verified distance submachine and accumulates
failure and draw counts. Its final comparison is count>0 and
3*count<=8*failures, including the exact zero-sample convention.

A successful trace for m represented samples uses at most
m*(n^3+5*n^2+10*n+9)+1 transitions. The fixed-fuel interpreter reaches that
same Boolean halt. Exact refinement identifies it with the rational estimate
and with this host's vote in the existing real-weight empirical recursion.
Neither a distance answer nor an accuracy/vote assumption is supplied.
Fourteen executions on literal data include clipped seed edges, retained host
edges, empty samples, exact 3/8 and neighboring thresholds, negative/zero
budgets and reverse endpoints.

The cost model treats rational arithmetic/comparison and natural-register/
pointer operations as atoms. Supplying the record fields from evolving graph
or edge storage remains an explicit representation premise. Outer candidate
and host traversal, selected-set updates, random generation, rational bit
costs, compiler/allocator simulation and efficient seed/packing construction
remain open. This is an actual controller-transition count, rather than the
preserved 204 padded instrumentation field, but is not physical-runtime or
whole-paper completion.

All seven new strict production builds, root/index, declaring-module audit,
seven official kernel replays, fourteen actual execution fixtures and
reciprocal exact-source review pass. All 210 inherited mathematical bodies
and all workflow/script gates are unchanged. Full 204 CI is green; full 210
and fresh 217 CI remain separate pending gates at publication.

Weighted-multigraph coverage, stronger Theorem 34 lower repair, literal finite/
uniform Theorem 10 quantifiers, cited-background reconciliation and the final
fresh skeptical whole-paper audit remain explicit separate obligations. No
new source correction is asserted.


## Historical checkpoint record

## Concrete linked-list distance controller (210 modules)

The new component gives the weighted-distance test an actual first-order
controller on finite linked-list matrix and distance-table storage. Its states
perform initialization, every neighbor/row traversal, all list reversals and
the final indexed lookup. No transition invokes a supplied graph/weight
function, finite-set operation, vector enumeration or hidden list traversal.

A proved successful transition trace reaches the correct halt in at most
n^3+3*n^2+6*n+4 steps. The executable fixed-fuel interpreter returns that same
halt. Exact matrix/vector refinement identifies its result with the 204
rational shortest-walk test, and hence the existing native real walk predicate
for nonnegative rational weights. Twelve executions on literal raw matrices
cover rational thresholds, reversed endpoints, unreachable endpoints, zero
weights, negative budgets, singleton and empty-domain boundaries.

This is a precise rational-atom linked-list/pointer-machine result. Rational
addition/comparison and natural-register operations are explicit atoms of the
model; it does not prove physical CPU time, rational bit complexity or a
compiler refinement. The matrix and dimension header are supplied data with
a proved representation contract. Input parsing/materialization, sampling and
voting data structures, efficient seed/packing construction, random-bit
generation and the complete algorithmic runtime join remain open. The 204
padded instrumentation counter is preserved separately; this new bound is on
actual controller transitions, not that returned counter field.

All six new sources pass strict production, root/index, the exhaustive
allowed-axiom audit, six official independent kernel replays, the twelve
execution fixtures and reciprocal exact-source review.
All 204 inherited proof bodies and all workflow/script gates are unchanged.
The 204 parent has full CI success at 07:44:14 UTC on 12 October, including all
342 exact-tree replays and 1,564 declaring-module checks.

No new mathematical source correction is asserted. Weighted-multigraph upper
coverage, stronger lower-certificate repair, finite/uniform lower quantifiers,
cited-background reconciliation and a fresh skeptical whole-paper audit are
still separate obligations. Whole-paper completion is not claimed.


## Historical checkpoint record

## Executable rational empirical core (204 modules)

The new component implements actual table-based rational weighted-distance
tests and the literal empirical sample/vote/edge recursion. It proves exact
refinement of the already verified real-weight semantics for every finite
tape. The same output is computed; no shortest-path answer or estimator
accuracy is assumed by the refinement proof.

Each distance table is materialized before the next round. Native walk
semantics prove the bounded-round result; loop erasure supplies completeness
for nonnegative weights. Orientation-independent Sym2 lifting does not choose
a quotient representative. Disconnected graphs, zero weights, empty walks,
negative test budgets, empty sample lists and threshold boundaries are covered.

The measured program executes these loops with an explicit high-level work
counter. A distance test has cost 6*n^3+2*n^2+n+2. With j supplied host IDs,
L candidate edges and at most m samples per query, the whole voting loop has
cost at most 1+L*(j*(m*(6*n^3+2*n^2+n+4)+5)+4). Actual fixed-length assignment
tapes satisfy the sample bound internally. Fifteen compiled execution
fixtures test real program outputs and the distance counter.

This is an abstract adjacency/weight/tape-access and finite-set operation
count. It does not certify constant-time implementations of those inputs or
primitives, arbitrary-precision rational bit costs, compiler-generated runtime,
or memory allocation. Seeds, hosts, eligible lists, edge order and finite tapes
remain supplied data. Efficient seed approximation, packing, random-bit
generation and a paid end-to-end polynomial runtime theorem remain open.
The executable implementation is on Fin n with rational weights and stretch;
the broader real-weight mathematical198 theorem remains unchanged.

All six exact new sources pass strict production builds, full root/index,
exhaustive allowed-axiom audit, official independent kernel replays and
reciprocal source review. All198 prior proof bodies and
workflow/script gates are unchanged. The198 parent has full exact CI success
at05:40:52 UTC on12 October:1364 declarations and336 repository replays.

This implementation milestone asserts no new paper defect and no whole-paper
completion. Weighted-multigraph upper coverage, stronger lower-certificate
repair, finite/uniform lower-bound qualifications and final skeptical
whole-paper audit remain separate.

The proved numeric measure is precisely the padded instrumentation counter
returned by this program. List length (including repeated tape.length), list
and vector enumeration, vector projection and counter summation are not each
instrumented as separate Lean evaluation steps. They belong to the chosen
abstract primitive boundary. No theorem bounds every evaluation step, allocator
operation or bit operation by this counter. A representation-aware operational
semantics and its cost simulation remain a separate runtime obligation.


## Historical checkpoint record

## Actual fresh-tape high-probability guarantees (198 modules)

This checkpoint closes the adaptive concentration premise for the corrected
simple-graph empirical Algorithms2/3. It constructs a normalized finite law
of genuinely fresh independent original-edge samples, clips each draw to the
actual reached graph, and proves the exact estimator expectation. A two-sided
Hoeffding bound and conditional fresh-step union bound apply only to reached
candidate/host queries, rather than to every possible graph state.

The same random assignment drives the original empirical recursion. The
nonrepeating input ensures a fresh current-candidate update cannot alter an
earlier reached state. Saturation gives no queries for large fault budgets;
in all other cases the actual query count is at most n^4. With
m = ceil(32(s+5) log n)+1 independent draws per test, the probability of an
inaccurate reached trace is at most n^(-s), for every natural s. Empty and
singleton inputs are handled directly by their empty candidate list.

Consequently the same actual output simultaneously is an f-EFT spanner and
has competitive lightness at most:

- Algorithm2: 1+64f*lambda(n,t+1).
- Algorithm3: 1+64*lambda(n,t+1)/eta, with q=floor((2+eta)f),
  h=floor(eta f)+1 and eta>0.

Here t=(1+epsilon)(2k-1), f,k>0, epsilon>0, and actual input edges have positive
weights. The finite optimum seed and all forest/component hosts are chosen
internally. The baseline1 and total zero-denominator ratio are explicit.
There is no supplied accuracy or independence premise in the final
high-probability conclusions.

This is a finite mathematical randomized construction. Polynomial-time seed
approximation, efficient packing, executable weighted-distance tests,
random-bit implementation and paid runtime remain open. The printed exact
lambda argument remains independently refuted; the corrected argument is
t+1. Weighted-multigraph upper coverage, the stronger repaired Theorem34 lower
scaling, Theorem10 finite/uniform qualifications, cited-background scope and a
fresh whole-paper audit are still separate. No whole-paper completion or
polynomial-time Theorem13 conclusion is claimed.

All ten exact new sources pass strict production builds, root/index,
exhaustive allowed-axiom audit, independent kernel replays and reciprocal
source review. The 188 parent remains a separate exact CI.


## Historical checkpoint record

## Actual empirical-output lightness (188-module packet)

The corrected empirical Algorithms 2 and 3 now have a joined deterministic
accuracy-event theorem for both EFT correctness and competitive lightness of
the same actual output. All minimum seeds and forest/component hosts are
constructed internally. No accepted-output lightness, blocking, probability
independence, host packing or congestion oracle is a premise.

The exact finite Bernoulli insert/restrict identities and actual accepted-voter
history prove expected retained host weight at least assigned weight/(8f).
This uses a fresh coordinate for the current original edge and literal containment
of the zero-fault greedy cleanup inside the estimator's old prefix. A finite
maximum sample attains the bound. Its actual blocking data, zero blocker cap,
MST pruning and genuine embedded tree domain give an assigned-host bound of
32f times lambda(n, stretch+1) times the host weight. Literal vote multiplicity
and original-edge congestion two aggregate these weights without duplication.

The seed baseline is retained. For t=(1+eps)(2k-1), Algorithm 2's one-vote output
has competitive lightness at most 1+64f*lambda(n,t+1). Algorithm 3 uses exactly
q=floor((2+eta)f), h=floor(eta*f)+1 and has bound 1+64*lambda(n,t+1)/eta for every
eta>0. A stronger absolute output-weight inequality is proved before dividing;
the total zero-denominator convention is explicit. The finite simple graph,
f,k>0, eps>0, globally nonnegative weights and strictly positive input-edge
weights are all explicit. These are corrected exact-extremal bounds: the printed
lambda(n,t) claim remains separately refuted by the established counterfamily.

Accuracy on the actual reached states remains an explicit event. This closes
the conditional sampled-output lightness part of Lemmas 32–33; it does not prove
its probability or the high-probability clause of Theorem 13. Empirical tape
independence/generation and adaptive concentration (Lemma 30), executable
shortest-path tests, sample bounds, and paid polynomial seed/packing/runtime
remain open. The optimum seed is a classical finite choice, not a polynomial
implementation or a claimed approximation algorithm.

All fourteen new strict production builds, root/index, allowed-axiom audit and
fourteen independent official kernel replays pass, with reciprocal exact-
source review. The 174 parent is fully green: run38199768599,
terminal success by2026-10-12 04:07:14 UTC,1,149 paper declarations and312 complete-
repository replays. The fresh188 full CI remains a separate gate. All174 inherited
proof bodies are unchanged.

Weighted multigraph extension, Theorem34 replacement lower certificate, literal
uniform finite Theorem10 lower coverage, cited-background reconciliation and a
fresh skeptical whole-paper audit remain open. No whole-paper completion is
claimed, and the exact-lambda defect remains distinct from the lower proof-
certificate gap.


## Historical checkpoint record

## Actual empirical-voting correctness (174-module packet)

The deterministic good-event implication of corrected Lemma 31 is now joined to
a literal finite empirical estimator and threshold-voting recursion. Each tape
entry is an actual list of finite sampled edge sets at the current state,
candidate and host. Samples are clipped to current non-seed edges and the
actual host is retained. The estimate is the fraction of failed weighted-distance
tests, with explicit total-division value zero on an empty list.

For p=1/(2f), the finite Bernoulli law itself gives probability at least 1/2
of avoiding any at most f faults, including f=1. An actual fault witness and
fault-disjoint host imply failure of the sampled distance test. With error at
most 1/8 on the actual reached states, this forces a vote at threshold 3/8.
The output recursion then proves the full all-fault walk-spanner guarantee.

The forest/component hosts are internally constructed from an actual q-fault
connectivity preserver. There is no supplied packing, congestion/count oracle,
or assumed acceptance behavior in the final theorems. They cover Algorithm 2's
one-vote insertion predicate at q=2f, and Algorithm 3's exact integer parameters
q=floor((2+eta)f), h=floor(eta*f)+1 for every eta>0. The common recursion scans
all eligible hosts; only its insertion predicate, not short-circuit runtime,
is identified with Algorithm 2. Finite simple graphs, f>0, stretch>=1 and globally
nonnegative weights are explicit.

These are classical finite mathematical graph-test recursions, not an executable
shortest-path implementation or a paid runtime model. Accuracy is an explicit
simultaneous event on the actual visited states. The probability law for the tape,
adaptive concentration (Lemma 30), accepted-output lightness (Lemmas 32–33), and
polynomial-time preserver/packing construction and distance testing remain open.
The sampled output is not identified with the older exhaustive-fault greedy
output whose corrected exact-extremal lightness bounds are already proved.

All eight strict production builds, root/index, allowed-axiom audit and eight
independent official kernel replays pass, with reciprocal exact-source review.
The 166 parent is now fully green: run38194242847, completed2026-10-12 02:42:48 UTC,
1,093 paper declarations and304 complete-repository replays. Fresh174 full CI
is a separate pending gate. All166 inherited proof bodies are unchanged.

The weighted multigraph main extension, Theorem34 replacement lower certificate,
literal uniform finite Theorem10 lower coverage, cited-background reconciliation
and fresh skeptical whole-paper audit remain open. The established printed exact-
lambda counterfamily and separate proof-certificate defect are not conflated.


## Historical checkpoint record

# Actual lower-family checkpoint — 10 October 2026

Status: active partial verification. Main upper/lower/runtime scope is incomplete.

## Corrected exact-extremal upper bounds (166-module packet)

For s=(1+epsilon)*(2k-1), the new final theorems construct a true minimum-weight
fault-connectivity preserver Q and an actual f-EFT s-spanner H with

    competition 2f:             lightness(H | Q) <= 1 + 16 sqrt(f) lambda(n,s+1)
    competition floor((2+eta)f): lightness(H | Q) <= 1 + 8 lambda(n,s+1)/eta.

Here lambda is now the actual supremum over weighted graphs with exactly n
vertices and weighted girth above the stated argument. It is not an assumed
bound or an at-most-n substitute. At n>=2 and argument>2, the totalized Lean
definition equals the literal actual-graph supremum. The n<2 boundary is defined
as zero, and zero optimum uses the existing total real-division convention.

The proof transports actual graph/MST weights through reindexing and subdivides
a positive edge of an internally chosen bottleneck MST into two equal positive
halves. This adds exactly one vertex, preserves both weights and lightness, and
does not decrease weighted girth. Iteration therefore proves the exact-order
monotonicity needed to compare every actual subtree host with the original
order. The already proved coarse girth bound establishes that the spectrum is
bounded. Sampling, pruning, real supremum comparison, genuine host transport,
heavy/light charging, congestion two, forest construction, and minimum-preserver
choice are then joined without a supplied packing or extremal-bound oracle.

The final scope is finite undirected simple graphs with globally nonnegative
real edge weights strictly positive on actual edges; f,k are positive natural
numbers and epsilon,eta are positive reals. The additive seed baseline one and
exact higher-budget floor remain explicit. All 152 parent proof files are
unchanged. This closes the corrected exact-lambda upper interface at s+1.
The printed argument (1+epsilon)*2k remains refuted by the existing counterfamily;
this checkpoint does not restore it.

A separate finite-uniform boundary is made explicit: an actual two-vertex unit
tree has extremal lightness at least one for every girth threshold. Consequently
no single constant gives lambda(2,(1+epsilon)*2) <= C*2/epsilon for every epsilon>0.
The all-positive-epsilon wording of cited Theorems4/17 needs a bounded-epsilon
convention or an additive baseline if read as such a finite-uniform assertion.
This does not refute a fixed-epsilon asymptotic assertion with a parameter-dependent
large-n onset, nor the O_epsilon coarse bounds. The source's Big-O onset ambiguity
is retained explicitly; no new asymptotic theorem-false claim is made.

All strict production, root/index, defining-module axiom and fourteen official
kernel replay gates pass, together with independent exact-source semantic review.
Fresh exact 166 full CI remains a separate pending gate. The exact 152 parent is
fully green: run38185593849, completed2026-10-12 00:29:25 UTC,1045 paper declarations,
and290 complete-repository kernel replays. Historical sections below describe
then-current stages only and do not override this status or the numbered map.

Remaining whole-paper obligations are the weighted multigraph main extension,
actual efficient algorithms and concentration/runtime (including packing runtime),
a valid Theorem34 lower denominator certificate with the claimed scaling, the
literal every-n/epsilon-uniform Theorem10 lower domain, cited-background/source
coverage reconciliation, and a fresh skeptical end-to-end audit. A proved finite
existence statement does not establish the polynomial-time clause.


## Historical152 packet snapshot

## Constructed square-root-f upper bound at exact competition 2f (152-module packet)

Theorem exists_eft_spanner_square_root_bound constructs a true minimum-weight
2f-fault connectivity preserver Q and an actual f-EFT spanner H of stretch
(1+epsilon)*(2*k-1), with the explicit finite bound

    competitiveLightness H Q w <= 1 + 16 sqrt(f) (8 + 2048/epsilon * n^(1/k)).

Finite simple graphs, globally nonnegative real weights strictly positive on
actual edges, positive natural f,k and epsilon>0 are explicit. The additive seed
baseline is retained. Zero optimum uses the existing total real-division
convention. No forest family, host family, local blocking certificate or optimum
certificate is supplied to the final existence theorem.

The actual heavy/light argument partitions candidates at residual blocker cap
r=floor(sqrt(f)). Heavy candidates use sampling probability 1/(2r); light candidates
retain cap f but receive 2r+1 unblocked actual component hosts. Their respective
weight bounds are 8r L w(Q) and 8f L w(Q)/(2r+1), where
L=8+2048/epsilon*n^(1/k). The exact integer inequality f<=r(2r+1), including f=1,
gives the stated bound. Only seed blockers disqualify actual seed-tree hosts.
Original edge identities, injective host-domain transport and congestion two
are preserved. Internally constructed doubled-subdivision forests discharge the
structural inputs at q=2f; finite minimization supplies Q.

This establishes the coarse O_epsilon(sqrt(f)*n^(1/k)) upper consequence associated
with printed Theorems 11/29. It does not restore the refuted exact lambda expression.
Theorem 34's denominator-certificate gap is a separate unresolved lower-bound issue.
The full main multigraph extension, efficient randomized algorithms/runtime and
fresh whole-paper final audit remain open. Historical sections below retain their
then-current scope and must not override this latest status.

All 144 parent proof sources are unchanged. Eight strict production builds, the
152-module root/index, all 1045 defining-module declaration axiom checks, eight
independent official kernel replays and reciprocal exact-source semantic review
pass. Fresh exact 152 full CI is a separate pending gate;144 at c1538fd1 is the fully
green baseline (run 38175414276, completed21:48:34 UTC, 11 October 2026;282 repository
replays). The 140 dependency baseline also passed completely.


## Constructed coarse higher-competition upper bound (144-module packet)

Theorem exists_eft_spanner_rounded_coarse_bound now constructs both a true
minimum-weight connectivity preserver Q and an actual f-EFT spanner H of
stretch (1+epsilon)*(2*k-1), with

    competitiveLightness H Q w <= 1 + 8*(8 + 2048/epsilon * n^(1/k))/eta.

The precise competition budget is floor((2+eta)*f). The domain is finite simple
graphs, globally nonnegative real weights that are strictly positive on actual
edges, positive natural f and k, and arbitrary positive real epsilon and eta.
No upper restriction on eta is assumed. The seed baseline one is retained;
zero optimum weight is covered by the existing total real-division convention.

The constructed native Eulerian packing is transferred to actual simple
forests by exact degree and restricted-edge isomorphisms. The actual doubled
two-subdivision has even degrees. Its internally constructed disjoint forests
project with congestion at most two; the existing genuine component-host and
greedy-weight analysis then applies. Exact floor arithmetic supplies the surplus,
and finite minimization supplies Q. No forest/host family or optimality certificate
is an input to the final existence theorem.

This establishes the corrected finite coarse upper consequence associated with
Theorem12's O_{epsilon,eta}(n^(1/k)) upper bound. It does not restore the refuted
exact lambda expression, prove the square-root-f bound at competition 2f, prove
the main multigraph extension, certify lower statements, or establish runtime.
The full paper remains incomplete and requires a fresh final skeptical audit.

All 140 prior proof files are unchanged. Four new strict sources, the 144-module
root/index, all 1027 defining-module declaration axiom checks, four official
kernel replays and independent exact-source component review pass. Fresh exact144
full CI is a separate pending gate;129 at f59a915d is the terminal full-CI baseline.
Both125 and129 completed all clean-build/index/audit/replay gates;140 is running. See TWENTYSEVENTH_SCOPE.md and receipts.


## Historical 140 packet snapshot

All140 local gates pass:11 new strict production sources, root/index,1017
declaration allowed-axiom checks and11 official new kernel replays. The frozen
553-line packet passed independent skeptical exact-source review; all129 prior
proof blobs are unchanged. New exact140 full CI is pending,125 and129 runs
38171859725/38172783934 are running, and the terminal baseline remains112/822
at5277f0ea (fullCI38159794045).

Theorem24's finite mathematical existence dependency is constructed by actual
vertex-count induction, including internal core trees, quotient expansion and
singleton-island splitting. The final predicate contains only original edge
membership, native bridges, family disjointness and actual joins for every
FaultConnected(2*k) pair. Full finite vertex domains and even degrees are
explicit; loops/parallels and k=0 are handled. No final forest family is supplied
to the final theorem. Polynomial runtime, the phantom-ambient wrapper, actual
doubling/congestion/host joins, weighted/fractional estimates and main EFT
bounds remain open. This is not whole-paper completion. See TWENTYSIXTH_SCOPE.md.

## Historical 129 packet snapshot (11 October20:34 UTC)

The129/988 packet adds four modules proving literal split-edge family pullback,
actual walk expansion, finite trace induction and native forest pruning. The
joined single-Steiner reduction carries a genuine disjoint-original-edge forest
lifting certificate for every supplied disjoint output family. It does not
construct that output packing. The multi-island induction and main bounds remain
open. All125 earlier proof bytes are unchanged. Strict new production builds,
129 root/index,988 declaration audits, four new official kernel replays and
independent exact-source component review pass. Full129 CI is pending;125's
run38171859725 is running after clean build/index/audit success. The fully green
baseline remains112/822 at5277f0ea, CI38159794045. No full-paper audit/completion
is claimed. See TWENTYFIFTH_SCOPE.md and its separate gate/review receipts.

## Historical 125 packet snapshot (11 October20:19 UTC)

The fully green baseline is112/822 at5277f0eafb5937064345c8b8645add37e88c45d8,
exact CI38159794045 SUCCESS18:02:40. The109 predecessor also passed its complete
CI38159252903. The frozen125/972 packet adds13 native Eulerian splitting and
single-Steiner reduction modules. All13 strict production builds,125 root/index,
all972 declaration allowed-axiom checks and all13 new official kernel replays
PASS. Flow's independent exact-source component review PASS at20:10 checked
all126 manifest entries and all112 parent proof blobs. New exact-commit full125
CI is pending. No paper-wide final audit or completion is claimed.

The final finite theorem constructs actual split graphs and a finite trace,
exhausts nonloop center incidence, and reduces to the exact terminal vertex
domain while preserving even degrees and required FaultConnected(2*k) pairs.
This means resilience to fewer than2*k deletions; k=0 is vacuous apart from
endpoint membership. It handles loops, parallel IDs, isolated/empty domains
and zero center degree, with no assumed splitting or final packing primitive.
The uniform-threshold Eulerian dependency is proved, not general non-Eulerian
Mader. Original-edge forest expansion and multi-island packing induction,
congestion, weighted/fractional joins, main upper bounds and runtime remain open.
See TWENTYFOURTH_SCOPE.md, TWENTYFOURTH_LOCAL_GATES.json and
TWENTYFOURTH_INDEPENDENT_FLOW_AUDIT.json for exact scope and separate evidence.

## Historical 112 packet snapshot (11 October17:27 UTC)

The fully exact-CI and independently reviewed baseline is106 modules /800
declarations at10c3a3753e62a00881eee9dbb14e4b77049b2226. Run38153732739
passed every clean-build/index/axiom/kernel-replay stage at16:30:23.

The reviewed109 existence checkpoint is7047d2e08e31907242cb53ff3b706905643907e8.
All strict production/root/index/814-declaration checks and three new official
kernel replays pass; its exact full clean CI38159252903 is still running.
The new112 packet completes the necessity and native tree-packing equivalence.
Three new strict production builds,112 root/index and all822 declaring-module
allowed-axiom checks pass locally. Prior109 proof sources and objects are reused
unchanged. All three new official replays pass; fresh reciprocal source review returned COMPONENT PASS at17:27 UTC; exact
full clean112 CI is a separate obligation.

For finite original edge identities and a finite nonempty actual vertex set,
a native multigraph has k pairwise edge-disjoint spanning trees iff every
surjective m-block actual-vertex labeling has at least k*(m-1) original crossing
identities. This covers printed Theorem22's positive integer domain and k=0.
The existence proof constructs the seed internally by actual induction. The
necessity proof requires only disjoint connected spanning subgraphs: arbitrary
partition fibers need not be connected. True crossing-quotient connectedness
and the native edge lower bound give m-1 crossings per member; original-edge
disjointness then bounds the sum. Loops and parallel cycles remain native.
The final packing predicate contains only original-edge membership, actual
connectedness, native bridges and disjointness, with no partition or maximality
assumption hidden inside it.

Mader splitting, Steiner expansion, the required connectivity-preserving forest
family/congestion, weighted fractional dependencies and unrestricted paper
upper/runtime bounds remain open. The finite existence proof is noncomputable;
no efficient construction or full-paper completion/final audit is claimed.

## Historical CI-green checkpoints

Commit `cff07e88f8e16711368e3cd55c6ae658f3dfcc2b` contains36 modules and369
project declarations, including the actual real-stretch lower family. All
local gates, exact-source kernel replays, and frozen independent reviews pass.
Full exact-commit CI passed at20:56:59 UTC, including repository-wide replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38084671078 .

The preceding commit `30ff80ef6bf429d823bf14d84866f4ac1b996fe6` contains 21 modules and 229
project declarations. Its local root/index/build, exhaustive allowed-axiom audit,
all module kernel replays and frozen independent semantic reviews passed.
Full exact-commit CI passed, including repository-wide kernel replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38080374924 .

The preceding 19-module/219-declaration checkpoint
`e5bbdf892cba74f0a0be8b890f1da2daec065399` also passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38079515337 .
The 16-module/171-declaration checkpoint
`827800bb20f1b59b896be0a0a1a5f5294f6dc788` passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38077848156 .

The earlier 12-module/151-declaration commit
`e79a8b06353ed2155bca7080080724c5abfba193` also passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38076966078 .
The initial four-module/65-declaration commit
`aedcf714c75ad2db7ee81ae3d0dc56e279155659` passed full exact CI:
https://github.com/gbodwin/paper-formalizations/actions/runs/38075342370 .

## New obstruction components

Three new modules add an actual six-vertex counterexample to the Theorem34
MST-cloud denominator certificate, a generic every-spanning-tree obstruction
including the exact source cloud rounding, and an exact high-fault saturation
lemma. Their 48 declarations passed standalone local axiom audit; all three
compiled and were independently kernel replayed. The source interpretation and
frozen statements have independent semantic review in
`FOURTH_SOURCE_AND_COMPONENT_AUDIT.md`.

The fixed-f certificate defect invalidates that proof step, not the lower
bound theorem itself. The infinite near-extremal family used to establish
source applicability is independently reviewed mathematics; its entire lambda
comparison is not claimed as formalized. The high-f lemma is exact finite only.
An f-dependent sufficiently-large-n threshold can avoid its diagonal examples,
so no unconditional asymptotic lower refutation is asserted.

Expanded 19-module aggregate build/root/index: PASS. Exhaustive allowed-axiom audit: PASS, 219 declarations. All three new exact sources had also passed independent kernel replay before being copied unchanged into this repository.
The 19-module/219-declaration checkpoint is published as
`e5bbdf892cba74f0a0be8b890f1da2daec065399`. Exact CI passed, including build/index/
all-declaration audit and repository-wide kernel replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38079515337 .

## New supplied-host and enlarged-cloud wrappers

Two further frozen modules, HostGraphSampling and LargeCloudCertificate, compile;
all10 new declarations pass exhaustive allowed-axiom audit, and both modules
pass independent kernel replay. Their semantic review is
FIFTH_SEMANTIC_REVIEW.md, frozen by FIFTH_SOURCE_HASHES.json.
The first actually joins the finite sample to the blocker/MST-pruned host graph
and proves a coarse per-host weight bound. It explicitly requires every
candidate blocker set to avoid the supplied spanning host tree. The coarse
ratio argument assumes at least two host vertices and strictly positive edge
weights. It does not construct global hosts or perform subtype transport.
The second proves the actual all-fault connectivity certificate for cloud size
strictly above q; the weaker resulting scaling does not restore Theorem34.
The 21-module aggregate build/root/index passed; all229 declaring-module declarations pass the allowed-axiom audit. Exact-commit CI passed at the frozen 30ff80e commit above.

## Covered mathematical content

Actual seeded greedy correctness, literal all-pairs distance semantics, genuine
minimum denominators, missing-edge degree/connectivity, actual greedy blocking,
finite host counting, blocker/MST graph pruning on a supplied spanning host,
finite Bernoulli weighted expectation and maximizing sample, actual bipartite
counterfamilies and unbounded square-root ratios, and the corrected explicit
coarse weighted-girth lightness estimate are checked components. No final bound,
probabilistic oracle or graph-packing theorem is inserted as an axiom.

## Remaining obligations

Eulerian Steiner-forest packing and its substantial multigraph/splitting/tree-
packing dependencies; global host construction and vertex-set transport; the
global host-family weight aggregation; optimized heavy/light sampling; a valid
replacement lower-bound certificate/construction; other lower bounds; randomized
conditioning/concentration and runtime; the source multigraph extension.

A supplied host tree is a genuine premise of the current pruning theorem.
WeightedSampling alone does not handle deterministic host-tree blockers; the
new host assembly explicitly requires those blockers avoid the host. The component
results do not imply a main theorem until these obligations are discharged.

No fresh whole-paper skeptical final audit has been requested, and no public
research-site link is implied by this partial checkpoint.

## New Section 4.1 cycle-construction foundations

Eight further modules have been frozen for local gates and independent review.
`ParallelSubdivision` defines actual degree-two branch vertices; different
`colorGraph` edge sets are disjoint. `DisjointCycleFaults` and
`SubdivisionCleanColor` prove that fewer than twice the number of colors in
faults leave a color with at most one failed graph edge, then localize that
failure to one base edge. `SubdivisionPreserver` lifts actual base walks and
proves full connectivity preservation for arbitrary added core edges. It allows
branch vertices to be isolated whenever they are also isolated in the input
and does not assume the post-fault certificate is globally connected.
`CycleCertificate` specializes to the native cycle graph and proves the actual
(2f−1)-fault certificate and exact vertex count. `SubdivisionWeight` gives an
explicit dart encoding and unit-weight upper budget. `CycleLinearization`
proves the cut cycle lies in the ordinary path graph. `PotentialForcing`
telescopes a real potential along actual walks and forces retention from an
explicit fault-set potential witness.

These statements do not yet include the constructed heavy-edge potential,
rotation to all core edges, genuine optimal-denominator lower ratio, or the
joined quantitative Theorems 9–10. No new main lower bound is claimed.
Local aggregate/axiom/kernel gates and review results are recorded below when
completed; this source update alone is not evidence that those gates passed.

29-module local build/root/index: PASS with all new-source warnings treated as errors. All 284 project declarations pass the exhaustive allowed-axiom audit. All eight new exact-source independent kernel replays passed in two bounded groups. Independent semantic/source review returned PASS; its frozen report is recorded in SIXTH_SEMANTIC_REVIEW.md. This is a component review, not a final whole-paper audit. Exact-commit CI for the new 29-module checkpoint will run after publication.


## Actual Section 4.1 finite lower family

Seven new frozen modules are recorded in SEVENTH_SOURCE_HASHES.json. All sources
compile with warnings treated as errors. The complete 36-module/root/index gate
passed, and all 369 project declarations have only propext, Classical.choice and
Quot.sound as axioms. All seven new exact-source kernel replays passed in two bounded groups.
Independent source/semantic review returned PASS, recorded in
SEVENTH_SEMANTIC_REVIEW.md. Its note that four replays were pending was accurate
at review time; seventh-replays-b.log records their subsequent PASS. No
whole-paper final audit is implied.

The explicit graph is the f-colored subdivision of the native cycle of length
M=m+3, with a heavy direct edge on each base-cycle edge. Every eligible output
retains every heavy edge, by actual fault sets and a telescoping rotated
potential. The unit-edge graph is a genuine q-fault certificate for q≤2f−1.
The denominator is the actual positive minimum preserver weight. Thus the
integer-stretch family has ratio at least n/(8 f² k), and the arbitrary-real
stretch t≥1 version has ratio at least n/(16 f² t). The admissible finite range
is m+2≥2 ceil(t), with n=(m+3)(f+1). The input itself is an eligible spanner;
there are admissible graphs of arbitrarily large order for fixed parameters.

This supplies the mathematical lower-family scope used by Theorem 9. It does
not establish a literal every-n, epsilon-independent reading of Theorem 10's
lower display. Exact source conventions and this distinction are included in
the bounded review. Theorem 10's upper half and Theorem 34 remain open.

The new 36-module exact-commit CI starts after publication. The prior 29-module
commit 9aa8ae3c5166dc4d348a3dbc1431bc4bef0e6ddd has passed CI build, index and
axiom stages; its repository-wide kernel replay is still running at 20:36 UTC:
https://github.com/gbodwin/paper-formalizations/actions/runs/38082449507 .


## CI runtime-budget follow-up

The 29-module run 38082449507 reached the configured 30-minute job ceiling and
was cancelled at 20:36:59 UTC, after its build/index/axiom stages passed. Its
log shows steady sequential replay progress with no reported kernel failure;
the last announced module was SubdivisionCleanColor, whose completion must not
be inferred from that start line. Therefore this run is not a full CI PASS.

The 36-module source/semantic checkpoint was pushed as
242611f0ded9e5eace12e5e705b6a6a638697a2a, with run 38084590994. A follow-up raises
the CI job budget from 30 to 60 minutes while preserving every build, audit,
index and sequential kernel check. The exact follow-up head must pass its own
CI before it is called fully CI-green. No local proof source changed.


## Supplied spanning-packing assembly

Three further frozen sources are listed in EIGHTH_SOURCE_HASHES.json. All39
modules/root/index compile, all377 project declarations pass the allowed-axiom
audit, and the three new exact-source official kernel replays pass. Independent
component review returned PASS in EIGHTH_SEMANTIC_REVIEW.md.

The actual assignment filter derives coverage and blocker avoidance from the
supplied tree count and actual congestion. Incidence counting retains the
seed baseline1. The joined theorem uses the actual recursive output and its
actual constructed blocking map, with the denominator a genuine optimum seed;
its positivity is proved from a supplied tree. The exported ratio is
1+8fL/h, where L=8+2048/epsilon*n^(1/k).

The supplied trees all span one common vertex type, lie in the optimum seed,
number at least2f+h, and have congestion at most2. Their existence is not proved.
General subtree transport, the global Eulerian forest packing and optimized
upper assembly remain open. This is a conditional component checkpoint.

The proof-identical36-module timeout-recovery head is
cff07e88f8e16711368e3cd55c6ae658f3dfcc2b. Its exact CI38084671078 passed all stages, including repository-wide kernel
replay, verified20:56:59 UTC. The newest39-module exact CI starts after
publication. The36-modulecff07e8 checkpoint is the latest fully CI-green baseline.

## Actual induced-host transport

Three new frozen sources are recorded in NINTH_SOURCE_HASHES.json. All42
modules/root/index compile; all398 project declarations pass the allowed-axiom
audit. Allthree exact-source official kernel replays passed. Independent bounded
source/semantic review returned PASS, recorded in NINTH_SEMANTIC_REVIEW.md.
These component gates do not establish a fresh whole-paper final audit.

The new theorems restrict actual blocking data along injective vertex maps,
transport actual unordered-edge sums and total graph weights exactly, and
apply the proved sampling/pruning argument on each genuine local tree domain.
The global-order bound follows from the actual cardinality injection. Empty
candidate sets and singleton hosts are handled, rather than excluded by a
hidden size assumption. Positive weights are required only on actual global
input edges; f,k are positive naturals and epsilon is positive.

This is a per-host transport result. The dependent-family assignment/incidence
join and forest-packing existence remain open. No unrestricted main upper
bound or fresh whole-paper final audit is claimed.

## Heterogeneous supplied-subtree assembly

The next three exact sources are frozen in TENTH_SOURCE_HASHES.json. Their
strict source checks and complete45-module/root/index gate pass. All403
project declarations pass the allowed-axiom audit. Allthree exact-source official kernel replays pass. Bounded independent
semantic review returned PASS in TENTH_SEMANTIC_REVIEW.md. This does not certify any unrestricted main upper theorem.

The actual family uses finite vertex types A i and injective maps into the
original graph, with genuine trees T i on those local domains. No common
spanning vertex set or hidden minimum host size is required. A concrete
pullback/filter assignment and a restricted-index union bound derive at least
h unblocked host votes from 2f+h actual joint-endpoint hosts and congestion two.
Exact weighted incidence, including finite-enumeration normalization, yields
1+8fL/h. The actual optimum-seeded output has that bound and the EFT guarantee.
The zero-denominator case follows the existing total division convention and
is explicit; no positive-denominator claim is made for that case.

The structural packing is supplied, not constructed, and its relationship to
q remains open. Eulerian forest packing, the multigraph extension, optimized
heavy/light sampling, a Theorem34 replacement certificate and runtime remain
substantive remaining obligations.

The prior39-module exact commit81a15b8a18f50768f1eb9c8f9f4be5e0dd7902dd passed
full CI38085816118 at21:20:41 UTC, verified with matching head and all job steps.
The42-module transport head3b542ca23bd80620686efe453ed7b39e6a02fdf3 has its own
run38087103105 pending at this record's preparation; local and semantic gates
are not a substitute for that exact-commit result.

## Native forest components and exact real-eta competition

Four exact sources are frozen in ELEVENTH_SOURCE_HASHES.json. Complete49-module
strict source/root/index and all428 declarations' allowed-axiom audit pass.
All four exact-source official kernel replays pass. The independent bounded
semantic review in ELEVENTH_SEMANTIC_REVIEW.md returned PASS after verifying
the frozen hashes and actual graph semantics. None of these gates constitutes
the fresh final whole-paper audit.

Native connected components provide the actual varying tree domains. Projection
of a fixed edge's component-host indices to forest indices is injective, so its
congestion cannot increase. Each forest connecting two actual endpoints supplies
its canonical component as a genuine host. The seeded-output join uses proved
native(q+1)-edge connectivity for each missing input edge of a q-fault preserver.
It still requires supplied acyclic subgraphs preserving these pairs, enough
forest indices, congestion two and q+1≥2f+h. Their existence remains open.

The separate rounded wrapper uses the actual real budget floor((2+eta)f), proves
its exact decomposition2f+floor(eta f), and derives the uniform finite coarse
bound1+8L/eta from votes floor(eta f)+1. Here L=8+2048/epsilon*n^(1/k), eta>0,
and the supplied subtree packing is explicit. Baseline1 is retained with no
upper restriction on eta. This does not prove a printed lambda comparison or
the optimized heavy/light upper bound. All zero-denominator handling remains
explicit through the existing ratio convention.

The prior 42-module and 45-module exact heads both passed full CI, verified
2026-10-10 at 21:50 UTC: runs 38087103105 and 38088236308 respectively.
The latest full-CI baseline is 45 modules at
36c403565bb2c911408b368df0979acc417100ee. This new 49-module checkpoint
requires its own exact-commit CI after publication.

## Actual simple-subdivision doubling and projection

Seven new sources are frozen in TWELFTH_SOURCE_HASHES.json. Their strict
source builds, the 56-module root/index gate and all 470 declarations'
allowed-axiom audit passed at 22:11:15 UTC on 2026-10-10. The local gate used
unchanged prior module objects rather than rebuilding all 56 sources. Official
new-module kernel replay and independent semantic review are separate gates.

Actual selected-color half-edge faults project injectively to original edges.
Native core edge-connectivity is multiplied by the copy count. With two copies,
all actual degrees are even; branch vertices have degree two and cannot belong
to a nontrivial connectivity island of threshold at least three.

Complete two-half-edge paths, rather than dangling branches, define the core
projection. Actual core walks project with stationary reversals allowed. Native
spanning forests are constructed without losing reachability. Each original-edge
host is charged to a distinct copy through an actual half-edge, so edge-disjoint
subdivision subgraphs yield congestion at most two. The same optimum-seeded
output then satisfies the earlier finite coarse ratio bound, under an explicit
supplied edge-disjoint connectivity-preserving subdivision family.

This discharges the simple doubling/projection interface, not the external
forest-packing existence theorem. No connected Euler-tour claim is made for
disconnected input, and no multigraph main-upper extension is inferred.
Separately, positive actual input-edge weights make any true preserver weight
positive whenever the input is non-edgeless. Thus the explicit zero-denominator
case occurs exactly for an edgeless input under those hypotheses.

All seven official new-module kernel replays now pass in two bounded groups,
completed at 22:13:57 and 22:15:26 UTC. Exact hashes remain frozen. The
independent seven-file component semantic review returned PASS at 22:29:26 UTC,
recorded in TWELFTH_SEMANTIC_REVIEW.md. It independently matched production
hashes and Git blobs and checked the actual graph semantics and degenerate
domains. No final whole-paper audit or unconditional upper theorem is implied.


## Actual cut and contracted-core foundations (newer packet)

Eight exact sources are frozen in THIRTEENTH_SOURCE_HASHES.json. Their individual
strict diagnostics pass. All eight new production sources, the 64-module
root/index and the exhaustive 530-declaration allowed-axiom audit passed at
22:49:48 UTC. The local gate reused unchanged earlier objects; it did not
freshly rebuild every previous source. The first four official new-module replays passed at
22:51:47 UTC. That window also strictly rebuilt a documentation-only precision
change in the parallel-edge example (equal endpoints use reflexive reachability).
The final four replays passed at22:52:59 UTC. The independent eight-file
semantic review returned component PASS at22:57 UTC, recorded in
THIRTEENTH_SEMANTIC_REVIEW.md. Exact64-module CI remains running.

The packet uses actual finite cuts, native graph edge identities through
contraction, and genuine surviving walks after deleting original edge IDs.
It constructs a minimal deficient core from native basic-instance hypotheses,
proves its contracted fault connectivity, and derives the actual crossing-edge
partition criterion. Parallel edges and loops are counted correctly; simplifying
adjacency occurs only after a specified deletion. The final partition wrapper
explicitly uses nontrivial surjective partitions. A singleton partition has
zero required crossing edges. Packing existence is still unproved.


## Integral general-multigraph core extension (newer packet)

Four frozen sources are listed in FOURTEENTH_SOURCE_HASHES.json. All four strict
production builds,68-module root/index and exhaustive548-declaration allowed-
axiom audit passed at23:06:32 UTC. The four exact official kernel replays passed
at23:07:54. Earlier objects were reused unchanged; this local gate is not a
fresh full68 rebuild. Independent four-file semantic review returned component PASS at23:21:37,
recorded in FOURTEENTH_SEMANTIC_REVIEW.md. It matched all four published hashes
and all64 prior proof sources. Published c3a3aae006f140cfb1b007974320f0d3b3ea90d6
has exact CI38094267232 running; the review-report commit has its own separate CI.

These sources extend integral minimal-core selection and the genuine contracted
fault-connectivity/partition-budget join to native finite multigraph inputs.
Basicness and retained core membership use the actual vertex set. Parallel
identities remain distinct. The full-vertex condition is explicit before
interpreting a finite ambient-type cardinality decrease as a graph-order
statement. The weighted fractional source lemma and packing/splitting/expansion
existence remain open; no main upper bound is completed by this extension.

The proof-identical reviewed 56-module report commit26f58f279857575e28088bc92605dd01bd70ea49 also passed its own complete exact CI38091887677 at23:05:46 UTC, including all repository kernel replays. This is separate from the pending64/68 statuses.


## Full exact64 CI and newer native forest packet

Both64-module exact runs have now passed every step, including all repository
kernel replays: reviewed report15f6e7cfae93c49cb836c6b91f543b9c1ea9c09f,
CI38093343350 completed23:21:09; proof9752254f87cad1849129b264b8ee2cd08fcc9afc,
CI38093142749 completed23:23:00. Both heads, terminal states and steps were read
back23:26. Thus64 modules/530 declarations is the full-CI reviewed baseline.
Reviewed68 own exact CI remains pending.

Four new source hashes are frozen in FIFTEENTH_SOURCE_HASHES.json. All four
strict production builds,72-module root/index and exhaustive577-declaration
allowed-axiom audit passed23:24:22. All four official kernel replays passed
23:27:08. Previous68 proof sources and their objects were reused unchanged;
this is not a clean full72 local rebuild. Fresh four-file semantic review returned component PASS at23:33:43, recorded
in FIFTEENTH_SEMANTIC_REVIEW.md. It independently matched all four frozen and
published117130f source hashes and all68 prior proofs. Exact72 CI38095126415
is still running; the review-report commit has its own separate CI. No whole-paper final audit or completion claim is implied.

The new construction selects actual original identities, preserves all actual
vertices and exact reachability, proves every retained edge a native bridge,
and constructs a spanning tree with its exact count when input is connected.
The final finite connected-edge lower bound assumes finite actual vertex and
edge sets. General tree packing, Eulerian forest packing, splitting and expansion
remain open. The external weighted fractional core theorem is still outside scope.


## Full exact72 CI and newer finite packing foundations

Exact proof checkpoint117130f1621f40a39749d0dc27145cdb4f2d4a71 passed full
CI38095126415 at23:42:21, including all repository kernel replays. Run head,
terminal result and every step were independently read back23:44. Its semantic
review report is recorded atf8ed484cb46e01e6d71262ae804310eb228c11a0, whose own
CI38095501137 remains separate and pending. The68 proof checkpointc3a3aae also
passed full CI38094267232 at23:42:14. The full-CI reviewed baseline is now72
modules/577 declarations, without any whole-paper completion claim.

Six exact new sources are frozen in SIXTEENTH_SOURCE_HASHES.json. All six strict
production builds,78-module root/index and exhaustive631-declaration axiom audit
passed in two bounded windows, completed23:42:13 and23:43:58. The first three
official replays passed23:45:02; the last three passed23:50:37. Earlier72 proofs
and their objects were reused unchanged, not freshly rebuilt by this local gate.
Fresh six-file semantic review is queued after the allocated minor-free review
and Flow constructor helper. Future exact78 CI is a separate pending gate.

The new scope is actual partition crossing/one-tree sufficiency, true component
refinement with least-color priority and an explicit n² termination bound,
conditional local edge-exchange walk substitution, and actual forest-density
nonbridge forcing. The replacement route is explicitly supplied in the local
exchange helper, not assumed to exist for the full packing construction. The
source's general packing/maximality contradiction and finite-level cycle selection
are still open, as are Mader splitting, forest expansion and full main upper bounds.

## Frozen78 semantic review (11 October,00:06 UTC)

The fresh six-file source/semantic review returned component PASS and is recorded
in SIXTEENTH_SEMANTIC_REVIEW.md. It matched all frozen and published9b2a722 source
hashes, all72 prior proof bytes, the exact78-module index and all recorded gates.
No semantic blocker was found. The exchange route remains an explicit premise,
and the density theorem produces a native nonbridge rather than a complete
crossing-cycle/exchange construction. General packing and full main scope remain open.
Exact78 proof CI38096551852 is running; a report commit has a separate exact run.

The reviewed72 report commitf8ed484 also passed full CI38095501137 at00:01:30,
with all steps read back00:04. Its full72 clean build and every repository kernel
replay passed. Thus both the72 proof and report checkpoints are fully green.

## Actual terminal quotient packet (11 October,00:09 UTC)

Seven new sources are frozen in SEVENTEENTH_SOURCE_HASHES.json; all78 earlier
proof files are unchanged from reviewed1d33c9e705ad48570d4f9787b5e19e8a7a1c475c.
All seven strict production builds passed in two bounded groups, and the85-module
root/index plus exhaustive667-declaration allowed-axiom audit passed00:09:34.
Prior78 objects were reused unchanged; this is not a clean full85 local rebuild.
All seven official kernel replays passed in two bounded groups, at00:10:57 and00:12:37. The fresh seven-file semantic review returned component PASS at00:17:30 (SEVENTEENTH_SEMANTIC_REVIEW.md).

The packet proves the native induced-core partition premise, contraction of
actual native forests along genuinely connected fibers, exact quotient-tree
counts, original-walk lifting, exact colored crossing-identity accounting and
the last-color terminal density/alternate-path obstruction. Actual vertex images,
finite target domains and explicit connected-fiber hypotheses are preserved.
The source's minimum-level exchange and maximality contradiction remain open,
as do general packing, splitting, Steiner forests, expansion and main bounds.

## Frozen85 semantic review (11 October,00:17:30 UTC)

The independent seven-file source/semantic review returned component PASS with
no blocker. It verified exact frozen/checkpoint9c2e5d1 hashes, prior78 proof byte
equality, the exact85-module index and all recorded gates. The terminal theorem
returns an actual last-color crossing identity and same-color reachability after
deleting that same identity. First-color trees, genuine connected fibers and
surjective labels remain explicit induction-step premises. Label construction
from terminal iterates, minimum-level selection, exchange/maximality and full
packing are not claimed by this85 packet. Exact proof CI38097692047 is running,
separately from any report-commit run; full reviewed72 CI remains the baseline.

## Full78 CI and next finite-level packet (11 October,00:30 UTC)

Exact78 proof CI38096551852 at9b2a722589b4484ccacb897f0357be1dd07cc3b2
completed successfully00:23:23. Head, terminal state and every step including
clean build and repository-wide kernel replay were read back00:25. The fresh
six-file semantic report is published at1d33c9e705ad48570d4f9787b5e19e8a7a1c475c,
whose own exactCI38097331985 remains pending. Full-CI reviewed baseline:78/631.
Reviewed85 proof9c2e5d1 and report33803cb have separate CIs running.

Six new sources are frozen in EIGHTEENTH_SOURCE_HASHES.json. Strict production
builds passed in two bounded windows,00:26:44 and00:28:22. The91-module root/index
and exhaustive704-declaration allowed-axiom audit pass. Prior85 sources and
objects remain unchanged and were reused; no clean full91 local rebuild.
All six official kernel replays passed in two bounded groups, by00:34:17 and00:35:24. Fresh six-file semantic review and exact91 CI remain pending.

The packet constructs finite occupied-block labels and real terminal fiber
connectivity, selects a minimum finite-level native nonbridge, and constructs
an alternate same-color route inside its level using cut symmetric difference.
The joined source countercase no longer takes labels, fiber connectivity, a
minimum edge or replacement path as input. The exact least splitting color is
also shown to be an earlier color. Initial first-color trees and last-color
disconnection remain the explicit inductive countercase. Full exchange,
maximality contradiction, packing, splitting, expansion and main bounds remain open.

## Independent91 component review (11 October,00:40 UTC)

Proof472def1a65d2a35113a21739955cf8285c20a6fc, tree4d47500dc99d0e0a7e818281331c24ed10d3362f, was published and read back00:36. Exact CI38099004674 is running. The fresh six-file review returned COMPONENT PASS00:40:40; see EIGHTEENTH_SEMANTIC_REVIEW.md. It independently verified current/frozen/published source hashes, prior85 proof equality and the exact91 root/module index. No new proof-source blocker or correction was found. The inherited HostCounting statement-map omission and stale replay note were corrected after review, without changing any Lean source. All91 modules are now represented in the human statement map.

The78 report commit1d33c9e exact CI38097331985 also passed fully at00:34:56; head and every job step were read back00:40. Thus both78 proof and report commits are fully CI-green. Local gates, component semantic review and exact full CI remain distinct. Tree exchange/maximality and the main forest-packing/splitting prerequisites remain open in the91 scope.

## Native lower exchange: frozen97 packet (11 October,00:51 UTC)

Latest full-CI reviewed baseline is85/667: proof9c2e5d14206573748e1054040807f84d24d680da, CI38097692047, full success00:39:08. Exact head and every successful job step, including clean build and all repository kernel replays, were read back00:45. The91 proof/report commits472def1/89bda02 have separate exact runs38099004674/38099333865 pending.

Six new strict production builds passed in two bounded groups, with completion read by00:48:12 and00:50:12. The97-module root/index and exhaustive743-declaration allowed-axiom audit pass. Prior91 proof sources and objects remain unchanged and were reused in local gates; a full clean97 rebuild is reserved for exact CI. Frozen hashes are NINETEENTH_SOURCE_HASHES.json. All six official kernel replays passed in groups, completion confirmed by00:51:27 and00:54:21. The first final-group attempt was busy75 and started no process. Fresh six-file semantic review and exact97 CI remain pending.

The packet constructs a lower-level native exchange edge and an actual within-level route, certifies the exchanged native tree, and proves exact global-level agreement under original-edge restriction and finite-terminal truncation. Generic all-stage reachability preservation retains explicit replacement-route and split-boundary premises. Tree/block-separation inputs remain the source's local inductive countercase. Concrete swapped coloring and all-color assembly, lexicographic maximality, general tree/Steiner-forest packing, Mader splitting, expansion and main upper bounds remain open. No full-paper completion or final audit is claimed.

## Independent97 component review (11 October,00:59 UTC)

Published proof52cd0ab93531cbbbe5741842ab70b55aebe36c06, tree13a6648ec36ba5eafeaf416fccdd3c54de0f7781, was read back00:55. Exact CI38100055355 is running. The fresh six-file reviewer returned COMPONENT PASS00:59:21, independently verifying frozen/current/published hashes, all91 prior proof sources unchanged, and exact97 root and statement-map coverage. No semantic blocker or proof change. See NINETEENTH_SEMANTIC_REVIEW.md. The generic stage-preservation helper retains explicit route/boundary premises; the lower-edge join constructs its own exchange witness and within-level route. Concrete swapped-color assembly, maximality and general packing remain open in this97 scope.

The85 review-report checkpoint33803cbc003339d7acc821810cfd74fc19e22c43 also passed full exact CI38098040812 at00:51:16, all steps verified00:56. Both85 proof and review-report commits are now fully CI-green. Newer91/97 exact runs remain pending.

## Recovery and full97 CI (11 October,15:04 UTC)

After the preview-limit interruption, the existing workspace and all partial
proofs were recovered unchanged. Remote/local HEAD remained reviewed97
e607ac12ac0023aaeb4616cedeababb92fca0850. Both97 exact runs completed successfully:
proof52cd0ab, run38100055355 at01:22:59; report e607ac1, run38100403078 at01:34:53.
Their exact heads and every clean-build/index/axiom/kernel-replay job step were
freshly read back15:04. Both91 runs38099004674/38099333865 also passed completely.
Full-CI reviewed baseline is97 modules/743 declarations. No active Light child
or compiler and no competing branch writer was observed.

The three frozen100 sources and manifests were preserved; all frozen/current
hashes and all97 unchanged prior proof bytes were rechecked. The new strict
production/root/index/765-declaration audit gate passed, completion confirmed
15:06:43. Prior97 objects were reused locally; no full clean100 local rebuild
is claimed. The separate three-module official kernel replay group passed, completion
confirmed15:10:10. The fresh bounded semantic review and exact100 CI remain pending. TWENTIETH_SOURCE_HASHES.json identifies the freeze.

This packet constructs actual two-color transformations and the changed-color
tree, then a true finite lexicographic maximum of actual earlier-tree colorings.
The inductive seed and finite horizon are explicit. The strict improvement and
maximality contradiction, new-sequence rigidity, full induction, packing,
splitting, expansion and main upper bounds remain open.


## Independent100 component review (11 October,15:17 UTC)

Proof5e40d7fb299f03c7555da20f5b62ae0ec6b4d94c, tree970aa85b7591a2955b626bbdbfa3ef66a73801dc, was published and read back15:11. Exact CI38150227125 remains in progress at15:17. The fresh three-file review returned COMPONENT PASS, verifying all frozen/current/published hashes, all97 prior proof bytes unchanged, and exact100 root/index coverage. See TWENTIETH_SEMANTIC_REVIEW.md. No proof source changed.

The review explicitly checks actual native swap identities, genuine changed-color trees, exact global level and boundary, and finite maximization over all admissible colorings. Related-pair counts detect strict comparable-refinement improvements; equal counts alone do not identify partitions. The optimizer's inductive seed and finite horizon remain explicit. New-sequence comparison/rigidity, strict improvement, full countercase assembly and induction remain outside this freeze. General packing, splitting and main upper bounds remain open. Full exact-CI baseline remains reviewed97/743.


## Frozen106 actual maximality contradiction (11 October15:58 UTC)

Six new exact sources (465 lines) pass strict production builds. The106 root,
module index and all800 defining-module declarations pass the allowed-axiom
check; the allowed set remains propext, Classical.choice, Quot.sound. All six
official kernel replays pass in two separately bounded three-module groups.
No prior100 mathematical source changed. See TWENTYFIRST_SOURCE_HASHES.json,
TWENTYFIRST_ENTIRE_SOURCE_HASHES.json and twentyfirst-{build,replays-a,replays-b}.log.

The route-preservation comparison never equates partitions from equal counts
alone: actual component inclusion first gives comparable refinements. The
source countercase supplies only the real partition criterion and k earlier
spanning trees, and an actual disconnected last-color pair. The finite-level
edge, earlier splitting color, replacement edge/routes, genuine changed tree,
admissibility and strict improvement are all constructed. Pairwise last-color
reachability follows for a truly maximal admissible coloring. Nonempty global
connectedness, the k-induction and complete packing-family assembly are not
silently inferred. General Mader splitting and main upper bounds remain open.
