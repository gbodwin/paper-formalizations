# Eighteenth bounded semantic/source review

Date: 2026-10-11 UTC. Review completed against the six-file freeze below.

Verdict: **COMPONENT PASS. No semantic blocker found in the six frozen modules.** The packet constructs genuine finite-level and within-level replacement-route witnesses for the stated colored-decomposition countercase. It does not complete tree exchange, packing, or the paper's upper bounds.

## Scope and independently checked identity

I read all 401 lines of the six production sources, the relevant native bridge, partition, refinement, terminal-quotient, and exchange-connectivity dependencies, and the underlying Mathlib edge restriction/deletion, simple adjacency, and cut symmetric-difference definitions. I compared the argument with the pinned Kaiser source, especially pages 2–4. I invoked no compiler/checker and changed no source, repository state, GitHub content, or Site. The only file written is this report. New tree-exchange drafts are excluded.

The canonical review manifest, production frozen manifest, current source bytes, exact local Git checkpoint bytes, and independently fetched GitHub source bytes agree for every file. I independently recomputed SHA-256 and Git blob identities of the fetched contents:

| Module | SHA-256 |
|---|---|
| NativeEdgeLevels | a88c2a4f14d3e42ded4b079520b5f6012edca5f9b5019f20501baabf874af56e |
| NativeNonbridgeCore | 9529308a5272bbd5f1f2a5dd3bc35c4abdd6e873003feff27f084b1b3fdb71ef |
| NativeMinimumCycleLevel | ae8d13da621c2bca47514c669eedd9055cb2cc2fe35c7a60a33fc2ccd87c1be7 |
| NativePartitionLabels | c39e8c5fcc8a44034f71450ca3c6f92eb2e21770f091eeed38f2e85ec2b5bacc |
| NativeRefinementCycleWitness | 6920fa7610d66f7c2d765a488db28428875bf450cf9cba21d20ba1882bc5848a |
| NativeSplitColor | e39b8f989bf2c656e41cbf63ef4779b78a7d220696ecaa54558f6e7eca28f73a |

GitHub's commit and branch APIs independently confirmed at approximately 00:38 UTC:

- Repository: `gbodwin/paper-formalizations`.
- Branch: `light-eft-spanners-checkpoints`.
- Published proof commit: `472def1a65d2a35113a21739955cf8285c20a6fc`.
- Commit tree: `4d47500dc99d0e0a7e818281331c24ed10d3362f`.
- Parent: `33803cbc003339d7acc821810cfd74fc19e22c43`.

All 85 production Lean module files from that parent are byte-identical in the current working tree and checkpoint; the proof diff adds exactly these six modules. Earlier reviews are inherited by that equality, not repeated in full. There are exactly 91 production module files and 91 distinct root imports, with identical sets and no duplicates or extra imports. The root diff consists only of the six additions. The published root, frozen manifest, and axiom-audit source were also fetched independently and exactly match local bytes. The repository working tree was clean during inspection.

The exact root/module index should not be confused with the human statement map: its module union contains 90 names because `HostCounting` is unmapped, as it already was at the 85-module baseline. All six new modules are mapped. This inherited documentation omission is not a six-file proof blocker; do not describe the statement map itself as exhaustive over all 91 modules. Its newest narrative also still says replays are pending, although the committed replay logs show completion.

## Validation evidence and limits

The local workspace, production, and committed copies of all four eighteenth gate logs match. The strict-build scripts use `set -euo pipefail`, compile the six sources with `-DwarningAsError=true`, and use the wrapper's `-DautoImplicit=false`. The second group compiles the aggregate root, runs the module-index check, and runs the project-owned-declaration axiom collector. Its log records 704 audited declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`, followed by index success and `EIGHTEENTH_AGGREGATE_GATE_PASSED`.

Both replay scripts invoke the official Lean `leanchecker` wrapper. Their logs contain individual successful replay markers for all six modules. This corroborates the owner's reported strict-build completion at 00:26:44/00:28:22 and replay completion at 00:34:17/00:35:24. This review inspected those records rather than re-running the gates; the first build-group log does not independently encode its process exit status. Prior 85 objects were reused. There is no claim here of a clean full-91 local rebuild or successful exact-commit remote CI. Those are separate gates.

The audit source examines collected transitive axioms of declarations owned by project modules. No `sorry`, `admit`, custom `axiom`, unsafe declaration, or implementation override appears in the six inspected sources. No final packing/exchange conclusion is introduced as an assumption.

## Source correspondence and semantic findings

Primary source: [Tomáš Kaiser, A short proof of the tree-packing theorem, arXiv:0911.2809v3](https://arxiv.org/pdf/0911.2809v3). I independently verified the pinned PDF SHA-256 `4bef0841bbfe41cc93c2edfa33ec6649c56f7810e6e5dc932e053dec1a85808b` and extracted-text SHA-256 `58342327af7f9d3cd5586549b12eb2ea53ab7018fc2a557dc6fc3859ffcde506`. The source explicitly permits loops and parallel edges. Page 2 defines least-color refinement and edge levels; page 3 derives a terminal-crossing cycle edge and chooses minimum level; pages 3–4 use a within-level replacement route in the exchange argument.

### 1. Actual internal edges and a bounded level sentinel

`edgeInside` requires an actual native `IsLink` witness and equivalence of its actual endpoints. `edgeInside_iff` uses native endpoint uniqueness up to reversal and symmetry of the setoid, so this condition is orientation-independent. It does not assign phantom identities artificial endpoints.

`internalStages` is the explicitly finite set of internal stages from 0 through N. `edgeLevel` is its maximum when nonempty, with a default zero otherwise. All level-membership/boundary results assume initial internality, excluding misuse of that fallback. The crossing-terminal premise then proves level < N, internality at the selected stage, and separation at the next stage. The maximum argument itself does not require monotonicity; later containment arguments correctly supply it separately.

N is a terminal sentinel, not the literal mathematical infinity from the article. For actual initially internal edges, terminal internality puts N in the stage set, so the maximum is N. Only levels < N are called finite here. A phantom edge, arbitrary non-antitone sequence, or default level zero does not justify source-style infinite-level reasoning. In the joined theorem the sequence is the actual stable refinement sequence, so this finite encoding supports the claimed source obligation.

### 2. Bridge removal preserves a real native replacement route

Mathlib's `IsBridge e` means that the singleton identity set is a genuine vertex cut. Its cut symmetric-difference theorem operates on native edge identities. Finite induction therefore proves that a finite set of bridges is a cut; symmetric-differencing a cut with all its other bridge members forces the remaining member to be a bridge.

`nonbridgeCore` restricts the original graph to nonbridge identities while preserving all actual vertices. Although nonexistent ambient identities can satisfy the predicate, restriction intersects with the original edge set, so they never become edges. If a retained edge became a bridge, the original cut has only original bridges among its other members, contradicting the retained edge's original nonbridge status. The finite-edge-domain hypothesis `[Fintype E]` is explicit where this cut enumeration is used.

Applying the already-reviewed native bridge/deletion equivalence constructs endpoint reachability after deleting the exact chosen identity from this core. Restriction and deletion happen before conversion to simple adjacency. Thus a different parallel identity remains a valid one-step alternative; a two-edge native cycle is not erased by premature simplification. Loops correctly have reflexive endpoint reachability and are never bridges. This proves a replacement route, not a stored native cycle object.

### 3. Minimum level and containment of the alternate route

`exists_minimum_cycle_level` minimizes over all present native nonbridges, not all ambient identities or a supplied cycle. Its explicit inputs are `[Fintype E]`, an antitone partition sequence starting at top, N, and some terminal-crossing present nonbridge. Top initiality supplies internality for every actual edge. The supplied crossing witness makes the selected minimum strictly less than N; the selected edge is then shown to cross the terminal partition and satisfy its exact next-stage boundary.

Every adjacency in the constructed nonbridge-core route has an actual original nonbridge identity c. Minimum selection gives level(e) ≤ level(c). Since c is internal at its own maximum stage and R is antitone, c is internal at level(e). This is the correct order direction. Mapping the whole route into `blockGraph` therefore keeps every step within one level(e) class; equivalence transitivity keeps every visited vertex in the selected endpoint block. All route identities avoid e.

This route supplies the last-color replacement-connectivity obligation used on page 4. The claim needs reachability, so a stored simple cycle certificate is unnecessary here. It does not, by itself, supply the other-color fundamental cycle, the exchanged tree, or a native cycle datatype theorem. Loops cannot be selected as a finite-level edge because a loop stays internal to every equivalence relation; parallel alternatives remain supported. N = 0 cannot satisfy the terminal-crossing premise with top initiality.

### 4. Genuine occupied-block labels and connected fibers

`exists_actual_partition_labels` takes `[Finite G.vertexSet]` and `[Nonempty G.vertexSet]` and constructs labels through the actual quotient of the setoid and a finite equivalence. Surjectivity is over actual vertices; kernel equality is proved using quotient equality in both directions. Arbitrary ambient nonvertices receive one chosen actual label, which creates no extra quotient blocks. No finiteness of the unused ambient vertex type is assumed.

The least-color iterate is proved antitone from the actual refinement step. `exists_native_terminal_labels` then uses the previously established quadratic stabilization bound for that same iterate, constructs its labels, and derives every color's within-fiber reachability from the fixed-point characterization of component refinement. Neither labels, a desired terminal partition, nor fiber connectivity are inputs. The bound concerns the number of refinement rounds; classical quotient choices and finite selections are not an executable polynomial-time algorithm.

### 5. The joined countercase has appropriate hypotheses

`exists_refinement_cycle_witness` explicitly assumes finite actual vertices, finite ambient edge identities, a coloring by `Fin (k+1)`, the actual all-partitions `TreePartitionCriterion G (k+1)`, first k color classes whose actual edges are all bridges and whose simple adjacency is connected, and an unreachable actual pair in the last color. Restriction retains the full actual vertex set, so those first-color conditions are genuine native spanning trees, including exclusion of loops and parallel cycles through the bridge condition. The partition criterion counts original crossing identities of every surjective finite labeling; it is not an assumed packing result.

The actual pair supplies nonemptiness. The theorem internally constructs terminal labels and fibers, invokes the prior native quotient/density obstruction, transfers its unequal labels to terminal separation via exact kernel equality, and invokes the minimum-level construction on the last-color native restriction. Its output contains the finite bound, a present last-color nonbridge, the exact level boundary, minimum among all present last-color nonbridges, and the same-color route avoiding that identity within its level block.

No minimum edge, cycle, route, quotient labels, or fiber connectivity is a premise of this joined theorem. First-color trees and last-color disconnection remain a conditional inductive countercase. It does not construct the initial decomposition or choose a maximal one.

### 6. The exact earlier splitting color

`exists_earlier_splitting_color` takes actual internality of a last-color edge and its separation by the next least-color refinement. Separation forces a nonempty splitting-color set. Its selected minimum cannot be the last color: the edge itself joins its endpoints inside the current block in that color, with the loop case handled by reflexivity. `Fin.eq_castSucc_of_ne_last` then returns an earlier color with equality to the exact minimum, equality of its component refinement to the actual next step, and separation of the endpoints.

This is stronger than producing some earlier splitting color. No `k > 0` premise is smuggled in: at k = 0 the stated separation premises are impossible, consistently preventing an inhabitant of `Fin 0`. The result is a separate conditional lemma; the six-file packet does not package it and the cycle witness into a completed exchange theorem.

## Remaining boundaries

The next unfinished work remains construction and certification of the actual earlier-color tree exchange, its lower-level edge and replacement route, preservation/comparison of the relevant refinement stages and least colors, and the lexicographic maximality contradiction. First-color induction assembly and general Nash-Williams/Tutte packing remain open. Mader splitting, Steiner expansion, weighted/fractional issues, the general Eulerian Steiner-forest result, runtime claims, and the Light EFT main upper bounds remain open as previously scoped.

This is an independent bounded component review of the frozen six-file checkpoint, not a final audit or whole-paper completion claim.
