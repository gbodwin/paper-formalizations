# Directed nonnegative-weight preserver checkpoint — pending independent review

Tested source: **58116f153e48e57a055767cabfd1bc89f622214d**.

The preserved directed-distance draft has been recovered, checked and strengthened with `SlackSparsification.Directed.exists_exact_input_preserver`. For finite vertices, nonnegative directed arc weights, and an arbitrary finite demand set, it constructs a subset of actual input arcs preserving all demanded distances with explicit bound

```text
(14*n / (1 - (1/2 : ℝ)^(1/2 : ℝ))) * (p : ℝ)^(1/2 : ℝ).
```

Shortest paths, hitting sets, in/out trees and the amplification construction are internal to the proof. Empty vertices/demands, unreachable demands and zero weights are included. The new `distance_ne_top_iff` connects finite distance to existence of an actual allowed directed walk. This is a **nonnegative-weight existence theorem**, not a claim about arbitrary signed weights, runtime, or whole-paper completion.

[Statement reconciliation](STATEMENT_RECONCILIATION.md) identifies the exact original statements and the six partial modules preserved on `distance-sparsification-checkpoints` at `b7a01e2ebe0582fb5417af1bdafecdb0d27a4052`. [Recovery manifest](recovered-source-manifest.json), [original snapshots](evidence/recovered-originals/), and [comparison](recovery-comparison.json) preserve every partial. Three recovered files require only explicit unused-instance/deprecated-name/style repairs; DirectedExact and both reachability partials remain byte-identical. The two reachability modules are preserved but **not compiled or accepted in this checkpoint**, and the sourcewise reachability premise remains unproved. No accepted +6 leaf or aggregate source was edited.

The stronger printed wording “distance preserver” in Theorem 5.2 differs from the cited source's reachability theorem. This is the existing source-comparison correction, not an established false-theorem result. The reachability continuation must supply the sourcewise result for both the input relation and its reverse when routing into and out of roots; a hypothesis for only one fixed orientation must not silently be treated as a uniform theorem for all graphs. No such continuation is claimed here.

[Integrated +6 acceptance record](INDEPENDENT_PLUS6_ACCEPTANCE.md) records the parent's independent clean-CI review and resolved artifact retrieval. Thirteen CI object hashes differed from local objects, so bit-for-bit reproducibility is **not** claimed. All original evidence/provenance remains unchanged.

## Validation

Official Lean **4.34.0**, commit **293d5d0c0c3f3dded4688b3ccd6a33939ac5102b**; Lake **5.0.0-src+293d5d0**; mathlib **5ed2965256430c3649e86755f9576b54eca72435**. All nine pinned dependencies are clean and unchanged. Resource checks: 23 GiB free disk, 16 GiB RAM limit, four CPU quota cores; no compiler/checker active at entry or handoff.

| Module | Final compilation attempt | Result | Individual replay |
| --- | --- | --- | --- |
| ConsistentTiebreaking (unchanged imported support) | 002 | exit 0; eight inherited unused-section-variable warnings | PASS |
| DirectedBasics | 005 | strict exit 0, no diagnostics | PASS |
| DirectedTrees | 007 | strict exit 0, no diagnostics | PASS |
| DirectedExact | 008 | strict exit 0, no diagnostics | PASS |
| DirectedComplete | 010 | strict exit 0, no diagnostics | PASS |
| DirectedPreserver | 013 | strict exit 0, no diagnostics | PASS |

Compilation uses the official binary with `-j1 -DautoImplicit=false -DwarningAsError=true --root=<source-root> -o <object> <source>`. The unchanged support file was first tried strictly (attempt 001 failed on its eight inherited lints), then compiled with default linters, preserving every warning. It was not edited or lint-suppressed. Every exact command, LEAN_PATH, final source snapshot, source/object hash, exit status and raw diagnostic is retained. No default `lake build` or runtime shim was used.

Each successful leaf was subsequently replayed sequentially with `lake env leanchecker -v <exact-module>`, after checking that the name selects a single leaf. All six replays passed. The separate verifier imports only `DirectedPreserver` and audits its actual project import closure. It passed with **119 actual-owner roots**, **18,093 recursive constants**, **14 opaque bodies**, and only **`propext`, `Classical.choice`, `Quot.sound`**. It traverses types and definition/theorem/opaque bodies, including private constants, and rejects unsafe/partial dependencies and unapproved axioms. The audit's “82 new declarations” means its six selected modules (including the unchanged imported tie-breaking module), not 82 newly authored declarations; see [per-owner counts](audit-coverage.json).

## Failed attempts and sequencing incident

All thirteen numbered compilation records are retained. There was additionally one prematurely started wrapper check while the DirectedComplete compiler was still finishing. It immediately failed on a missing dependency object. This briefly violated the single-compiler sequencing requirement; no successful result came from that attempt. Both calls initially allocated attempt number 009, so the wrapper's runner JSON was overwritten by the completing dependency's diagnostics. The tool-reported wrapper diagnostic, unchanged source snapshot, explicitly reconstructed metadata, and duplicate raced copy are preserved in [the incident record](evidence/SEQUENCING_INCIDENT.md) and adjacent files. The reconstructed record is not presented as the original lost runner JSON.

Both processes exited before continuing. The runner and replay/audit script now use the same exclusive nonblocking process lock, held across attempt allocation and the awaited compiler/checker calls. The corrected DirectedComplete and wrapper checks then passed, and all final individual replays plus the audit ran sequentially under that lock. No parallel agents or CI job were started. Other failed attempts concern unused-instance/style/deprecation diagnostics or a finite-set API elaboration mistake; no proof hole, new axiom, or linter suppression was introduced.

## Evidence and pause point

- [Source/object hashes](source-object-hashes.json), [preservation checks](preservation.json), [dependency pins](dependencies.json), [toolchain hashes](toolchain-binary-hashes.json), [environment](environment.json).
- [Raw evidence](evidence/), including every attempt and individual replay; [warning classification](warning-classification.json).
- [Dependency chunk manifest](evidence/dependency-chunk-manifest.json), which reconstructs the raw recursive TSV byte-for-byte.
- `checkpoint-evidence-hashes.json` covers all other checkpoint files.

Source and evidence are separate additive `[skip ci]` commits on the already guarded development branch. The certified branch, original partial branch, accepted integration source/evidence, and websites remain unchanged. The aggregate continues to represent the accepted +6 checkpoint; new directed modules are deliberately checked through their isolated audit entry point pending review. No automatic CI is requested. All compiler/checker processes are idle at handoff. The next step is independent review of this bounded directed-distance result, not further optional development.
