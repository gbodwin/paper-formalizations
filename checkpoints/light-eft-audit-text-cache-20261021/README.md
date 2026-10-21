# Pure name-text cache for decoder audit serialization

Source-only candidate for independent sequential review against515a39d1. Fast is
off. No compiler, local admission, push, CI or worker was launched. Existing
source checkpoints and failed run39539245748 evidence remain preserved. The
accepted kernel baseline remainsc1aaa0a0; the new36-proof batch remains unelaborated.

The independent parent comparison identified audit PID25610 as the failed child:
90.074690seconds before kill, with compile/resolve/replay already passed and owned
cleanup, reaping and lease release verified. The accepted identical audit source
and target object had completed in55.999180seconds. Failed preflights were slower
too. Four exports match the baseline but collision/PASS completion is absent, so
the failure remains mandatory. Comparison bundle libfile_d81836d0380481918ac2170f0b22286f,
79,596,627bytes, SHA982ad6d5aa70c837c06a6b10c8fdce122c701f822eac071788bf1aaa777d556f
is the parent evidence reference. Its current local materialization failed with
download failed; this checkpoint uses the trusted supplied diagnosis and does
not claim to have locally reverified that ZIP. No user recovery is needed.

The exact bottleneck is unproven. Export or log absence does not locate the
interrupted instruction. In the preserved source, the collision call precedes
TSV construction and writes; this optimization is therefore not presented as
proof of where the90seconds were spent. It is a candidate reduction of explicit
redundant work in a separate serialization path, subject to later measured
qualification. The pinned String.join is itself a left fold over append, so no
quadratic-buffer or automatic speedup claim is made.

The sole runtime source change is in JointAssignmentLawAudit.lean. A pure cache
maps full Lean.Name values to their existing `toString` result. Only inventory
owner/name and recursive-table name/owner/type/body name fields use the cache.
Names remain keyed by their full structural values, never rendered strings, so
display aliases and hash collisions do not merge distinct keys. A fresh empty
cache is local to one run_cmd. List order, duplicates, delimiters, empty lists,
UTF8 bytes, column order and headers are unchanged.

The cache invariant is: every present keyn has value `toString n`. It holds for
empty, lookup preserves it, and miss inserts exactly that pure value. Therefore
each rendered name equals the old result. Iterating an array in its original
order and intercalating the resulting texts with the original comma preserves
the entire list field. Substitution into the unchanged row interpolation gives
byte-for-byte equal TSVs. The proof argument assumes the cache is created empty
and updated only by these helpers, as the production code does; arbitrary forged
cache contents are not an input or a new admission authority.

The imported Environment stays live through the entire run_cmd. Cached keys are
Names from that environment, not the independently read collision-reader parts.
The complete collision namespace, owned lossless byte keys, subsumption rules,
module/part iteration, release order, cleanup and markers are byte-identical.
Root inventory, private helper discovery, recursive type/body/inductive/recursor
links, unsafe/partial/axiom rejection, interfaces, counts and final PASS are
unchanged. Existing proof sources, object inputs, singleton resolver/replay,
resource accounting and all workflow/identity/scheduling controls stay unchanged.
The new pure verification helper declarations are not paper premises and are
outside the target actual-owner module inventory.

The pinned ToString Name instance calls Name.toString, whose implementation walks
components and performs identifier-escape checks; it has no rendering memo table.
The source therefore justifies fewer such evaluations when names repeat. In a clearly
synthetic4096-row differential model,32770reference formatter calls become4104
distinct-full-name calls with identical UTF8 output. This is a structural count,
not a Lean timing or a real audit census. Additional hash lookups/cache storage
may offset some savings; memory and runtime benefit remain unmeasured. Cache
size is bounded by the distinct names actually serialized in this finite audit.
No memory, wall, CPU, output, admission or job bound is relaxed: in particular
the90second child wall and both120minute jobs remain. Timeout remains failure.

test_serialization_models.py blocks native process/lease/resource/sleep actions.
Its differential tests cover empty fields, all supplied constant kinds, full-key
hash/display aliases, Unicode/numeric/private/empty names, repeated ordered lists,
cycles, unsafe/partial/disallowed axioms, missing dependencies and100seeded finite
graphs. The formatter is an arbitrary pure oracle; these tests do not pretend to
implement Lean.Name.toString or Lean Expr traversal. The check_source.py exact
inverse replacement recovers the entire original audit, proving all nonrendering
code stayed byte-identical. Existing engine path sets and all specification
semantics are preserved; only the audit hash and necessary binding cascade change.

staged/SerializationEquivalenceFixtures.lean contains an exact copy of the actual
new helpers and compares them to the original Lean formatter on full Name values.
It imports only Lean and is unelaborated, not a native test result. It is not
wired into CI or given a new execution route. After source review, a future
qualifying bounded validation must first check this fixture's compilation and
byte equivalence, then measure the actual complete decoder audit with identical
coverage under existing controls. Any fixture adapter/workflow change requires
its own exact review; this checkpoint authorizes no execution. Performance and
successful90second completion cannot be inferred from source/model acceptance.

Use this checkpoint's refresh_bindings.py and check_source.py for its finite
delta. The previous scheduling checker remains unchanged historical evidence
for515a39d1; it intentionally does not authorize this added source delta.
All36 mathematical proofs, shared-stream refinement, joint state/cost composition,
arithmetic bit costs, bank/caller handoff, aggregate costs and the whole paper
remain open. Next is independent source/equivalence/binding review before any
compiler, push or rerun.

Primary API references used for source inspection, pinned to Lean4.34.0:

- https://github.com/leanprover/lean4/blob/v4.34.0/src/Std/Data/HashMap/Basic.lean
- https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/String/Defs.lean
- https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Data/Name.lean
- https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Data/ToString/Name.lean
