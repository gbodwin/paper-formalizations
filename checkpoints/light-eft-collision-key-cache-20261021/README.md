# Per-module lossless collision-key reuse: source review checkpoint

Parent is c46b0a6b66a67b86d5de7a16f3bf38983571d2a5. This checkpoint is
source-only: Fast off, no compiler, push, CI, admission workaround or retry.
The accepted kernel baseline remains c1aaa0a00c0c943cec4b2753a937023e9884db04.
The 36 new mathematical bodies were not reached by run39559929401 and remain
unverified. Existing source, failures and evidence are preserved in Git/Library.

The parent's independent diagnosis of that run is retained by reference:
libfile_39b0e069d5f08191aa8eeea647930bb5, 46,666,541 bytes, SHA256
88ba7dd40f46daa40893a303405c2348319a84dfd11c0c9c909a82a7eef20330.
The full audit succeeded in54.322s; focused reached all16 phases and the same
four exports but died at90.025s,2.610s after strict-checks-complete. Scan time
was43.925s full and76.064s focused. Both native fixtures and owned cleanup
passed in that diagnosis. These are parent-verified facts, not newly inspected
raw receipts here. Neither run measures this checkpoint's runtime benefit.

## Finite change and equivalence argument

For one module let E be its effective ConstantInfo names and R the raw constNames
and extraConstNames in the same original read order. Before opening new parts,
seed a temporary HashMap Name ByteArray with each distinct name in E, computing
its unchanged ownedKey once. Map keys come exclusively from the still-live
imported environment. Raw-reader names are lookup arguments only. A hit returns
the previously independently allocated bytes; a miss runs the exact original
encoder. The effective declaration loop uses the same helper. No cache is added
to State or returned by scanOne; no raw-reader Name/String/Expr can enter it.
The cache can survive region release safely because its Name keys refer to the
pre-existing environment, whose regions remain live and are never freed here.

Invariant: every cache entry (n,k) satisfies k=ownedKey(n). It holds for the empty
map; rememberKey preserves an existing entry or inserts that exact encoding.
Full structural Name equality governs lookup, not display text. Thus keyFor(n)
is byte-for-byte ownedKey(n), on hits and misses, including arbitrarily large
numeric components, Unicode, private and otherwise unusual names. Substitution
at the two raw-claim sites and the effective-declaration site preserves every
map lookup/update, count, classification, issue and output line, in the same
order. The original full scan loops, malformed-shape/name checks, compatibility
predicate, effective lookups and replacement direction are unchanged. This is a
source argument, not a kernel-checked theorem or performance result.

Ignoring the unchanged compatibility lookup encoder calls, the original performs
|R|+|E| encodings. The replacement performs |unique(E)| plus the number of raw
names absent from E. Every effective lookup is a hit. The difference is
|E|-|unique(E)| plus the number of raw occurrences present in E, nonnegative.
This proves a reduction in encoder calls in the model, not total time, allocated
bytes, peak memory or fit within90s. The added temporary Name map and lookups
have overhead. If the effective module is absent, seeding is skipped; raw misses
and the existing module-count unclassified path remain intact. Seeding happens
before acquiring any reader-owned region, so an allocation failure there cannot
leave a newly read region to release. All existing failures remain failures.

## Buffered completion investigation

Preserved pinned v4.34.0 primary sources show Stream.ofBuffer.putStr writes via
copySlice with exact=false; write explicitly documents avoiding quadratic
repeated writes. flush is a no-op. withIsolatedStreams converts the collected
UTF8 buffer after command return; Language.Lean.process/doElab then attaches it
as an informational message. Final logInfo, local cleanup/destruction, output
conversion and later frontend work remain candidate contributors to the
unresolved command-completion interval; no measurement isolates one here.
No output/flush/channel/command-boundary change is justified by these sources.
They are all preserved byte-for-byte, including collision stdout, diagnostic
stderr,16 markers, four exports and final PASS. This patch targets redundant
encoding in the measured dominant scan phase only. No claim that completion
has been repaired, that a timeout was benign, or that new timing is known.

Primary references (exact preserved source bytes/excerpts are in the review
packet): leanprover/lean4 v4.34.0 src/Init/System/IO.lean lines1710-1730,1799-1809
and src/Lean/Language/Lean.lean lines766-787. The original source response record
is preserved alongside its SHA256 binding, not re-fetched as mutable main.

## Validation and next executable step

repair.py deterministically reconstructs the four finite non-spec modifications
from c46. check_source.py requires exact reconstruction, exact four-spec hash
cascade, all1008 production bindings, unchanged engine/dependency path sets and
every other resource/policy field. Historical checkpoint check scripts remain
historical baseline checks; this checkpoint's exact source check supersedes
their earlier byte-identical-collision-helper condition for this candidate only.

Eight new Python models check byte equivalence, exhaustive short seed/raw sets,
the encoder-call formula, structural distinctions, Unicode/deep/large-Nat names,
environment-vs-reader key provenance, per-module cache scope, raw fallback and
complete report/order/count/rejection differential behavior. These are models.
Eleven existing process-blocked prerequisite models and sixteen existing
classifier/coverage-parser models also pass. They establish no native runtime.

The native resolver fixture now includes the exact production encoder and cache
helper bytes and checks empty/full/partial/repeated caches, hits/misses, distinct
numeric/string components and the encoding invariant over deep/unusual names.
It runs before the unchanged text fixture and unchanged singleton resolver in
the existing bounded resolve child. The existing final fixture marker, exit0,
completed-log binding, resolution checks and replay/audit prerequisites remain
mandatory. The composite is exactly the updated fixture plus the original
resolver. The fixed source hash, submitted-source snapshots and receipt checks
prevent omission of new cases while reusing the old marker. A prior fixture
success cannot qualify these changed bytes. These added Lean bodies are
unelaborated; they require actual future bounded execution after review.

No workflow, stage order, compiler route, new child, output path, namespace
authority, whole-process deadline, resource guard, allocator/thread/replay-stack
setting or120-minute job budget changes. The same-job fresh producer context,
full-before-focused order and mandatory exact-commit aggregation remain intact.
No other audit clone or paper theorem changes. No object reuse across jobs.

After sequential independent review, the next executable step would be one
separately authorized exact-commit qualification using the existing schedule.
This checkpoint launches nothing. Full and fresh focused jobs and aggregation
must succeed, with complete receipts, collision coverage, native fixture,
kernel/audit evidence and all36 bodies independently reviewed before acceptance.
Timeout remains failure; no unchanged automatic retry. Shared-stream refinement,
joint state/cost composition, arithmetic bit costs, bank/caller handoff,
aggregate costs and whole-paper acceptance remain open.
