# Audit phase instrumentation — source review only

Parent independent receipt review establishes that run39549447443 attempt1
failed in decoder audit PID24486 at90.063123seconds, with4.262444seconds preexec,
861samples, peakRSS4,817,195,008bytes and minimum headroom14,386,495,488bytes.
Owned cleanup and lease release passed. Compile and replay passed. The exact
native serialization fixture and singleton resolver passed together in9.380646
seconds with bound ordered markers. Optimized audit source was confirmed; the
parent reports four exports matching baseline and only allocator startup in
the raw audit log. This uses the trusted parent diagnosis, not a fresh local
verification of its60,818,767byte Library bundlelibfile_fa80a5271b2c8191afa63e876b51f27f,
SHA25611ce767c1152ca3df260a6643d73203afab015c06375f7f39be134de954d8943.
Both old/new attempts are timeout-censored; performance improvement is unknown.
Prior failures, source, native artifact references and local evidence are preserved.

This candidate adds only diagnostic stdout timing to the audit source. Removing
the exact insertions restores every byte of reviewed7a7993f5. The entire collision
namespace, owned key/region cleanup, pure cache namespace, all traversal/checks,
four export write arguments and final PASS remain unchanged. No optimization,
proof repair, new import, new output file, runtime-adapter change or compiler
route is added. Imported module data, target owner roots and proof dependencies
are unchanged; the timing helper belongs to this audit file, not the target.
All16 timing calls are outside hot loops. No loaded module/declaration names,
paths, expressions, input payloads or environment variables are printed.

The16 fixed phases, in source order, are frontend-ready, timing-helper-ready,
scan-helper-ready, serialization-helper-ready, audit-run-start,
environment-ready, scan-complete, roots-complete, inventory-complete,
recursive-complete, interfaces-complete, inventory-written, dependencies-written,
imports-written, findings-written and strict-checks-complete. Every marker is
flushed immediately. The clocks are IO.monoMsNow reduced modulo2^64, explicitly
reported as mono-ms-mod64. Thus each decimal clock has at most20digits, and all new
marker lines together have a fixed bound below2048bytes. No per-row/module/read
clock calls or counters are added. Existing collision output remains intact.
The scan-* labels avoid the existing collision parser's reserved collision-/COLLISION
tokens. Differential tests use that unchanged real parser and retain its strict
malformed/incomplete collision-log rejections.

The first marker follows imports and includes compilation/elaboration of its
small first run_cmd. No marker therefore localizes only to startup/imports/that
first command; it cannot separate those causes. Markers around the collision
and cache namespaces locate helper command processing. The gap from
serialization-helper-ready to audit-run-start includes elaboration/compilation
of the large main run_cmd. Later gaps cover environment setup, complete collision
scan, root discovery/checks, root inventory/serialization, recursive traversal
with serialization, interface checks and individual exports. Existing collision
markers provide the finer module coverage if that phase is reached. This
minimal first pass intentionally does not separate traversal from per-row
serialization, nor instrument inside region readers or hot loops.

Clock deltas include scheduling, GC, IO/flush overhead and frontend processing;
they do not attribute CPU time or prove a bottleneck. A marker means its command
position was reached, not that every preceding Lean command succeeded: the
frontend can continue after errors. The offline phase_report.py accepts only
ordered fixed-label prefixes, flags malformed/truncated/duplicate/out-of-order
markers, and declines elapsed-time claims if modulo2^64 clocks decrease (possible
wrap or inconsistent data). Empty/partial/complete timing sequences always
report audit_acceptance_established=false. Even strict-checks-complete cannot
replace the original PASS, exit0, complete audits/exports, resource/lifecycle
receipts, same-run authority, full/focused jobs or exact-commit aggregation.
The report is not wired into any production acceptance path.

Instrumentation adds small but unmeasured frontend/clock/stdout/flush costs.
IO errors remain failures; no exception is swallowed. All90second child bounds,
CPU/memory/output/admission/ownership checks, two120minute job limits, fixture
prerequisite and repository single-compiler coordination remain unchanged. The
four-spec audit/source/hash cascade is the sole production metadata change;
all engine membership sets, dependency sources, workflows and resource fields
are identical. The paid spec is unchanged. refresh_bindings.py uses the existing
acyclic refresh only; instrument.py/check_source.py are offline finite tools.

test_phase_models.py blocks native process, lease, resource and sleep APIs. It
tests all17 valid prefixes, zero-clock/equal-clock observations, wrap/decrease,
malformed/unknown/reordered/duplicate/truncated markers, bounded output, exact
source inversion and no hot-loop/collision/cache instrumentation. These are
models, not native Lean validation. The new instrumented audit remains
unelaborated. Fast is off. No compiler, admission, push, CI or retry was started.
Independent source/implementation review is next, before any execution.

The accepted kernel baseline remainsc1aaa0a0. The36-proof focused batch remains
unverified; whole paper, shared-stream/state-cost refinement, arithmetic bit
costs, bank/caller handoff and aggregate costs remain open.

Pinned API source: Leanv4.34.0 src/Init/System/IO.lean, whose monoMsNow is an
opaque BaseIO Nat monotonic-millisecond reading unrelated to wall-clock time:
https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/System/IO.lean
