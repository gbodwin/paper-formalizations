# Exact Bash argument hash correction: source only

Parent307414c84ebdbe7395f0c08d3f27ecf0d66ec7c5 and run39831708126 attempt1
remain preserved. Canonical audit step42 and bootstrap admission step43 passed.
Global replay step44 then failed with ValueError('Unreviewed replay-loop body')
in replay_preflight.before_lake -> command(argv), before Lake/checker invocation.
Focused was skipped; aggregate failed. No567-checker success or36-body
qualification follows. Complete canonical/runtime evidence still requires
independent receipt review; a green gate is not an overall acceptance claim.

Official full artifact12454386216 is168157486bytes with official SHA256
8b2c0175204466a383f3ec70cf0d42054b7c96cc04012ff1ba3f94583347376e.
The decoded full log SHA256 is
7b7f40d6624819a49ad3f641dc1436680527657a02b9f812ae4cd4ac0e4984bd.
The official archive/admission files were not locally materialized again;
their byte-level cleanup/ownership review remains independent. The observed
error path precedes any Lake/checker exec; finally cancels the admission timer
and restores its signal handler. Full-job cleanup completed in the job log.
The serialized physical window was released after all jobs were terminal and
queues were empty. No retry or new physical reservation occurred in this unit.

## Deterministic byte mismatch

scripts/KernelCheck.sh is unchanged, SHA256
b7dac23e6300e3c34d6192887f52d6f780b2bef9720f43b94d4c0f1b3116d77d.
Its single-quoted -c argument starts with a literal LF after the opening quote.
The complete981-byte argument, including leading and trailing LF, hashes to
1fa6ae14282686d2b21fab4e3cdf011b6124c8daed587b2d23a5f42b1e9c5e62.
The former53717997a6a67054021e6b82a61113676e62b2f2ed134868ffd622eb86874bbb
pin hashes the980-byte body after removing only the leading LF. The former
static extraction split after that LF, accidentally excluding an actual shell
argument byte. Bash single quotes preserve that LF: no shell expansion or
normalization occurs inside the argument. This diagnosis uses literal source
bytes plus the actual failure stack, not a new shell/admission execution.

## Minimal correction and preserved guards

Only LOOP_SHA changes in the production admission helper. command(argv) still
compares SHA256 of the exact raw argv string; it does not strip or normalize
untrusted input. The scheduling exact-controls parser now extracts after the
opening quote, retaining the LF, and pins that same complete argument. Its
mutual LOOP_SHA literal and full helper source hash are refreshed. The script,
workflow bytes, privileged outer/inner Bash launch, all567 fresh sequential
checker commands, one Lake setup, before-first-checker verification, source/
CI identity, environment equivalence, no-writer, timer cancellation/placement,
security/lifecycle/resource guards and proof checks are unchanged.

The five existing engine input sets retain exactly the same row/path scope;
only required acyclic hashes refresh. All non-engine contracts, sources,
ordinary/dependency/external roots and all1034 regular plus seven nested
object-admission bindings remain exact. Jobs stay120/120/5minutes and existing
90-second whole-child/admission timers and all CPU/AS/RSS/headroom/file/
allocator/thread limits remain unchanged. No audit work is moved outside a
guard, no log/check is dropped, and partial results do not qualify acceptance.

check_source.py is a static literal/source/hash regression only. It does not
import or execute the production admission helper/policy, run a shell, Lake,
Lean/checker, acquire a compiler lease or change resource limits. It independently
extracts the unchanged quoted bytes, checks the positive literal and exact old
counterexample, rejects finite raw-byte variants under strict hash equality,
and checks the exact minimal source transforms and existing binding rows.
Historical validators with the old extraction remain preserved as historical
evidence; they are not retroactively rewritten or claimed as current authority.

This corrected source must receive coordinator sequential independent review
before publication or any recoverable CI retry. The canonical/cache repair is
preserved unchanged; its isolated runtime benefit remains unmeasured. The36
mathematical bodies and whole paper remain unqualified. Fast stays off. No
compiler/native/physical attempt, push, CI or retry occurred during preparation.
