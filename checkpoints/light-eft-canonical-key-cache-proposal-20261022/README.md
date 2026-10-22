# Canonical audit: source-only owned-key reuse proposal

This is an additive review checkpoint against exact
8cdc62e577e29561e441538e96e426aa31f3b7c0. Production audit, workflow, five
specifications, engines, proof sources and all existing evidence remain intact.
PROPOSED.patch changes only the canonical audit's collision helper. It is not
applied. No Lean/compiler/kernel/audit/model/native test, admission, publication,
CI attempt, reservation or physical retry was performed. Fast remains off.

## Failure facts and access qualification

Coordinator independently verified run39809387613 attempt1's official archive
12443982278:154272684bytes, SHA256
e224e771a662f933b819945795a9d6a5e54d1ea38ce6c800822e780126711bf0.
Audit child342f9e721db346acba201ea561476c64 ran CanonicalOutputAudit.lean.
Three admission replays and canonical compile, resolve and replay exited0.
The whole-child90-second timer began4430518993496ns; preexec verification was
4.813775433seconds later; kill started90.027314525seconds later; exit was-9.
Finalization134.979320953seconds after start includes approximately45seconds
postkill cleanup, not extra runtime allowance. Direct reaping, descendant
cleanup/ECHILD and both lease releases passed. Peak sampled RSS4890279936bytes
was below6GiB, AS12GiB, audit CPU90seconds; last headroom14578475008bytes,
cgroup OOM events0. This is a child deadline, not evidence of memory exhaustion.

The1881-byte raw log has mimalloc startup only. Partial exports have52592
dependency rows,6523 imported names, one actual-owner declaration and empty
violations. Neither partial exports nor absent captured markers imply success
or locate the remaining in-memory phase. The hotspot, transience, speed benefit
and timeout fit are unmeasured. The new replay admission/global567-replay loop
and focused36 bodies were not reached.

Those are coordinator-supplied verified observations, not a claim that this
author reassembled the runtime exports. Compact diagnosis Library
libfile_ebd3c17998c8819185b9c4a829de7b38 is8034396bytes, archive SHA256
2529acb824efeb90db0cd5847758f0b3b17945c14482a68a086e1f8f5b176882;
34-payload manifest SHA256
b5bd3e98ab149d4aabca6bf5654ed848d26e0efb95f0acc6004a324b689ed735.
Preparation succeeded here, but one supported compact download failed.
Two workspace-placement preparations returned no workspace path; no second
download or large-archive transfer was attempted. Library read found no readable
ZIP content. Consequently REPAIR-BRIEF.md was not read locally. This missing
brief must be reconciled by the coordinator before accepting this proposal.
No user recovery action is requested.

## Exact candidate and static equivalence argument

The proposed collision namespace is byte-identical to the existing frozen
BridgeAudit.lean namespace at the base commit. The canonical code after the
namespace is byte-identical to the original audit. BINDINGS.json pins the full
source, patch, namespace, unchanged tail, reference helper, fixture and resolver.
This source equality is not a new native qualification or performance result.

The only algorithm change is a per-module map from full Lean Names to fresh
lossless encoded bytes, seeded exclusively from the still-live environment's
effective declaration names before any new part is read. It is not an audit
result cache. Every raw part, name claim, effective declaration and compatibility
decision is still inspected on each audit execution.

Invariant: every cache entry(n,k) has k=ownedKey(n). Empty maps satisfy it;
rememberKey either preserves an existing entry or inserts exactly ownedKey(n).
Lean's full structural Name equality distinguishes anonymous/string/numeric
components and uses their full data, not printed names or hashes as identity.
Hash collisions still undergo that equality. Therefore keyFor returns the same
bytes on a hit or miss as the former ownedKey call. Byte-array pointer identity
is not used by the scanner.

Induct over the unchanged ordered loops of raw constNames/extraConstNames and
effective constants. Their keys, branch decisions, representative locations,
counts, compatible-update/retain direction, issues, marker text and order are
unchanged. The remaining lookupDeclaration still uses the original encoder.
Missing module, malformed shape/name, unclassified and incompatible cases are
not filtered or normalized. File reads, error capture, reverse release and
read/freed equality checks are unchanged. Exceptions and rejection predicates
remain fail closed; this is not equivalence of physical OOM/deadline outcomes.

The cache stores only environment-owned Name keys and independently allocated
bytes. Raw-reader Names are transient lookup arguments, never inserted. Cache
state does not enter persistent State. Raw readers return before their data is
cleared and newly read regions freed; private/server/main release remains in
reverse dependency order. The original environment remains alive and none of
its regions are freed by the scanner. A seeding failure occurs before any new
owned part is allocated. New allocation/lookup overhead remains a qualification
risk rather than an excuse to raise any resource limit.

Let D be the effective-name sequence, E its distinct Names, and R the raw-name
occurrences. At the substituted sites the old scanner calls the encoder
|D|+|R| times. The proposed scanner calls it |E|+raw_misses times on a successful
module scan. This avoids |D|-|E|+raw_hits encoder calls, but adds cache allocation
and lookup costs. No elapsed-time, total-allocation or peak-memory improvement
is asserted. In failure prefixes, early seeding may perform additional work.

## Preserved audit and execution contract

The entire recursive audit tail remains exact: actual-owner enumeration and
the required theorem root, every declaration type, definition/theorem/opaque
body, inductive/all/constructor/recursor links, unsafe/partial checks, exact
three allowed axioms, six required reachable interfaces, complete import
inventory, four export bytes/order and final strict rejection/PASS logic.
All raw-parts collision coverage/classification and output buffering are exact.
No log, check, export or failure is dropped. Nothing is moved outside supervision.

The whole-child90-second timer including launcher/handshake, audit CPU90seconds,
AS12GiB, audit FSIZE64MiB, other FSIZE16MiB, memory/headroom accounting, leases,
no-writer and lifecycle gates remain untouched. Full/focused/aggregate job
limits stay120/120/5minutes; all567 fresh sequential checker processes and every
existing proof/verification gate remain required. No historical/cached audit
receipt or partial export may qualify this proposal. Whole paper remains open.

## Review boundary

PROPOSED-CanonicalKeyEquivalenceFixtures.lean copies the existing bridge fixture
with only a canonical final marker. The composite resolver prepends that exact
fixture to the unchanged canonical singleton resolver. Both are unexecuted and
unwired proposals. FUTURE-INTEGRATION.md specifies the mandatory prerequisite;
the current production specifications intentionally still bind the old audit.
This checkpoint is not executable production authority. The existing independent
reviewer/coordinator must review the exact proposal sequentially, reconcile the
missing repair brief and approve any finite integration before publication or
physical qualification. The author does not act as independent reviewer.
