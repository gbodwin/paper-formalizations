# Bounded Light EFT recovery proposal — no compiler executed

Greg authorized retry/diagnosis in his existing personal workspace. This proposal reconsiders our conservative admission policy; it does not edit that policy or approve execution. Production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`; prior preparation/evidence remain unchanged. No support contact, security setting change, namespace switch, cache eviction, extraction, compiler/checker, installation or CI action occurred.

## Current measured capacity

The existing environment connected successfully. No live Lean/Lake/checker/extractor was observed; the universal lock was free. The exact snapshot is `evidence/current-capacity.json`:

- Visible parent `memory.max`: **17,179,869,184 bytes (16 GiB)**.
- Parent `memory.current`: **14,920,544,256 bytes**; headroom **2,259,324,928 bytes (2.104 GiB)**.
- Free workspace disk: **12,577,579,008 bytes (11.714 GiB)**; no swap.
- Visible child limit: `max`. Membership is still `0::/` in a noninitial namespace; the `/..` mount does not expose all ancestors. Their limits remain **unknown**, not unlimited.
- An initial nearby snapshot charged 13,895,176,192 bytes to files, 49,070,080 to anonymous memory and 969,498,624 to kernel memory (including 962,891,928 reclaimable slab). Thus much charge is cache, not active compiler heap. Reclaimability is not reserved capacity or permission to drop caches.
- `memory.events` reports historical `oom=1`, `oom_kill=1`; it is not a new event caused by this diagnosis. Memory pressure-file read returned ENOENT and is recorded, not interpreted as zero pressure.

## What is policy, and what is essential

`LightEFTExactSupervisor.py` hard-codes 4 GiB admission, and `LightEFTCgroup.py` refuses noninitial namespaces lacking a proven full ancestor chain. These are **self-imposed conservative execution-admission checks**, not Lean soundness requirements or kernel guarantees that every check needs 4 GiB. Full ancestry is indispensable to the claim “we know the effective cgroup budget,” but not logically indispensable to running a bounded process while expressly accepting unknown outer limits. Conversely, lowering a threshold does not establish safety or make unseen ancestors disappear.

Keep the accepted clean gate unchanged. A distinct reviewed bounded-pilot supervisor could retain the universal lock, source-bound receipts, process identity, serial execution, child reaping and all proof/kernel checks, while labeling accounting `PARTIAL_VISIBLE_ANCESTORS` and using per-process limits. This is a proposed risk-bounded experiment, not a transparent bypass of the reviewed gate. No such supervisor has been implemented or tested here.

## Local dependencies: fresh download is not intrinsically necessary

Read-only reconciliation found:

- All **nine** dependency HEADs match the manifest and tracked trees are clean.
- All **3,808** mapped dependency source hashes match; **19,040** corresponding allowed-suffix object files totaling **3,063,490,480 bytes** are present, with no missing primary `.olean`.
- All **3,808** retained `.ltar` archives, totaling **238,316,640 bytes**, still match the previously preserved length/SHA256 inventory. No extraction was performed.
- All **486** accepted project source/object bindings still match the incremental evidence; their primary objects total **106,140,936 bytes**.
- The preserved setup log `/tmp/lean-environment-verification/cache-get.log` explicitly reports the official `https://cache.mathlib.org/mathlib4-master` route, 8,908 downloads and 8,908 decompressions. It is copied/hash-bound as historical evidence. Prior accepted Light EFT receipts use these current dependency directories.

This is meaningful historical official-cache and incremental-use provenance. It is **not** a complete authenticated per-archive byte-to-extracted-object receipt chain: the historical log lacks those individual hashes/HTTP receipts, and current hash agreement cannot create them retroactively. Do not call the local dependency artifact fully authenticated under the stricter clean-artifact specification.

For a reviewed incremental pilot, the existing local dependency installation is a reasonable candidate without a mandatory fresh download: pin its exact files before use and explicitly retain the historical-provenance qualification. The primary leaf `Aesop.Script.Tactic.olean` is 50,040 bytes, current SHA256 `7da491c3c197eb579eb15836b00d43da6400f391efeacca5a2e7f7f9db798402`. This size alone is not a memory-usage prediction. Freshness is not itself trust; independent reviewers must decide whether this provenance basis suffices for each claimed validation level. A fresh project build may reuse accepted dependencies but must still rebuild every project object and must not silently inherit prior project outputs.

## Authorized same-route retry

One normal request at **2026-10-17T13:13:02.048981+00:00** to `https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar` again returned **403 Forbidden**, exact body `error code: 1010\n` (17 bytes), SHA256 `2938e9f1284180959e33ab1718d0793a72ff6e4cdb8108c34dcd14e69446de5c`. Same default identity/proxy/TLS route, no redirect, alternate endpoint or retry loop. Headers and raw body are preserved. Peer capture has the same recorded object-interface limitation. The route remains blocked; no successful archive bytes were obtained. No support action is required by this recovery proposal.

## Proposed first pilot for independent sequential review

1. Hash-bind a new minimal input containing only `import Aesop.Script.Tactic`; hash-bind its pinned dependency/source closure and exact official executable. Use explicit dependency-only `LEAN_PATH`/`LEAN_SRC_PATH`, with no inherited project objects. No Lake, Cache.Main or native compilation fallback.
2. Under the existing exclusive lock, require no competing worker and take fresh visible-parent and system readings. Proposed limited admission: at least **2 GiB** visible headroom and system MemAvailable, more than **2 GiB** free disk. Record unknown ancestor limits. This is a new pilot policy requiring review, not a modification already applied.
3. Execute only official Lean, `-j1 -M512 -DautoImplicit=false -DwarningAsError=true <smoke.lean>`, without object output. Pinned `Lean/Shell.lean` confirms `-M512` is a 512 MiB internal memory setting. Do not use `-T` as a wall timeout: it counts allocations.
4. Proposed child limits: **RLIMIT_AS=1,610,612,736 bytes (1.5 GiB)**, **RLIMIT_CPU=60 seconds**, **90-second wall deadline**, **RLIMIT_FSIZE=16 MiB**, core dumps disabled. Only this child receives limits; no global/security/cgroup settings change. Lean's internal cap is supplementary, not a total-RSS guarantee. RLIMIT_AS bounds mappings too and may make startup fail; that is an informative contained failure, not a reason to silently enlarge it.
5. Retain the reviewed supervisor's fail-stop cleanup design: source/harness/argv/input hashes, UUID/PID/start/end/exit receipts, inherited lock, subreaper/process-group containment and complete reaping before unlock. Sample child RSS/virtual size, visible current and memory events every 250 ms. Terminate on visible headroom below **512 MiB**, increase in OOM counters, timeout, unexpected compiler descendants, or lost process/accounting identity. Preserve raw failure/source. A race or unseen ancestor may still OOM-kill processes; these controls cannot promise isolation of the supervisor or complete machine safety.
6. Stop after the one attempt and review measured peak RSS/VM, `wait4` maximum RSS, exit and event deltas. No automatic retries, widening or batches. If it passes with margin, separately review one fresh strict compile of `LightEFTSpanners.FiniteLaw` against only pinned dependencies into a new output directory under the same cap. A checker/resolver run is a later separately bounded sequential step, never aggregate-prefix replay.

The observed headroom exceeds this proposed pilot admission; at the full 1.5 GiB address-space cap it leaves about **619 MiB** visible margin before unbounded external/accounting effects. This is a plausible bounded first experiment, **not proof it will fit**. Large dependency mappings, elaboration or audit closure may exceed the cap. The full 486-build/485-singleton-replay/recursive-audit clean gate cannot currently be promised within capacity; no measured per-target peak set is available. A pilot failure or heavy-module limit is a specific next datum, not evidence the mathematics fails. Unchanged audit coverage and no unsafe/partial/admitted axioms remain required for any later acceptance.

## Review decision and remaining blockers

Recommended next decision: review the isolated capped-pilot design and qualified local dependency provenance, then authorize implementation/testing of that supervisor before the first compiler invocation. No compiler is authorized by this report. Fresh cache access still fails. Full ancestor accounting remains unknown; the proposed pilot acknowledges it instead of treating it as an automatic mathematical blocker. Clean final validation additionally needs its reviewed dependency trust basis and evidence that the actual workload fits; neither is claimed here. Theorem 34/general lower and modeled-runtime boundaries are unchanged. Stop here with no compiler/checker running for independent sequential review.
