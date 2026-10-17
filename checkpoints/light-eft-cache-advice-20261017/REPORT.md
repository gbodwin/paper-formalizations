# One bounded advisory pass and hash-then-advise candidate

No Lean/checker/extractor or new import attempt ran. This additive packet preserves production `78cb40c7837db049d645d73696f2e0b724ce8a3b`, the consumed pilot directories, old runner, clean gate and every prior input/evidence file. [The causal-wording correction](CORRECTION.md) explicitly distinguishes the prior cache-growth inference from a measured fact.

## Single authorized pass

`relieve_once.py` was invoked once. UUID `15228551a17040b897871cdd5f7ac383`; UTC **2026-10-17 13:41:23.134138–13:41:28.202953**. It held the same universal lock, device **33**, inode **3849**, acquired nonblocking, with compilers/checkers/extractors idle. The pass directory rejects reuse.

Selection was fixed before advice: at most **512 files / 1 GiB**, choosing descending-size Mathlib primary objects **outside the frozen 3,808-module project dependency map**. It selected 512 objects totaling **428,221,640 bytes**. No expansion followed. The hash-pinned prior 66,976-input inventory supplied exact identities and hashes. Each selected file was opened read-only/no-follow, checked regular, hashed and compared through that same descriptor, then advised using `POSIX_FADV_DONTNEED` with offset/length 0 (whole file); metadata identity was rechecked through the descriptor afterward. All 512 calls returned successfully and their per-file records are retained. No error or OOM delta occurred.

Executables, all shared libraries, project outputs, evidence and final deliverables were excluded. This used ordinary per-file advisory cache release, not deletion, truncation, forced sync, global drop_caches, extraction or a memory-limit change. Successful calls do not prove reclamation.

## Observed before/after accounting

Complete raw and parsed parent/child `memory.stat`, current/max, OOM events, MemAvailable and per-process RSS are in [before.json](evidence/one-advisory-pass/before.json) and [after.json](evidence/one-advisory-pass/after.json). Snapshots are sequential observations, not atomic reservations. The visible parent limit stayed **17,179,869,184 bytes**; the child limit stayed `max`.

| Parent observation (bytes) | Before | After |
| --- | ---: | ---: |
| memory.current | 17,161,916,416 | 16,736,657,408 |
| Headroom | 17,952,768 | 443,211,776 |
| file | 16,053,477,376 | 15,629,545,472 |
| anon | 126,828,544 | 126,869,504 |
| shmem | 2,318,336 | 2,318,336 |
| file_dirty | 307,200 | 573,440 |
| file_writeback | 0 | 0 |
| inactive_file | 610,172,928 | 610,447,360 |
| active_file | 15,440,969,728 | 15,016,771,584 |
| slab_reclaimable | 974,635,744 | 973,254,680 |
| System MemAvailable | 17,851,097,088 | 17,798,955,008 |

Child memory.current was **17,160,380,416 → 16,735,121,408**; all requested child stat fields are retained in the raw evidence. Parent OOM counters stayed `(1,1,0)` and child counters `(0,1,0)` for oom/oom_kill/oom_group_kill. Observed parent current dropped **425,259,008 bytes** and file dropped **423,931,904 bytes**, consistent with relief during the pass but not an isolated per-call causal measurement. Remaining observed headroom is about **422.68 MiB**, still below the unchanged **2 GiB** admission threshold (and below the 512 MiB running stop floor). No admission or import was retried.

## Narrow hashing change for review

The candidate is an additive copy of the reviewed runner, with [an exact diff](evidence/runner-exact.diff). `pilot_child.py` and `pilot_accounting.py` are byte-identical copies. The original runner and manifests are untouched.

`pilot_cache_advice.py` centralizes streaming hashing. It validates a regular file's descriptor identity before/after hashing and compares the full row against the hash-pinned prior inventory before preflight advice. Eligible paths are dependency-package source `.lean` files or objects in the exact package `.lake/build/lib/lean` tree with `.olean`, `.olean.private`, `.olean.server`, `.ilean` or `.ir` suffixes. Executable mode bits and all library/other suffixes suppress advice. Toolchain executables/libraries and project/evidence/deliverable paths are outside the advice allowlist.

Immediately after hashing each eligible unchanged input, the candidate advises through the same descriptor and rechecks metadata. Preflight uses the preserved inventoried row; post-run verification uses the matching pre-run row. Before/after advice logs record path, identity, length/hash, syscall parameters, exclusions/errors and unknown reclaimed bytes. No file is reread merely to claim successful reclamation. Advice errors propagate and are retained. Input comparison, dependency pin/inventory checks, lock ownership and complete lifecycle cleanup remain intact.

**Unchanged:** admission 2 GiB, running stop floor 512 MiB, internal Lean `-M512`, RLIMIT_AS 1.5 GiB, CPU60s, FSIZE16MiB, CORE0, 90-second wall deadline, 250ms monitoring, exact command/environment, direct wait4 ownership, no automatic retry or cap increase. The candidate retains the already-consumed fixed pilot paths, so this packet does not activate another attempt. Any later attempt needs separate review/authorization and explicit new unique paths. The existing descendant-observation and hidden-ancestor limitations remain.

## Tests, preservation and handoff

**11 focused harmless-file/static tests pass**: actual advice preserves file bytes/identity; same descriptor is read-only; wrong hash or replaced identity refuses before advice; symlink refuses; uninventoried eligible input refuses; executable/shared-library and project/evidence exclusions; syscall error logging; dependency-source handling; exact unchanged caps/launcher/accounting plus both hash-phase integrations. The earlier nine-test log and final eleven-test log are both preserved. No child process or Lean was used for these tests.

All old tracked files remain unchanged. The same universal lock is free and compilers/checkers/extractors are idle. Publish implementation, exact diff, measurements, per-file advice records and test evidence with CI skipped, then stop for independent review. This is cache-relief evidence and an unexecuted runner candidate, not an import, proof-validation, clean-build, authentication or whole-paper result.
