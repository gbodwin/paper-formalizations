# Same-project preparation: cgroup visibility, cache mapping and quiet-window CI

Independent review accepted harness `ded293f2e4b17405cd009c5ba65acf913154b139` and evidence `5f37d12f032262d9f26daafe1eb1041175524c0e` as **preparation only**, not execution approval. This additive checkpoint preserves those results, frozen production `78cb40c7837db049d645d73696f2e0b724ce8a3b`, all historical evidence, audit, resolver and package pins. No Lean/checker, native extractor, build, CI, installation, dispatch, replacement environment, remount or namespace switch ran.

## Current cgroup inspection: a specific visibility gap

`inspect_cgroup.py` performs read-only descriptor-based kernel inspection. It opens the visible directories and accounting files with O_NOFOLLOW; records fstatfs, device/inode, fdinfo mount IDs, raw file values, self-membership, and before/after membership/mount data. `evidence/cgroup-observation.json` and `cgroup-assessment.json` retain the observations.

Both `/sys/fs/cgroup` and its `init` child are genuine cgroupfs (`0x63677270`), with accounting descriptors on mount 90/device 24. The complete mount-parent/path check finds no covering overmount of the observed accounting paths. Membership, namespace identity and mountinfo are stable. The observer PID occurs in `init/cgroup.procs`, not the visible parent. `/proc/self/cgroup` reports `0::/`; the mount root is `/..`. These observations identify the visible self group and its parent without changing namespaces.

Crucially, **the visible parent is not the genuine hierarchy root**: it exposes `cgroup.type = domain`, a finite `memory.max`, and resource-domain counters. The root-exempt ENOENT case did not occur. `/..` here reaches the visible parent of the namespace root, not a proven global hierarchy root. There is only one cgroup2 mount in the visible mount table. No complete ancestor chain above that parent is available through the inspected permitted view. We did not try an alternate process root, remount, namespace switch or access workaround.

The visible parent has limit **17,179,869,184 bytes** and observed current **14,662,328,320 bytes**, leaving **2,517,540,864 bytes (~2.34 GiB)**. The child limit is literal `max`. The visible parent's budget already falls below the 4 GiB requirement; unknown ancestors could restrict it further. No missing file or denied read was interpreted as unlimited.

A noninitial namespace is not inherently unusable. This particular view lacks proof of the full ancestor chain. Accordingly no new mapping exception or admission change was made. The precise remaining resource gap is access to a genuine, unmasked hierarchy-root/ancestor accounting view for this same configuration; waiting alone does not supply that evidence. The parent reports only this existing configuration and offline, unauthorized GregAcer. No replacement environment or offline machine was accessed.

## Python-only pinned cache-key reconciliation

`cache_mapping.py` is a **review candidate**, isolated from the execution harness. It translates the pinned cache hash and supported header grammar without importing Lean, loading its runtime, calling FFI hash routines, or running Cache.Main. The source references/hashes are in `evidence/derivation-source-hashes.json`.

The derivation follows actual definitions:

- `Hashable UInt64` is identity; list hashes fold `mixHash` from seed 7.
- String hashes use UTF-8 bytes, MurmurHash64A with seed 11 and 64-bit little-endian arithmetic; file canonicalization replaces CRLF with LF, not lone CR.
- Root generation is 5. The root hash folds generation plus the canonical hashes of mathlib's `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json`. The implementation does **not** separately mix `Lean.githash`, despite its descriptive comment; the toolchain file is one input.
- Module keys fold root hash, relative-path-component hash, content hash, and ordered filtered import keys. Root filtering matches pinned Cache.IO. The parser models nested ordinary comments, line comments, module/prelude, public/meta/all modifiers and header termination at documentation/declarations. Unsupported escaped/non-ASCII identifiers or malformed headers refuse. Every encountered frozen header was within the supported subset.

The resulting root hash is `1d7d1aa06138c6e4`. The 486 frozen project modules lead to **3,808 dependency modules**, with source SHA256, ordered imports, intermediate hashes, key and official master-cache URL recorded for each. All nine dependency HEADs and tracked cleanliness were checked. All **3,808 derived names match existing local `.ltar` filenames**. This is useful corroboration against an independent existing cache, not fresh official-origin or object validation.

`evidence/dependency-map.json` is preserved in full, with 16 ordered reconstruction chunks under `mapping-chunks`. Existing local archives were read and hashed into `candidate-archive-inventory.json` and its own ordered chunks. Those are explicitly labeled unauthenticated candidates for future comparison. No project objects were copied, inherited, loaded or installed; no archive was decompressed.

Hash definition references: [pinned Lean hash.cpp](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/runtime/hash.cpp), [String.hash entry point](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/runtime/object.cpp), and the locally hash-bound pinned mathlib Cache/Hashing.lean, Cache/IO.lean and Lean ParseImportsFast sources. This Python port still requires independent review before use as the gate's artifact provenance basis.

## Genuine official-HTTPS access blocker

The first fresh request was to the derived official master-cache URL:

`https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar`

It returned **HTTP 403 Forbidden** at `2026-10-17T07:15:29.026031+00:00`. The helper used standard CA verification and hostname checking. The raw helper diagnostic and request identity are preserved in `https-samples-attempt-1.log` and `https-sample-receipts.json`. No successful archive bytes were received; the helper did not preserve the HTTP error response body, and no cause beyond the observed 403 is asserted. Retrieval stopped after this first failure. No alternate endpoint, user agent, credential, network setting or access workaround was tried.

The intended trust basis is pinned source-to-key derivation, authenticated official HTTPS origin, exact archive bytes/hashes, and independent reconciliation. **No new signature service or user-supplied artifact is required by this plan.** The official route currently ends at a concrete HTTP 403; its existing access needs resolution before fresh origin/byte reconciliation can proceed. This is not a request for Greg to supply cache files or debug the implementation.

## Extractor and full artifact: prepared, not executed

The existing official distribution is 580,367,391 bytes and freshly hashes to `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`. The installed `leantar` is 2,692,960 bytes with SHA256 `06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3`. Neither it nor an archive decompressor was executed. Independent comparison of the installed extractor member against the verified distribution still precedes any separately reviewed extractor action.

`prepared-extraction-command.json` binds the exact proposed absolute executable/argv, fresh staging cwd, input inventory and stdin SHA256. `prepared-extractor-stdin.json` follows pinned `mkLeanTarConfig`: mathlib-root modules use `{file, base}` redirection into staging mathlib; other dependency archives use the plain path and staging cwd. All 3,808 inputs are named and hash-bound, but their fresh official-origin comparison is blocked, so this command must not run yet.

After independent mapping review, successful official-origin comparisons, extractor-member verification and separate authorization for native extraction, the same-project pipeline can produce a complete dependency-only output inventory and immutable bundle identity. It must record all archive-to-file mappings, toolchain/pins, exact extraction inputs/UUID/PID/times/diagnostics, every output hash, and the final bundle URL/length/SHA256. Pinned `mkBuildPaths` includes trace/hash/C/IR metadata and optional `.ir.sig` in addition to Lean objects; the final packaging/install contract must reconcile these explicitly rather than silently add a native build fallback. The existing consumer remains blocked with `UNAVAILABLE_REVIEW_REQUIRED`; no full output inventory or usable bundle is claimed.

## Exact workflow guard and bounded quiet window

The prepared `.github/workflows/light-eft-exact.yml` now guards exactly:

- production `78cb40c7837db049d645d73696f2e0b724ce8a3b`;
- reviewed **preparation** harness `ded293f2e4b17405cd009c5ba65acf913154b139`.

It is still dispatch-only and is not installed on main. This exact guard is not execution approval. A later artifact-bearing, execution-reviewed harness would require a separately reviewed explicit guard update; no symbolic/latest ref is accepted.

The retained 117 workflow definitions were checked: all events are push, pull_request or workflow_dispatch; there are no autonomous schedules. The 153 potentially ungrouped branch tips are dormant trigger routes, **not 153 active workers**. Fresh reads of in_progress, queued, waiting, pending and requested each returned zero runs. No actual uncoordinated producer was observed. Shared concurrency still cannot exclude an ungrouped producer if one is actually initiated.

The next CI plan is therefore a bounded **known-initiator quiet window**, coordinated by the parent registry:

1. Finish independent code/artifact/resource review. Preserve the exact source and eventual reviewed harness SHAs.
2. Parent, ordinary worker and reviewer agree a bounded window with no overlapping push/PR/dispatch/rerun activity. Offline unauthorized GregAcer remains offline; no replacement environment is introduced. Do not infer an active producer merely from a dormant ref.
3. If subsequently authorized, install only the reviewed exact workflow plus minimal shared-group addition on the fresh default-branch tip, with CI skipped. Never merge this checkpoint branch wholesale or rewrite dormant branches.
4. Before dispatch, stop ordinary compiler/checker activity, confirm the common lock/process state, perform a fresh all-active-status queue check, and record ownership of the single compiler slot by CI. Use only the normal authorized dispatch route; no permission expansion or API bypass.
5. Parent monitors active/queued runs throughout the window while this ordinary worker remains compiler-idle. No push, PR, dispatch or rerun may cause overlap. If an actual unexpected producer appears, identify its concrete run/ref/actor and coordinate stopping our gate rather than silently disabling unrelated workflows. Resume ordinary compilation only after CI ends and the slot is explicitly returned.

The zero-run snapshot is not a permanent reservation. The quiet window needs coordination when execution is actually authorized; no rewriting of 153 dormant refs or broad workflow disabling is proposed. No installation, dispatch, rerun or cancellation occurred here.

## Preparation validation and scope

Ten Python-only tests pass, covering header parsing/refusal, newline canonicalization, a known existing cache-key vector, all mapped source hashes and existing archive names, the exact workflow guard, and the absence of autonomous events in all 117 retained definitions. These are not Lean/compiler/checker tests or fresh cache-origin acceptance. All raw attempts, including HTTP 403, remain preserved.

The accepted exhaustive audit, resolver, production proofs, pins and history are unchanged. Theorem 34's general lower claim, modeled-runtime limits and site issues remain open; no website changed and no whole-paper completion is claimed. Publish additively with CI skipped, then stop for independent review.
