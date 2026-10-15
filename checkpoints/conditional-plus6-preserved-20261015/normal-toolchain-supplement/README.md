# Independent-review evidence supplement

Evidence only. Candidate remains UNVERIFIED and unaccepted. Tested source remains `d0f9ee2364bf4a5aaa7e0ca4da48216e42bbc63e`; original validation evidence is preserved unchanged in commit `b3d23474c0f2b00ff6e26b8e0101702a785927de` and [the adjacent evidence directory](../normal-toolchain-evidence/README.md).

## Dependency audit: readable chunks and reconciliation

[Browse all 49 chunks](dependency-chunk-index.md). Each contains at most 400 original lines; maximum size is 375,249 bytes. The original 8,364,100-byte file remains unchanged at [recursive-dependencies.tsv](../normal-toolchain-evidence/recursive-dependencies.tsv).

[dependency-manifest.json](dependency-manifest.json) records ordered chunk hashes, byte sizes, line ranges and data-row counts. Concatenation was checked byte-for-byte against the original, whose SHA256 is `177ff8d281782d236a90be47321b9021114b904bcc42b669462e90f679360e8d`. Only the first chunk includes the header. For an independent reconstruction, run from this supplement directory:

```sh
cat dependency-chunks/part-*.tsv > /tmp/recursive-dependencies-reconstructed.tsv
sha256sum /tmp/recursive-dependencies-reconstructed.tsv
cmp /tmp/recursive-dependencies-reconstructed.tsv ../normal-toolchain-evidence/recursive-dependencies.tsv
```

The Python-only [reconcile.py](reconcile.py) parses the original audit outputs and verifies:

- 19,216 lines = one header plus **19,215 unique declaration rows**.
- **241 distinct inventoried roots**, all present with matching ownership: [root-reconciliation.tsv](root-reconciliation.tsv).
- Every dependency name resolves to a recorded row. Following recorded type/body/constructor edges from those roots reaches all 19,215 rows; no unreachable rows or missing dependency names.
- **14 opaque entries**: [opaque-body-coverage.tsv](opaque-body-coverage.tsv). Thirteen have nonempty constant-dependency lists. `Lean.opaqueId` has none because its body is its bound argument `x`; see the [installed source excerpt](opaqueId-source-excerpt.txt). An empty constant-dependency set does not indicate that its body was skipped.

This reconciles existing traversal evidence; it is not a new Lean audit or proof build. The original unchanged audit source explicitly traverses `.opaqueInfo v => v.value.getUsedConstants` and increments the opaque count for every such entry. Independent mathematical and audit-method review remains the reviewer's responsibility.

## Toolchain comparison: honestly dated rerun

The original comparison printed its summary to tool output but did not retain a per-file raw receipt. This is a **new comparison**, begun October 15, 2026 at **15:19:25 PDT** (22:19:25 UTC), completed at **15:19:38 PDT** (22:19:38 UTC). It does not retroactively turn the original summary into a retained receipt.

[toolchain-comparison-result.json](toolchain-comparison-result.json) records:

- **17,738 regular files** compared by byte size and SHA256 between retained release-archive members and installed files.
- **12 symbolic links** compared by exact link target; archive directories checked for presence.
- **Zero mismatches, zero extra installed paths**, decompressor exit 0 and empty stderr.
- Archive SHA256 unchanged before/after; Lean, Lake and leanchecker binary hashes unchanged before/after.

The full [raw per-file receipt](toolchain-file-comparison.tsv) is preserved, with [small readable chunks](toolchain-chunk-index.md) and a [byte-exact chunk manifest](toolchain-chunk-manifest.json). [compare_toolchain.py](compare_toolchain.py) is the actual method: stream the zstd tar archive, hash each regular archive member and corresponding installed file, compare link targets, detect missing/wrong types and extra paths, then record pre/post state. No proof compilation or kernel replay was performed. Only Lean/Lake `--version` queries were executed, sequentially, along with filesystem hashing.

[Pre-runtime checks](runtime-pre.json) and [post-runtime checks](runtime-post.json) include version exit codes/output, executable hashes, elan link target, relevant environment overrides and process snapshots. They confirm Lean 4.34.0 / commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Lake 5.0.0-src+293d5d0, no relevant runtime override variables, and no concurrent Lean compiler/checker worker.

## Archive identity and provenance limit

[archive-identity.json](archive-identity.json): retained `/workspace/toolchains/lean.tar.zst`, **580,367,391 bytes**, SHA256

```text
caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b
```

The retained [original setup script](original-prepare-paper-environment.sh) records its download from the official Lean GitHub v4.34.0 release asset `lean-4.34.0-linux.tar.zst` and extraction into the installation directory. The new comparison establishes installed-file equality to that retained archive.

A read-only request to `https://api.github.com/repos/leanprover/lean4/releases/tags/v4.34.0` to obtain independently published asset metadata failed with proxy `403 Forbidden`; see [archive-provenance-result.json](archive-provenance-result.json). **No claim is made that GitHub's published asset digest was independently verified here.** The provenance evidence is the retained setup script and local archive identity. Network policy was not changed, and the blocked query was not retried via alternate routes. A reviewer requiring independent upstream digest authentication must check this SHA256 against the official asset using an authorized connection.

## Preservation and handoff

Only this new supplement directory is added. Original candidate sources, prior evidence, the certified branch and websites are unchanged. The conditional hypotheses remain `UniformSubsetPlusTwo G C` and `0 < C`; no unconditional +6 or acceptance claim is made. No proof builds were rerun. The worker returns idle with no compiler/checker process running. [supplement-sha256.json](supplement-sha256.json) hashes every supplement file except itself.
