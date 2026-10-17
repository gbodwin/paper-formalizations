# Targeted historical-file advice passed; fresh arena128 chain refused

**TWELVE-FILE_ADVICE_COMPLETED; CHAIN_ADMISSION_REFUSED; ZERO LEAN CHILDREN.** One finite targeted advice pass was followed by exactly one fresh chain invocation. The unchanged 3.5 GiB visible-headroom gate refused that invocation before child creation. Compilation, allocator logging, official resolution and singleton kernel replay did not execute. No retry or gate relaxation followed.

## Exact targeted advice pass

The pass covered exactly the four closed raw files inputs-before.json, inputs-after.json, hash-advice-before.jsonl and hash-advice-after.jsonl from each approved checkpoint:

| Checkpoint | Published manifest commit |
| --- | --- |
| light-eft-finitelaw-arena128-chain-20261017, evidence/compile | 8f5f4c80e6bd86074b0fee59ec2aa728c9e23d4e |
| light-eft-finitelaw-bounded-chain-20261017, evidence/compile | 5ffa5b72db912bfa251a07c9aacb42a67a47464e |
| light-eft-3gib-import-result-20261017, evidence | 7ec594260eea20cc893fa2030179d98e1a2eb0a8 |

Total **302,254,496 bytes**. Exact paths, bytes, published manifest hashes and expected content hashes are in [historical-files.json](historical-files.json); the three published manifests are preserved under historical-manifests. The plan is hash-pinned in targeted_advice.py and does not expand recursively.

Under the existing universal exclusive lock (device 33/inode 3849), each file was opened read-only with no-follow/nonblocking flags, checked regular, streamed through SHA256 on that same descriptor, compared with the published hash/size and stable identity, then advised once with POSIX_FADV_DONTNEED over offset 0/length 0. The same descriptor's identity was checked again after advice. All 12 hashes matched and all 12 calls succeeded. These operations wrote no historical bytes. There was no deletion, global clearing, redownload or extra pass. The targeted files are outside the compiler input sweep.

[Full pass accounting and individual receipts](advice-result.json):

| Measurement | Bytes |
| --- | ---: |
| Visible headroom before | 3,560,394,752 |
| Visible headroom after | 3,871,080,448 |
| Visible current decrease / headroom gain | 310,685,696 |
| memory.stat file decrease | 302,264,320 |
| memory.stat anon increase | 303,104 |
| memory.stat kernel decrease | 8,699,904 |

These are measured counter changes around the finite pass. The file counter decrease supports actual file-cache reclamation, while the total current change also includes kernel and anonymous changes. Advice return values alone do not prove reclamation or exclusive causal attribution.

## One fresh chain, then refusal

Fresh root suffix `80ebc98f7f5d46d19051db96577f0952`; initially empty project output root. Chain admission attempt `34955cf074ce4f67b428ad054c4997f5`, created 2026-10-17T14:43:24.454884+00:00, finalized 2026-10-17T14:44:29.935659+00:00. Actual child PID and exit code are null: no child was spawned.

| Post-preflight gate | Bytes |
| --- | ---: |
| Required visible headroom and host MemAvailable | 3,758,096,384 |
| Actual visible headroom | 3,703,836,672 |
| Visible headroom shortfall | 54,259,712 |
| Host MemAvailable | 17,727,184,896 |

Host MemAvailable passed; visible headroom failed. [Authoritative receipt](evidence/compile/receipt.json) and [supervisor traceback](invocation.log) preserve `RuntimeError('Visible headroom below required floor')`. This is admission refusal, not a compiler diagnostic or warning.

As authorized, the unused prior_inventory dictionary was released after the preflight hash/advice list was built; the before inventory remained for postflight checking. The receipt records the release. No quantitative memory saving is attributed to it. It did not make admission pass.

## Prepared settings and preservation coverage

[approved-changes.diff](approved-changes.diff) records fresh paths, coverage of the targeted-pass/driver/bindings sources, and the dictionary release relative to the previously reviewed arena128 chain. The chain model and all resource gates remain unchanged. MIMALLOC_ARENA_RESERVE=128MiB is explicit in all planned stages, MIMALLOC_VERBOSE=1 in compilation only. The existing compile-success gate requires parsed arena_reserve 131072 KiB and records reservations before proceeding. Resolver/replay omit verbosity. None of these allocator settings was exercised here.

Planned, **unexecuted** command:

```text
/workspace/toolchains/lean-4.34.0-linux/bin/lean -j1 -s65536 -M512 -DautoImplicit=false -DwarningAsError=true --root=/workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners -o /workspace/light-eft-verification/.lake/finitelaw-bounded-chain-20261017-80ebc98f7f5d46d19051db96577f0952/objects/LightEFTSpanners/FiniteLaw.olean /workspace/light-eft-verification/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean
```

Configured child caps remain AS soft/hard 3,221,225,472 bytes, CPU 60 seconds, wall 90 seconds, FSIZE 16 MiB and CORE 0, with independent kernel readback before exec. The 512 MiB stop floor, OOM/PID monitor, fresh 3.5 GiB visible/host admission before every child, common lock and fail-stop cleanup are retained. No child handshake occurred, so there is no new observed child limit readback. Six harmless in-process plan/argv/environment checks passed; no compiler ran during those checks.

Frozen production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. The unchanged FiniteLaw source was byte-compared to that commit, SHA256 `7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240`. Official compiler SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; checker SHA256 `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe`. The official-resolution harness and singleton checker plan remain prepared but unrun. Only the fresh output root precedes the dependency/toolchain roots as a project-object search path.

All 66984 compiler-input rows remained byte-identical across before/after inventory verification, SHA256 `59c3c0b3829d13dd49f751f24d5c257cecd68e397e82ac235288fe0756c77789`. [386 ordered chunks](chunks/manifest.json) reconstruct raw inventories/advice logs; all originals remain. Prior source, pins, proofs, partial results and evidence are unchanged. Historical file bytes matched the published hashes before their one advice operation and retained stable same-descriptor identity afterward; those 12 files were not reread by the compiler sweep.

## Terminal state and limits of the result

Before/after same-UID threads: 247; visible pids.current: 269 in both groups; pids.events max 0 unchanged. Parent OOM/kill/group counters stayed 1/1/0; child-group 0/1/0. Full raw accounting is preserved. The kernel no-children check and input-preservation checks passed. Universal lock inode 3849 is free; no Lean/Lake/checker/extractor process remains. The fresh directories and one-use markers are consumed and preserved; no output objects exist. Existing scripts/__pycache__ remains untouched.

This supplies measured targeted reclamation and a fresh admission refusal only. It does not exercise the arena hypothesis or provide new child-side errno, because no compiler child ran. Before another allocator configuration change, the prior errno requirement remains outstanding. No further configuration change was made here.

The route still reuses existing dependency objects with incomplete archive authentication and partial visible-ancestor accounting. No full-clean, successful compilation, resolution, kernel replay, CI-readiness or whole-paper completion claim. Publish with CI skipped and stop for independent review.
