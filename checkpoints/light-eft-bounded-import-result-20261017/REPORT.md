# One authorized bounded import attempt: admission refused, no child

Reviewed implementation: `b8d12ff6e9ebd55833b5f6a7afe9a6a0cc21002e`, evidence `81e14e3fa6ea2a5823543af0870e6193020c6045`. Production source remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. The three runner/launcher/accounting files matched the reviewed commit byte-for-byte before invocation. The reviewer was reported finished; local process inspection found no compiler/checker/extractor and the universal lock was free.

**Result: ADMISSION_REFUSED_NO_CHILD.** Exactly one `run_once()` call was made. UUID: `4d633a769d284b41b47a8aae74961d6c`. Created at **2026-10-17 13:32:58.948472 UTC**, finalized at **13:33:44.304978 UTC**. The runner recorded `RuntimeError('Visible headroom below required floor')`; the wrapper exited 1. No launcher, Lean, checker or extractor started. Therefore no import was attempted inside Lean, no pre-exec handshake occurred and no child resource limits needed application.

## Exact admission observation

Admission occurred after streaming the input inventory:

- Visible parent limit: **17,179,869,184 bytes**.
- Parent usage: **17,116,909,568 bytes**.
- Headroom: **62,959,616 bytes (~60.04 MiB)**, below the unchanged **2,147,483,648-byte (2 GiB)** requirement.
- System MemAvailable: **17,794,539,520 bytes**. Host availability did not override visible cgroup refusal.
- Visible child limit: `max`; usage **17,115,373,568 bytes**. Unseen ancestor limits remain unknown.
- Parent OOM counters: oom=1, oom_kill=1, oom_group_kill=0, matching the previously observed historical counts.

The 66,976-entry inventory covers **8,992,356,010 bytes** of input. Streaming hashes read file contents without holding the whole inventory's bytes in RAM, but the reads increased file-cache accounting. This is the anticipated admission-refusal path, not evidence that the import itself exceeds its proposed cap.

## Preservation and cleanup

The runner held the same universal lock, device **33**, inode **3849**, without replacement. With no child spawned, it still established kernel ECHILD. After refusal it rehashed preserved inputs and verified them unchanged. `inputs-before.json` and `inputs-after.json` are byte-identical, each **23,978,671 bytes**, SHA256 **`0e5ac21fd8217f2ae19be1f5be7e23e080b8c67387efead248fc384ad22053ba`**. The exact submitted import source and both full inventories are retained alongside the receipt.

[The ordered chunk manifest](input-inventory-chunks/manifest.json) provides 120 readable chunks that reconstruct either identical inventory by concatenating bytes without separators. Reconstruction was verified. [Result reconciliation](evidence/result-reconciliation.json) binds the invocation count, inventory identity and terminal checks.

Terminal checks found no compiler/checker/extractor; the same lock was free. Both fixed one-attempt directories remain preserved and will refuse reuse:

- `.lake/bounded-import-20261017-5ba09dcb949541f29eb286e312c9f8ea`
- `.lake/bounded-import-evidence-20261017-5ba09dcb949541f29eb286e312c9f8ea`

No retry, cap increase, fallback, cache clearing/deletion, download, extraction, source change, clean-gate change, installation or CI dispatch occurred. All old tracked sources and evidence remain unchanged. The raw invocation log prints the same exception twice because the wrapper printed its traceback and then re-raised; there was only one invocation and one UUID.

This result establishes only that the unchanged reviewed admission gate refused under the measured conditions and preserved inputs/cleanup. It establishes no import-loading success, proof replay, clean build, heavier-module capacity, cache authentication or CI readiness. Publish additively with CI skipped, then stop for independent review.
