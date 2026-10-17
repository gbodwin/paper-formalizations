# Draft incident request — NOT SENT

For the platform/network operator responsible for the existing Light EFT verification environment. Parent to route if appropriate. This requests narrowly scoped diagnosis and authorization; it does not authorize the worker to change settings or begin execution.

**Official-cache access.** Please reconcile this ordinary HTTPS GET against the existing network/cache-service policy and authorize normal official-cache retrieval for the pinned dependency archives if appropriate:

- URL: `https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar`
- Request start: **2026-10-17 07:33:32.182801 UTC**; response Date: **Sat, 17 Oct 2026 07:33:36 GMT**.
- Status **403 Forbidden**; exact 17-byte body `error code: 1010\n`.
- Ray ID **a4bd9db7fd006aea-DFW**; headers include `server: envoy`, `server-timing: cfEdge;dur=2,cfOrigin;dur=0`, `x-envoy-upstream-service-time: 100`.
- Same URL/default route and `Python-urllib/3.12` identity; TLS CA and hostname verification enabled; no redirects, alternate route or retries. Peer-certificate capture failed; the response alone cannot conclusively distinguish service-side denial from an intermediary.

The required scope is successful normal HTTPS reads of the exact official `cache.mathlib.org/mathlib4-master/f/<derived-key>.ltar` inputs recorded in the 3,808-entry pinned map, with per-archive provenance receipts. No credentials, blanket network change, alternate endpoint, user-agent evasion, signature service or user-supplied archives are requested. The worker stopped at the explicit denial. Raw body, ordered headers and receipt are preserved in [the diagnostic evidence](../light-eft-provenance-fixes-20261017/evidence/https-diagnostic-receipt.json).

**Effective memory accounting.** Please provide a verifiable read-only accounting view for this same process/environment that exposes its actual cgroup membership and every ancestor through the genuine hierarchy root, with stable mount identities and unmasked `memory.max`/`memory.current` values. No worker remount, namespace switch, privileged write or replacement environment is requested.

The preserved observation has cgroup2 mount root `/..`, self membership `0::/`, actual observer PID in the visible `init` child, and genuine unmasked cgroupfs descriptors. Visible parent `memory.max` = **17,179,869,184 bytes**; `memory.current` = **14,662,328,320 bytes**; observed headroom = **2,517,540,864 bytes (~2.34 GiB)**. The child limit is literal `max`; its current usage was **14,660,792,320 bytes**. Ancestors above the visible parent are unavailable. Thus the 4,294,967,296-byte admission requirement fails on observed headroom, and unknown ancestor limits independently prevent establishing the effective budget. These are historical measurements, not a present reservation. Waiting or extra free host RAM cannot supply the missing ancestry evidence. See [preserved observation](../light-eft-provenance-inspection-20261017/evidence/cgroup-observation.json).

Please return the access-policy diagnosis and a verifiable accounting interface/description for independent review. Until then, artifact acceptance and clean execution remain blocked. No Lean/checker/extractor, CI installation or dispatch is requested by this incident draft.
