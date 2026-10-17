# Light EFT provenance fixes — preparation only

This additive checkpoint supersedes the parser and extraction proposal in preparation `1fa65a85179b9343463d4f55a848944d0e75efb9` / evidence `3f2c39d34259de417cca937a343a964c86509e9f`. All old inputs, scripts, raw failures and reports remain unchanged. Production remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`; the accepted preparation harness is `ded293f2e4b17405cd009c5ba65acf913154b139`. No Lean, checker, extractor, installation, CI, dispatch, namespace change or website action occurred. This is not artifact acceptance or execution approval.

## Exact whitespace and conservative boundaries

The corrected isolated `cache_mapping.py` replaces Python `str.isspace` with the exact four-character predicate from pinned `Init/Data/Char/Basic.lean`: space, tab, CR, LF. Like pinned `ParseImportsFast.whitespace`, it rejects tabs before applying the predicate. At a scanned token boundary, other ASCII controls and all non-ASCII characters cause explicit refusal. Ordinary comment contents remain opaque; documentation comments terminate the header. Thus NBSP, vertical tab and form feed can never silently introduce another import. This restricted parser deliberately refuses some inputs for which the pinned parser would merely stop reading the header. It does not claim to implement arbitrary Lean syntax.

`boundary-fixtures.json` has 26 source-derived cases: NBSP/VT/FF/NEL/NUL at initial, post-keyword and post-identifier boundaries, accepted space/CR/LF, prefix-keyword behavior, comment boundaries and contents, documentation/body termination and EOF. Tests also cover tab rejection at three boundaries. Expected outcomes come from the pinned definitions preserved with SHA256 in `evidence/pinned-parser-definitions.json`; these are source-derived differential fixtures, not execution against a Lean oracle. The whitespace predicate is compared against the literal alternatives extracted from the pinned source for every Unicode scalar value.

The corrected Python derivation was run over the unchanged 486 frozen project headers and all 3,808 dependency modules. Its full serialized mapping is **byte-identical** to the previous 3,059,710-byte mapping, SHA256 `7c5150b666457ce16e835cdb2b5044ea8d2a29f005d05a79d5cbaf772af540b5`; root key remains `1d7d1aa06138c6e4`. Previous ordered mapping chunks still reconstruct these exact bytes. Frozen project hashes are enforced by `derive`; dependency source hashes, ordered imports, pins and all cache keys are identical. This does not authenticate existing archive contents against an official origin.

Five Python-only tests passed; raw commands/results and the regeneration result are preserved. The parser remains a review candidate outside the execution harness.

## Retained archives and explicit packaging disposition

The new `prepared-extraction-command.json` removes `--delete-corrupted`. It points to the unchanged, hash-bound prior stdin and archive inventory. The old command is retained as historical evidence and is **superseded, not authorized**. The new proposal never deletes retained inputs. Any separately authorized extraction must verify input hashes before and after, retain failure diagnostics, and quarantine failed output without mutating the source cache.

Extraction staging and the installable artifact have different inventories. Every extracted regular file must be recorded with archive identity, relative path, length and SHA256 before filtering. Path traversal, links, unexpected executable output or unclassified files stop packaging. Cross-archive output collisions must be recorded and compared; conflicting contents stop packaging. No output inventory exists yet.

| Pinned cache output | Proposed disposition |
| --- | --- |
| `.olean`, `.olean.server`, `.olean.private`, `.ilean`, `.ir` | Include only mapped dependency-module regular files under the consumer's exact `.lake/packages/<pin>/.lake/build/lib/lean/` path schema. Preserve each hash and originating archive in the bundle manifest. |
| `.trace`, `.olean.hash`, `.olean.server.hash`, `.olean.private.hash`, `.ilean.hash`, `.ir.hash` | Preserve in the complete extraction evidence inventory/staging; exclude from the installable object bundle. They are not a replacement for SHA256 provenance. |
| `.ir.sig`, `.ir.sig.hash` | Preserve and inventory; exclude under the current reviewed consumer allowlist. No claim that exclusion is sufficient for every later load. If these are required by the planned verification, stop for a separately reviewed consumer/packaging change before execution. |
| Generated `.c`, `.c.hash` under the cache IR directory | Preserve and inventory as extraction evidence; exclude from the object bundle; never compile or link them. |
| Optional `.extra` | Inventory and quarantine outside the bundle pending explicit review of actual contents; never silently admit it. |
| Any other path/suffix or nonregular member | Refuse packaging; retain diagnostics. |

This disposition accounts for every entry in pinned `Cache.IO.mkBuildPaths`, including its optional `.extra` entry. It does not expand the current artifact consumer allowlist. No missing file may trigger Lean, Lake, Cache.Main, native compilation, linking, or inherited-project-object fallback.

Before artifact acceptance, **each** of the 3,808 archives needs a successful authenticated official HTTPS receipt binding pinned source-to-key mapping, final origin, full archive bytes/length/SHA256, and comparison with any local candidate. Filenames alone are insufficient. Likewise the official Lean distribution bytes must be authenticated against the pinned release URL and reviewed distribution hash, and the extractor member must be compared with the proposed executable. The preserved local distribution/executable hashes alone are not a fresh origin receipt or member comparison. No native extraction is authorized here. Any later approved extraction needs unique input-bound PID/timing receipts, complete output inventory, pins and immutable bundle length/hash/manifest/URL binding. The artifact remains unavailable.

## Same-route HTTP diagnostic: explicit denial retained

One request used the **same URL**, same default `Python-urllib/3.12` identity, default environment proxy handling and normal TLS CA/hostname verification. Redirects were disabled; no alternate host, identity, route, credential, network setting or retry was used.

URL: `https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar`.
Request started `2026-10-17T07:33:32.182801+00:00`. Response: **403 Forbidden**, 17-byte body `error code: 1010\n`, body SHA256 `2938e9f1284180959e33ab1718d0793a72ff6e4cdb8108c34dcd14e69446de5c`. The retained ordered headers include `cf-ray: a4bd9db7fd006aea-DFW`, `server-timing: cfEdge;dur=2,cfOrigin;dur=0`, `server: envoy`, and `x-envoy-upstream-service-time: 100`.

`https-response-body.bin` contains exact response body bytes. `https-response-headers.bin` is the HTTP library's serialized header representation; the receipt also retains ordered header pairs, not a claimed wire capture. Requested/final origin URL is unchanged. Peer-certificate/socket capture failed because the error-response object did not expose the expected `.raw` member; this failure is retained. TLS validation remained enabled. The edge/intermediary markers and body distinguish this from an opaque unexplained 403, but do not conclusively attribute the denial to the cache origin rather than an intermediary. No successful archive bytes were obtained. Retrieval stopped at this explicit denial.

Concrete next access action: the platform/network operator and, if necessary, official cache service operator should reconcile the above URL, UTC, ray ID and response against their existing access policy/logs, and authorize the ordinary route if appropriate. No bypass is proposed and Greg is not asked to debug paths or supply archives. No retry is authorized by this report alone.

## Resource resolution and existing CI option

The prior read-only descriptor evidence remains unchanged: genuine unmasked cgroupfs, visible self group and parent, mount root `/..`, parent limit 16 GiB and observed headroom about 2.34 GiB; ancestors above the visible parent are not exposed. Waiting cannot establish their visibility. No namespace exception is added.

Concrete same-environment operator action: expose a read-only, verifiable cgroup accounting view that includes this process's actual membership and the entire ancestor chain through the hierarchy root, with stable mount identities and unmasked limits/current values. This requires platform/operator provisioning, not worker remounting or a namespace switch; no such change occurred. Admission must then verify every limit and sufficient effective headroom. Merely asserting more RAM does not close the accounting gap.

The specifically identified existing alternative is the repository's prepared `.github/workflows/light-eft-exact.yml` job `verify`, using its existing `ubuntu-latest` configuration. It is a **conditional future CI option**, not a currently allocated or proven qualifying runner. It can be considered only after reviewed artifact provenance, a separately reviewed execution harness/exact guard and qualifying resource accounting on that actual runner. No new environment was created, no workflow installed and no dispatch initiated.

The current guard remains exactly production `78cb40c7837db049d645d73696f2e0b724ce8a3b` plus preparation harness `ded293f2e4b17405cd009c5ba65acf913154b139`. The proportional quiet-window plan remains: coordinate known initiators, stop ordinary compilers while CI owns the slot, prohibit overlapping pushes/PRs/dispatches/reruns, freshly check all active/queued states immediately before dispatch and monitor throughout. Earlier zero-run reads are historical, not a current reservation. The 117 retained workflow definitions have no schedules; dormant refs alone do not justify rewriting 153 branches. GregAcer remains offline/unauthorized according to the parent registry.

## Review handoff

Publish this additive preparation with CI skipped and stop. Required next review covers the restricted parser, source-derived boundary fixtures, unchanged mapping, no-delete proposal and packaging disposition. Access, complete resource accounting, fresh archive/distribution provenance, extractor-member reconciliation and output inventory remain blockers. Theorem 34, modeled-runtime limitations and site issues are unchanged; no whole-paper completion is claimed.
