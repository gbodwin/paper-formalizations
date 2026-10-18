# One fresh unchanged-route cache GET — denied, stopped

Exactly **one** bounded GET was made to:

`https://cache.mathlib.org/mathlib4-master/f/35a94f3f050967bd.ltar`

The request started **2026-10-18T04:28:46.220037Z** and completed **04:28:49.872218Z**. It returned **HTTP 403 Forbidden** with the complete **17-byte** body:

```text
error code: 1010\n
```

The displayed `\n` denotes the final newline byte. Exact response-body SHA256:

**`2938e9f1284180959e33ab1718d0793a72ff6e4cdb8108c34dcd14e69446de5c`**

Retrieval stopped at this denial. There was **no second request, redirect follow, automatic retry, alternate endpoint, identity/transport workaround, credential/network-setting change, candidate archive comparison, extraction, execution, Lean operation, rebuild, replay or audit**. No archive bytes were accepted. This is a current observation; the Oct 17 13:13 UTC 403/1010 request is retained historical evidence and was not substituted for this request.

## Fresh receipt and complete response

Attempt UUID **`4d06e6508fa2469187bcf1e96e4ccd43`**, requester PID **296431**. The helper source SHA256 is **`59f102664ff04a5997fda150685a0342d540c6f0d99ccf988f3d70a17b4d390b`**. It ran once with:

```text
python3 -B -u checkpoints/light-eft-cache-route-single-get-20261018/get_once.py
```

Controller exit **1** means the explicit denial stop, not an incomplete body or unexpected process failure. [invocation.log](invocation.log) preserves its full diagnostic receipt. The source has exactly one opener call; a fresh exclusive claim prevents automatic reinvocation. The old helper was read for its configuration and was **not run**, and none of its fixed output files was overwritten.

The [fresh receipt](attempts/4d06e6508fa2469187bcf1e96e4ccd43/receipt.json) records status, reason, requested/final URL, ordered headers, complete length/hash, EOF/framing evidence, timers, source hash and any transport limitation. The final URL is exactly the requested URL. All **15 ordered response header pairs**, including their original parsed order, are retained. Representative current fields are:

| Header | Observed value |
| --- | --- |
| `date` | `Sun, 18 Oct 2026 04:28:49 GMT` |
| `content-type` | `text/plain; charset=UTF-8` |
| `content-length` | `17` |
| `server` | `envoy` |
| `cf-ray` | `a4c4cc6b8a066bae-DFW` |
| `server-timing` | `cfEdge;dur=13,cfOrigin;dur=0` |
| `x-envoy-upstream-service-time` | `103` |
| `connection` | `close` |

[response-body.bin](attempts/4d06e6508fa2469187bcf1e96e4ccd43/response-body.bin) contains the exact 17 bytes. Library EOF was observed, Content-Length matched, and there was no read exception or byte-limit hit. [response-headers.bin](attempts/4d06e6508fa2469187bcf1e96e4ccd43/response-headers.bin) is **789 bytes**, SHA256 **`f6918a9e92a9d4b490e3732c12924faf7362f2cd787f96adac5965f7a96a47ff`**. It is `HTTPMessage` serialization; neither it nor the ordered header list is claimed as a wire-packet capture. Header URLs were preserved as data and were not fetched.

## Unchanged request route and transport limitation

The helper used default **`Python-urllib/3.12`** identity and the same ordinary `urllib` opener construction as the historical helper: default environment proxy handling, `ssl.create_default_context()`, CA verification **CERT_REQUIRED**, and hostname checking enabled. No proxy, trust-store, request-header or TLS environment was changed. Redirect handling returned None; no redirect was followed. No retry handler or loop was added. Socket timeout remained **30 s**; an overall **45 s** wall bound and **1 MiB** accepted-body bound constrain this one request. At most one overflow byte could be retained before an incomplete-response stop; the actual 17-byte denial did not approach that bound. No extra connection was made for metadata.

The historical best-effort socket/certificate accessor again reported:

```text
AttributeError("'HTTPResponse' object has no attribute 'raw'")
```

That metadata limitation is preserved. Normal TLS verification remained enabled; no certificate/socket fingerprint is claimed, and no alternate interface/transport request was used to obtain one. The headers/body establish the observed denial on this route; they do not conclusively attribute its cause to the cache origin rather than an intermediary.

## Candidate and review boundary

[bound-candidate.json](bound-candidate.json) retains the previously bound metadata for **Aesop.Script.Tactic**, cache key `35a94f3f050967bd`: expected archive **8,784 bytes**, SHA256 `070e7ab6520a067af651413c741a370c667459d58142029eb905de0fbed4156d`. Its inventory authority was verified by length/hash before the request. Because the response was a denial, **the local archive body was not read or compared**. The success-only comparison branch was never entered. No other archive was fetched or inspected for comparison.

The accepted incremental audit at `c7f33d7ece117ddc7d20e4f7a5dad2f870e9d41f` remains unchanged. [prior-audit-review.json](prior-audit-review.json) records the user's independent review and its precise limitation: the connector could not independently retrieve the full approximately 30 MB canonical inventory, although the manifest and matching **83,032-binding** preservation receipts were verified. No full-inventory independent-retrieval or provenance upgrade is inferred. The audit's 216 chunks/five exports, 8,950 roots, 60,369 closure constants, 48 opaque bodies, three standard axioms and owned cleanup remain within that accepted incremental scope; no whole-paper completion is claimed.

[result-reconciliation.json](result-reconciliation.json) verifies this receipt, exact body/header bytes and helper hash without another HTTP request or candidate archive read. Prior source, objects, resolutions and artifacts were preserved; no mathematical source, pin or website changed. Evidence is published additively with `[skip ci]`, followed by exact remote verification and an idle/free-lock check.

The **unchanged-route retrieval blocker remains HTTP 403/1010**. No workaround was attempted. Authentication of all **3,808 archives**, official toolchain distribution/extractor authentication, any extraction, clean adapter/validation, exact CI and whole-paper acceptance remain future separately reviewed work. Even a later successful single-archive response would establish only that one archive's retrievability/comparison, not those broader results.
