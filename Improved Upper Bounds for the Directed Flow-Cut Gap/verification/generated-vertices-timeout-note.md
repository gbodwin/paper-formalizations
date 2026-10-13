# Resource-only replay window extension

This successor changes only the full workflow job's timeout from 120 to 180 minutes and adds this evidence note. Every proof, strict build, fixture, declaration/axiom audit, source manifest, kernel replay, permission and other workflow byte is retained.

Exact Flow387 commit faa6e537430c86eb6204d2c42b3ba59158ec6782, run 38333094707, job 115087044723, completed cancelled at 2026-10-13 03:43:32 UTC. The job started at 01:38:32 UTC, giving 125 minutes elapsed. Its first 81 stages succeeded; the full kernel replay stage started at 02:37:26 UTC and was interrupted. Its configured job timeout was 120 minutes. This strongly supports a timeout interpretation, allowing for termination handling, but no explicit cause annotation was obtained. The completed job's full log returned BlobNotFound on both 03:47 and 03:52 retrievals; no replay completion count or absence of proof diagnostics is claimed.

The later 394, 411 and 416 exact runs were still running when checked at 03:47 UTC. Exact 394 subsequently passed, completed at 03:51:59 UTC and independently validated against all 86 successful stages, 394 ordered manifest-matched replays and 20,089 declarations. Exact 411 and 416 remained running at 03:58. Their outcomes remain separate, as does the frozen 428 publication's exact run. This change preserves all gates and provides more time for the enlarged exact source closure; it does not convert any cancelled or pending run into a pass. The newest independently validated full-green Flow baseline is exact 394, commit 152f7011889530275b24f28f6387463255f64c6c. Its success does not erase the earlier cancellation; this larger successor retains the more generous window without weakening any proof gate.

Fresh full CI for the exact resource-successor commit remains required.

## Exact cancellation receipt

```json
{
  "status": "EXACT_CI_CANCELLED_DURING_FULL_KERNEL_REPLAY",
  "checked_at": "2026-10-13T03:50:22.688064+00:00",
  "commit": "faa6e537430c86eb6204d2c42b3ba59158ec6782",
  "run_id": 38333094707,
  "job_id": 115087044723,
  "started_at": "2026-10-13T01:38:32Z",
  "completed_at": "2026-10-13T03:43:32Z",
  "elapsed_seconds": 7500.0,
  "successful_prior_stages": 81,
  "replay_step": {
    "name": "Replay the reference closure through the Lean kernel",
    "status": "in_progress",
    "conclusion": null,
    "number": 82,
    "started_at": "2026-10-13T02:37:26Z",
    "completed_at": null
  },
  "configured_timeout_minutes": 120,
  "cause_status": "Timeout strongly supported by the exact configured 120-minute cap and 125-minute elapsed job; no explicit cause annotation obtained. Full job log currently unavailable (BlobNotFound), so no terminal replay count or absence-of-proof-diagnostic claim is made.",
  "workflow_file": "/workspace/shared/flow-recovered-published-20261012T1247Z/production387/.github/workflows/lean.yml",
  "workflow_sha256": "c134b73dd83db6e2366aea4e7c62abb2e179881581f8963d9fae5487753dd6c6",
  "evidence": {
    "run": "2d660924bd7bd537270b0d592d92147309578bd92abc105a5282bdcaab7ce2aa",
    "jobs": "0af3c1ab2be74d5eaa562ec866a12a6ea02a332b013392f4b4a986a3d34b29f4",
    "logs": "472a132c8d783d9302a0b9fe63487871a6d4c4054072948eee11257357593044",
    "check": "32f9807a1c18edaabdae37a922a9c94684927f67e0a209d2443f7b2030a895f2",
    "annotations": "32f9807a1c18edaabdae37a922a9c94684927f67e0a209d2443f7b2030a895f2"
  },
  "full_green_baseline": "5415fa428d633bd729af1160f3b9fe9e40ed9320"
}
```
