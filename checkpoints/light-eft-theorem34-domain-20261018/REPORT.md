# Narrow domain clarification of the conditional strategy barrier

Previous proof checkpoint: **`27a4c6aec51c86d85805a981e85879b57c6a0982`**. The parent independently accepts the asymptotic handwritten barrier except for this domain clarification. No new formal/Lean acceptance is claimed.

The **only mathematical text change** is in hypothesis 1, before R is defined:

> Require `n_(f,i)≥2` for every f,i.

On a singleton graph the nontrivial-cut condition is vacuous and D_q=0; n→∞ alone does not exclude singleton initial indices. The explicit hypothesis makes the denominator/normalizer discussion apply at every index. The proof, constants, order of limits, other hypotheses and original-theorem scope are otherwise byte-for-byte unchanged. This is a clarification of the research statement, not a new paper error or a theorem refutation.

[statement.diff](statement.diff) contains the exact change. The [previous report](previous-REPORT.md), [previous manifest](previous-manifest.json) and immutable prior commit preserve the previous version/evidence. All 11 original bindings were verified before editing; all other prior files remain unchanged. Current bindings are refreshed without rerunning any experiment or proof tool.

No other mathematics, candidate experiment, Lean/compiler/kernel check, retrieval, extraction, accepted source, runtime/preparation or site change occurred. No new construction escaping the barrier is claimed. Candidate experiments remain stopped. The worker pauses for independent review after publication with CI skipped and exact remote verification, the common lock free and no compiler/checker process running.
