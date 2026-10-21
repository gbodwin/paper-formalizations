# Ordinary Flow continuation: source and evidence reconciliation

Status: historical checkpoint recovered; no new Lean acceptance or whole-paper
completion. Compilation, push and CI remain paused for parent coordination.

## Source and scope

The source is Bodwin–Samborska, *Improved Upper Bounds for the Directed Flow-Cut
Gap*, arXiv:2604.03412v3, 9 July 2026:
https://arxiv.org/html/2604.03412v3 . The version/date and main-result statement
were checked against the publisher's HTML on 21 October 2026. A shell download
returned HTTP 403; no local full-paper source artifact is claimed.

The original main result remains unfinished as a formalization project. Its
constructive randomized polynomial-time guarantee is part of the target, not
an optional extension. The existing STATEMENT_MAP records mathematical bounds
and probability components separately from unfinished algorithmic obligations.
Its historical checkpoint paragraphs and VERIFICATION.md's 193-component heading
are not the current source-closure count.

## Exact ordinary baseline

Branch: directed-flow-cut-grid-family-runtime-20261013.
Commit: ea1dfba989c89eb8ceed693cdad42ba8d96584f5.
Lean: 4.34.0. Mathlib: 5ed2965256430c3649e86755f9576b54eca72435.

The baseline was fetched independently from gbodwin/paper-formalizations into
/workspace/flow-ordinary. The configured /workspace/paper-formalizations checkout
remains clean on work at dc376e8efac8c1bc236abbe68d296060d7ba4142.
No canceled/deleted October 15 workspace or conversation was consulted.

Read-only remote branch inventory found a newer ordinary preserved draft at
f853a31d941c5466647c14dca86e928164ca8c27, branch
flow-unverified-recovery-20261014. Its two commits after the baseline change
58 paths, all under recovery-checkpoints/. Its README explicitly identifies
reconstructed dispatcher/envelope bytes and unverified original-store drafts.
It is retained as a remote ref, not promoted into the checked source closure.
No independently preserved 830/834/842 checkpoint was identified in this
inventory. Their absence here is not evidence that their work never existed.

## Independently checked historical evidence

GitHub run https://github.com/gbodwin/paper-formalizations/actions/runs/38479792598
has successful check job 115579296014. The connected GitHub tool returned its
full decoded job log. Checkout output identifies the exact baseline commit.
The log records 26,090 audited declarations and 722 successful kernel replays.
All 722 unique replay names match reference-recovery.json's selected source set.
CheckReferenceRecovery.py passes all 722 source hashes and both fixture bindings.
All 13 embedded receipt/log payloads in grid-envelope-runtime-local-evidence.json
match their recorded SHA-256 values. These are historical verification facts;
no local Lean compiler or kernel replay was run in this continuation.

Preserved evidence is in /workspace/flow-evidence-20261021: the decoded CI log,
remote-head inventory, reconciliation.json, and a SHA-256 manifest. The earlier
shell GitHub API request returned Forbidden; the connected read succeeded.

GridFamilyEnvelope.family_fixed_polynomial_bit proves the bound for the same
physical grid-family run, including its terminal attempt, from represented
cost/graph/demand roots. It retains the initial heap/address/source-width,
dense-cursor and empty-stack premises. The 12 new envelope fixtures are numerical
checks, not additional physical runs. Positive whole-grid natural-reference
fixtures retain that classification.

## Open obligations and next narrow step

1. Reconcile the preserved final-dispatch draft with the exact 722 baseline;
   validate actual branch composition and ordered complete-state output before
   treating it as a completed machine.
2. Discharge represented-input premises via original-store construction, while
   keeping typed Vector/Fin inputs distinct from a raw external parser and
   declared list/Boolean charges distinct from actual physical machine charges.
3. Complete the remaining solver-to-rounding/weighted outer composition, edge
   path, reductions and exact-W weak-decomposition algorithm/runtime obligations
   recorded in STATEMENT_MAP. A grid-family runtime result alone does not finish
   these source claims.
4. After parent coordination: one compiler only, focused changed-module and
   dependency checks, then all relevant kernel replays, exhaustive declaration
   and allowed-axiom audits, sequential independent review, exact-commit CI and
   preserved evidence before acceptance. Preserve all resource gates, including
   the existing 240-minute workflow cap. Only propext, Classical.choice and
   Quot.sound are permitted axioms.

The environment has a four-CPU cgroup quota, 16 GiB memory cap, no swap, about
30 GiB free disk, and no Lean/lake/leanchecker process at inventory time. Fast
mode was not enabled; this session exposes no independent billing/mode readout.
Parent coordination must preserve Standard usage/Fast off. Light EFT retains
CI/integration ownership at 70492ce724a942392d94d13ca273c4a0aa208628,
run 39584225670; that run was not launched, changed or adopted here.

## Companion PaperLab

Fresh Sites owner inventory returned ten sites and no continuation cursor;
none is the Flow companion. No site was created or published. A companion must
keep full-paper source coverage, explicit corrections, theorem-to-Lean scope,
and acceptance evidence aligned; partial completion must not be published as a
finished paper. Existing distance-preserver, alternate-light, degree-fault and
minor-free projects were not modified.
