# Package-prefix selection reuse: source-only proposal

Base: `ed86a6e8a5fc62e7d807b10dca43669f3cd848a6`. This checkpoint adds proposal files only. Production code, workflow, five live binding specs, proofs, 567-check inventory, and every existing acceptance/resource/lifecycle gate remain unchanged. No policy, model, Lean, compiler, audit or native test was executed for this proposal. Independent review is pending. It does not authorize a physical retry.

## Observed failure and budget

Exact run [39845888749 attempt 1](https://github.com/gbodwin/paper-formalizations/actions/runs/39845888749) is terminal: full job 120058918089 cancelled, focused 120117085101 skipped, aggregate 120117083064 failed. Canonical step 42 and launcher admission step 43 succeeded. Global replay step 44 cancelled; exact full binding step 45 was skipped. No acceptance carries forward from those partial successes.

The full job started at 20:06:18 UTC. Global replay began at 21:26:14, after 4,796 seconds (79m56s), and cancelled at 22:07:50. Its log contains 337 distinct replay-start diagnostics, the exact ordered prefix of the required 567 targets; 230 targets were unannounced. The first was at 21:26:22.3538226, the last at 22:07:47.3529436 for `LightEFTSpanners.PreparedOutputLaw`. These are start diagnostics, not individual completion receipts. The strict sequential loop implies earlier zero exits before successor launches, but this is a control-flow inference, not a complete 567-check receipt. Runner cleanup logged termination of Lake, Bash and the final LeanChecker. No global owned wait4/ECHILD receipt is claimed.

The median of 336 adjacent diagnostic intervals was 7.511626 seconds. Multiplying that observed cadence by 567 estimates 4,259 seconds (~71m) for global replay and ~9,055 seconds (~151m) including the observed prelude. This is an extrapolation, not a measured complete runtime, guaranteed lower bound, or admission forecast. It establishes no safe retry budget. The decoded log says only “The operation was canceled.” The timing is consistent with the existing 120-minute envelope, but no explicit timeout/cancellation-origin message was recovered. Do not report a confirmed timeout trigger or OOM.

## Smallest isolated source proposal

`PROPOSED.patch` factors the existing first-package-marker search into `_selected_root`. Within ONE `validate` call it reuses the selected root for each exact first namespace component, then repeats each used prefix's marker search before return. `selected_path` retains its public signature. No state survives the call.

Under the existing immutable-input/no-writer premise, root choice is a function solely of the ordered roots, exact first component, and predicted directory/file overlay. It is independent of the remaining module components. The extracted helper preserves directory/root-olean marker order, symlink rejection, first-root choice and missing-leaf non-fallback. Every module still validates its components, constructs and compares its complete leaf path, and performs the original required leaf regularity/symlink check. The full ordered `selected` mapping and output schema are unchanged. An induction over the unchanged module iteration therefore gives the same acceptance/rejection and selected mapping on immutable inputs. Final prefix rechecks additionally reject a persistent root-selection or symlink change.

This is not a claim of observational equivalence under arbitrary concurrent writers. A transient change between visits is outside the required no-writer premise; the final recheck does not prove absence of such a writer. Names are exact strings without normalization. No dependency/content/inode hash, declaration audit, collision scan, kernel result, replay, resource sample, or receipt check is reused or removed. `contracts.effective` and its complete physical root/leaf enumeration, binding checks and shadows/prefix checks remain byte-identical.

For M modules and K distinct first components, marker searches in a successful `validate` call change from M to at most 2K; the M module/leaf checks remain. This only reduces the search count when M > 2K. Actual M/K, marker-search elapsed time, peak benefit and the full-job budget effect have NOT been measured from this runner. This proposal cannot yet justify another deadline-bound run. It does not change global replay cadence or eliminate any of its 567 fresh serial checker processes.

## Evidence and next boundary

`BINDINGS.json` pins the production blob, proposed bytes and diff. `BASELINE-package_selection.py` preserves the exact original. `MODEL-CASES.json` is an unexecuted adversarial test description, not a passing fixture report. `QUALIFICATION-PLAN.md` lists the remaining evidence and review boundaries. `TERMINAL-EVIDENCE.json` identifies the complete official failure artifact and compact local log measurements.

The physical CI reservation was released only after all hosted jobs and post-job cleanup were terminal, repository nonterminal queues were empty, and the local compiler inventory was empty. Full official artifact metadata and log hashes are preserved; author-side workspace placement returned no local path, so this checkpoint does not claim to have verified the complete ZIP or its supervised receipts. Coordinator-supported compact receipt extraction remains needed; no repeated large transfer or user recovery is required.

All 36 new mathematical bodies remain unqualified. The accepted `c1aaa0a00c0c943cec4b2753a937023e9884db04` bridge baseline and all previous failures remain preserved. Shared-stream refinement, joint state/cost composition, arithmetic bit costs, bank/caller handoff, aggregate costs and whole-paper acceptance remain open.
