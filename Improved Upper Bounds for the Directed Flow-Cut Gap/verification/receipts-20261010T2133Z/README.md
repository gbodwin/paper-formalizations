# Verified partial aggregate advanced to 251 modules

Exact commit 82b0a95c0a4062f5f2f81a4790a144a680d52d1d passed CI 38082454802 on 2026-10-10 at 21:25:15 UTC. All source/index/strict gates, the full 16,576-declaration flow-cut axiom audit, original regressions, eight recovered runtime bodies, five graph-execution groups, four weighted/tape groups and three zero-safe-packing groups passed. All 326 project leaves, including all 251 flow-cut modules, passed independent kernel replay; the import-only flow-cut root then passed the official exact-root replay.

The former driver unintentionally selected every prefix-matching module concurrently when asked to replay the root after all leaves. The corrected driver calls the same official replay function once for the exact root, preserving every leaf check. Its independent source review and terminal resource record are included. The successful root process took 5.93 seconds with maximum RSS 7,355,856 KB. This proves the driver duplication and successful repair; the former shutdown's OS cause remains unknown.

Independent reviews cover the 14 graph and 44 non-graph additions, and the final eight-module repair reconciliation. Fifteen pathwise helper signatures now explicitly include a fair-bit full-support premise; both final exported bounds discharge it from the actual full_support proof. Do not describe the helper-level change as assumption-preserving.

This is a verified partial paper checkpoint. Later separately verified components are documented in separate receipts and are not implicitly included in the 251 aggregate. Full graph representation/compilation, raw input and fuel/budget construction costs, and complete end-to-end physical runtime remain open. Final whole-paper skeptical audit and personal research website completion link remain future gates.

This evidence checkpoint changes documentation only. No proof, workflow or existing source is changed.
