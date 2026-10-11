# A Note on Distance-Preserving Graph Sparsification

Greg Bodwin. Information Processing Letters (2022).
Source: https://arxiv.org/abs/2001.07741v3 (7 May 2021).
Site: https://paperlab-distance-sparsification.greg-bodwin.chatgpt.site

## Scope and status

New project selected on 11 October 2026 after checking all nine existing Sites,
all accessible GitHub repositories, the full main tree and all repository branches.
There was no prior Site or Lean project for this paper.

This is an in-progress formalization. No theorem is certified by this initial
checkpoint. The first module implements an explicit finite form of Lemma 1,
including termination and the edge-union construction, pending compilation.
The five graph applications remain to be connected to actual constructions.
Theorem 5.2 and Theorem 10 are cited background inputs in the paper itself.

The original v3 TeX, bibliography and arXiv HTML are retained in `source/`.
The author's retraction of the earlier all-pairs +4 claim is preserved. It is
not a new discovery from this formalization.

## Verification discipline

Use the repository's pinned Lean 4.34.0 and mathlib revision. Proved means:
compilation, an audit allowing only `propext`, `Classical.choice`, `Quot.sound`,
and independent kernel replay. Conditional reductions are labeled separately.
No `sorry`, new axioms, native_decide, or weakened restatements count as proofs.

The local runtime currently cannot locate its own executable through the
container's per-process `/proc` path. Standard installation and explicit
LEAN_SYSROOT/LAKE_HOME were tried. GitHub Actions is the independent fallback;
the toolchain's kernel and runtime have not been patched.
