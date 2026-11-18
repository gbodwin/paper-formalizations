# Median-tree verification

This repair continues the public recovery commit
`a501d1c841b0dc28544c80f183f3ab940ebf792b`. The November 4 private objects
and the compiler log were unavailable, so the failure was reproduced against
this public source on the pinned Lean 4.34.0 toolchain.

Lean emitted three partial compiler helpers for the original structural
definitions of `Tree.vertices`, `Tree.height` and `Tree.Balanced`. The
repaired definitions keep their original kernel bodies. Executable traversal
and height use a total well-founded fold, with equality to the kernel
definitions proved for every tree. The structural equation compiler
recreates the retained matcher and its unfolding proofs. The proofs below
the definitions in `MedianShortcuts.lean` are byte-for-byte inherited.

## Local evidence

Strict compilation, a separate official kernel replay, and a complete
type-and-body dependency audit passed for the revised MedianShortcuts
module. The comparison binds the original public source and the repaired
source, whose SHA-256 is
`72bbc58ac01800476625a037e349d1e02514db5ce203724e509d959f940c64a6`.

| Check | Result |
| --- | --- |
| Logical declaration audit | 125 declarations, with no unsafe or partial entries |
| Type-and-body audit | 12,781 nodes, 191,355 edges, axioms propext, Classical.choice, Quot.sound |
| Retained matcher | Full type and value match apart from binder names, with matching universe parameters and dependent matcher metadata |
| Retained declarations | 80 checked types and all five matcher-consumer theorem types and proof bodies match apart from binder names |
| Compiler-only inventory | 90 entries recorded separately from logical declarations |
| Compiled evaluation | Inorder traversal and height agree on empty, balanced and skewed trees |

The first comparison in `1edb12e` used Lean's default opaque-value accessor,
which omitted theorem bodies. That commit's CI runs were cancelled. The
corrected audit reads `TheoremVal.value` directly. The projection terms in the
retained tree steps use the same kernel projections and beta-reduced form as
the baseline structural elaborator. The corrected audit also checks that all
four retained tree and edge steps refer to the restored matcher.

The comparison excludes generated simp and nested-proof certificates from the
retained type inventory. All revised logical declarations, including generated
subproofs, are included in the dependency audit. Compiled evaluation is
fixture evidence. The kernel equalities establish the source-level
implementations for all trees.

The active 722-module manifest binds the repaired MedianShortcuts source.
The other 721 source bindings and existing workflow stay byte-identical.
Historical runs are recorded against their original commits. The
737-module dispatcher and original-store candidate has its own frozen inputs.

To reproduce the scoped check from the repository root:

```sh
lake build +DirectedFlowCutGap.MedianShortcuts
bash scripts/CheckFlowMedianRepair.sh
```

The separate CI workflow builds the immediate charging consumer and candidate
schedule as well. The original full workflow supplies the wider build and
kernel checks. Whole-paper acceptance remains open, including original-input
preparation, weighted and edge composition, and the exact-W algorithm.
