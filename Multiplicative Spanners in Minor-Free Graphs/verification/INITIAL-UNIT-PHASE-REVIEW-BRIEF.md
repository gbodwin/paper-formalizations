# Actual unit-tree initialization, checkpoint30

Eight frozen sources are listed in initial-unit-phase-freeze.json; all202 source/root hashes are in checkpoint30-source-hashes.json. The193 inherited library bodies and all workflow/kernel/index scripts are unchanged. All eight drafts strictly compile; production/root/axiom/replay gates follow in bounded turns.

Please independently verify the actual graph semantics, not just the arithmetic:
1. ConnectedWithin genuinely retains every walk vertex inside its finite set. Actual connected subsets of every smaller cardinality are built by real boundary edges.
2. A finite maximum packing of connected k-sets yields residual connected components of size below k, without a packing premise. Original connectedness plus k≤|V| attaches every whole residual component to an actual selected core.
3. Arbitrary owner choices partition all original vertices; they cannot split a residual component. Actual paths inside each branch have length at most4k.
4. Unit-weight loop erasure gives the simultaneous intrinsic bound min(|B|−1,4k). Each actual original internal edge belongs to at most one branch. Induced connectedness proves at least |B|−1 internal edges.
5. The final unit-tree theorem handles the small-tree case explicitly. Otherwise k=t+1 supplies intrinsic diameter≤8t and conserved credits c max(t, certified branch diameter), paid entirely by disjoint original tree edges. Total reserve≤c(|V|−1).

This is the actual initialization needed for the weighted hierarchy, with integer t>0 and supplied actual unit-weight tree and nonnegative credit rate. It does not claim the remaining low-degree/path/absorption phases, multilevel charging, full weighted lightness, fast runtime, or final whole-paper audit. The tree is the intended MST input to initialization; its existence/reweighting interfaces are separate existing lemmas.

Save review/initial-unit-phase-review.json with exact reviewed hashes and scope. No compiler needed for this reciprocal source review.
