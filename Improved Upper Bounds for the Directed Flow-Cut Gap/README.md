# Directed Flow-Cut Gap: represented-input graph oracle

This is a partial formalization. The current local 269-source runtime closure
constructs the literal graph oracle in one 2,120-slot physical machine: original
demand queries, graph discovery, forward support recovery, canonical path costs,
stable selection, internal mask and capacity bottleneck. One same-run bound
includes the terminal halt. Positive graph order, original heap representations,
word widths and initial heap/address bounds remain explicit. Raw source preparation, the outer adaptive packing controller and the
paper's complete physical runtime remain open.

The exact published 230-source parent [a452bbdb](https://github.com/gbodwin/paper-formalizations/tree/a452bbdbdd587670dfaf1dbe73bf53c34dcf901a)
has [full CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38285499613)
success at 18:45:39 UTC on 12 October 2026: all 70 stages, 230 exact-manifest
kernel replays and 16,027 reference declarations. This candidate's own full CI
remains a separate gate. The separately verified mathematical aggregate351 is
overlapping work and is not added to this runtime source count.

Five import headers are narrowed explicitly, with every theorem body preserved.
The safety, fixture and kernel replay gates remain in force. Exact local receipts
and the independent component/preservation reviews record the candidate's scope.

## Preserved earlier checkpoint notes

# Directed Flow-Cut Gap: pending 193-component candidate

This is a partial formalization of arXiv:2604.03412v3. This integration candidate
contains 193 component sources and awaits its exact-commit build, exhaustive
axiom audit, kernel replay, execution checks and final independent source review.
It is not a completed formalization of the paper.

The verified partial baseline is
[fc11ede6](https://github.com/gbodwin/paper-formalizations/commit/fc11ede6a4c581c35163dba0698128057895c34d),
with 174 components, 11,053 audited declarations and successful
[CI 38011321856](https://github.com/gbodwin/paper-formalizations/actions/runs/38011321856).
That result includes the binary-cover execution regression and independent review.

The nineteen additions cover the binary vertex-LP graph oracle, dispatch,
objective guesses and charge bounds; six finite-data operations through flag
union; a pathwise approximate-packing bound; literal integer-mass construction
and selection; and binary prefix selection with exact stored-width costs.
Fourteen additions passed standalone strict compilation. The five final graph
bound/cost sources have completed development elaboration without diagnostics;
their standalone aggregate build is still a gate. Earlier integration failures
were repaired by proof elaboration and normalization changes.

The pathwise packing result gives a marginal bound of 3 alpha times the original
weight under explicit reached-state oracle guarantees. It does not itself
provide the adaptive random oracle, efficient weighted mass construction or
whole-program probability/runtime proof. Full edge-resource execution, weighted
outer composition, exact-W construction and final paper audit remain open.

See STATEMENT_MAP.md, CORRECTIONS.md and VERIFICATION.md for the exact scope.
All source hashes are in verification/component-verification.json. This candidate
preserves every component of the verified 174-source baseline byte for byte.
