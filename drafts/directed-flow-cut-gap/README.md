# Directed flow-cut source checkpoints

The latest source snapshot is `20261010T0352Z`. These `.lean.txt` files preserve work in progress and are excluded from the compiled library. The snapshot manifest links unchanged files to their earlier snapshots. This is not a complete-paper or verification release.

The separately verified partial checkpoint is [fc11ede6](https://github.com/gbodwin/paper-formalizations/commit/fc11ede6a4c581c35163dba0698128057895c34d): 174 components and 11,053 owned declarations, with full [exact-commit CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38011321856), execution regression and independent source review.

Four newer weighted components now pass strict standalone compilation: approximate packing on actual retained events, integer prefix-mass selection, rational-to-integer mass construction, and binary selection. Their full integration and execution gates remain open. The new literal binary mass constructor, edge-LP work, and runtime callback repairs remain drafts. The final algorithm/probability/bit-cost composition and the companion paper website are incomplete.

See [the latest manifest](20261010T0352Z/source-manifest.json) for exact source hashes and file locations.
