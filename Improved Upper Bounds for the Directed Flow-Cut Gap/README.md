# Directed Flow-Cut Gap: unverified integration candidate

This branch contains 191 component sources. It adds seventeen working drafts to
the 174-source candidate so a clean build can give compiler feedback on the
combined dependency graph. Some additions have not compiled. This is not a
verified checkpoint or a complete formalization of the paper.

The additions cover the binary vertex-LP graph oracle, dispatch, guesses and
charge bounds; six concrete finite-data bodies through flag union; a pathwise
approximate packing trace; and finite integer-mass selection. The published
statements keep the actual graph, positivity, representation and oracle-cost
premises explicit. They do not finish the whole bit-runtime/probability proof.

The verified partial baseline is commit
2f3c83e2f3988e75a8800132004c9650a425368f (162 modules, 10,328 declarations).
The 174-source candidate 38949686912c514a50e2569fae79f57ec55513c0 separately passed
its build, index, exhaustive axiom audit of 11,053 declarations, and 174 component
kernel replays in run 37992257057. Its combined execution gate is being recovered
in the separate fc11ede6a4c581c35163dba0698128057895c34d candidate. Those results
are not verification of the seventeen new sources here.

No source outside this one paper is changed. See verification/component-verification.json
for exact source hashes, and STATEMENT_MAP.md and CORRECTIONS.md for the existing
mathematical scope and documented paper repairs. Every new source requires
successful compilation, complete axiom/kernel checks, appropriate execution
tests and independent exact-source semantic reconciliation before promotion.
The direct edge-resource solver, remaining callbacks, weighted outer program,
efficient exact-W construction and final full-paper audit remain open.
