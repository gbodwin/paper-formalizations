# Directed Flow-Cut Gap: UNVERIFIED 251-component candidate

This is an incomplete formalization of arXiv:2604.03412v3. These source bytes
were frozen at 2026-10-10T11:19:02.476639+00:00. The component snapshot SHA-256 is
`d97d8c7713c7be345595abff195aef75aaa940bb9ceb1497779a381e6c4336a7`.

The candidate preserves all 193 component sources from
[6b8a1e24](https://github.com/gbodwin/paper-formalizations/commit/6b8a1e24b087378384898f44108c21345a2a089b)
and adds 58 components: 14 graph-execution bodies, 17 weighted-runtime
components, 22 packing-assembly components, and five dependency modules.
The confidence component includes its proof-only unit-mass consequence. Its
same-query failure contract and provider assumptions remain explicit premises.

This exact aggregate has not been compiled, audited, replayed or executed.
Some added source bytes are uncompiled. No earlier development or standalone
result certifies this snapshot. The verified partial baseline remains
[7d242865](https://github.com/gbodwin/paper-formalizations/commit/7d24286524de9e2b4dbd513a36dc7c6c02a2504a),
with 193 components, 12,650 audited declarations, independent source review,
and all runtime/kernel gates passed in [CI 38054205285](https://github.com/gbodwin/paper-formalizations/actions/runs/38054205285). The full paper is unfinished.

The workflow retains the full repository build, all module-index checks,
exhaustive owned-declaration axiom audit, existing binary-cover and weighted
regressions, and kernel replay. It also integrates the existing eight-body
finite-data/binary-graph regression required by the 193-component candidate;
its execution remains pending. A small parser additionally checks the
printed graph and dispatch charges against their required finite shapes. It adds exact snapshot checking and strict
compilation of every added component. Passing those gates will still leave
the additional source-specific execution regressions and independent semantic
reconciliation described in VERIFICATION.md outstanding.
