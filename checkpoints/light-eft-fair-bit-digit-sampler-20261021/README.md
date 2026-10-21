# Fair-bit digit sampler and independent-call tape interface

Source-only checkpoint, parent reviewed `9a7e9d8783e4415a59f5f968acca00509c66ebb8`,
accepted native baseline `c1aaa0a00c0c943cec4b2753a937023e9884db04`. The six
reviewed flat-tape additions are unchanged, including Lean source SHA256
`b1d3beaa25f9528611b7ae85c86a41e4feda57b53c62b3a1ccb2cf6c28360ee9`.
No accepted gate, source, workflow or resource limit is altered. Fast is off;
no compiler, admission, push or CI is authorized or launched in this pass.

For q=2f and initial remainder 1, the scalar sampler computes binary digits of
1/q. At state r<q it computes d = (q <= 2r) and r' = 2r mod q, requests ONE
fresh fair Boolean b, and halts with output d if b differs from d. If b=d it
continues at r'. It never asks a primitive for a uniform Fin q integer. The
deterministic List runner returns the exact read count and untouched suffix;
canonical halting words consume t+1 bits at depth t+1.

Randomness is explicitly modeled by `fairCoin`, mass 1/2 for each Boolean, and
fresh `Law.bind` calls at each continuation of `fuelLaw`. This is the specified
probabilistic-program primitive, not a theorem that a hardware RNG or finite
seed is fair. `fuelLaw` is the finite-prefix operational semantics. Its waiting
mass after t fresh bits is exactly 2^-t. Almost-sure termination is stated as
that mass tending to zero and total finite halting-trace mass being one; no
separate measure-theoretic theorem over a supplied infinite stream is claimed.

The source claims exact bias 1/(2f), finite-trace normalization and an expected
consumption of exactly TWO fair bits/reads per scalar call, including the final
bit. These are random-bit/read counts, NOT a bound on arithmetic bit operations,
machine steps, memory allocation, worst-case termination or total paper runtime.
The all-matching infinite bit path is nonterminating with zero mass in the
declared prefix semantics; there is no deterministic finite worst-case bound.

`IndependentTapeLaw` explicitly repeats the DERIVED scalar output law via fresh
independent `Law.bind` calls, proves equality with the finite product, and hence
with the reviewed ideal flat tape and supplied-response assignment event law.
This is a finite-call OUTPUT semantics interface. It does not prove that a
charged implementation threading one shared stream/cursor refines those fresh
calls or preserves the joint output/cost/state law. That refinement and cost
composition remain open; no supplied tensor is assumed to have been generated.

New source: 20 sampler theorem bodies and six independent-call theorem bodies,
all unelaborated. Together with the unchanged reviewed flat-tape module, the
combined checkpoint has 36 unelaborated theorem bodies across three modules.
The author inspects the argument sequentially; fresh independent review is next.
Static hashes, raw Git proofs and finite source checks do not establish Lean
elaboration, replay or audit acceptance.

Source-derived project closures: flat tape 81/82, sampler 82/83, independent
tape 83/84 (existing imports / including the target). Exact native resolution
and fresh objects remain future reviewed obligations. No execution manifest,
new CI adapter or alternate compiler route is introduced.
