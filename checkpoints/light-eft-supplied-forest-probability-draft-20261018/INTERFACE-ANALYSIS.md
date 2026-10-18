# Exact interface and mathematical analysis — unelaborated draft

Proposed declaration: `LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability`.
Physical module: `LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability`.
The [3378-byte draft](staged/LightEFTSuppliedForestProbabilityStage/PolynomialFailureProbability.lean) has SHA256 `e1db9fb7e7b70d6287eee4df38d231fd882efd08ab8b29da0d7313c6ac4621fc`.

These are source-level interfaces, not fresh `#check` output. No Lean elaboration, kernel replay or audit was performed in this preparation. Future compilation must confirm the imported object interfaces and the draft's implicit-instance/definitional reductions.

## Interfaces used

1. **Accepted deterministic theorem**

   `voting_good_event_of_supplied_forests G Q hQG q f h k w eps F hF hcount hcong hf hh hk heps hw hwpos tape hacc`

   Here `hQG : Q ≤ G`, `F : Fin (q+1) → SimpleGraph V`, and `tape : Tape V (ForestComponentIndex F)`. Its accuracy hypothesis is exactly

   ```lean
   AccurateTrace Q.edgeFinset w ((1+eps)*(2*k-1)) f
     (componentEligible univ F) (componentHost F) tape h (input G Q w)
   ```

   Its conclusion, after reducing its local lets, is the complete conjunction

   ```lean
   IsEFTSpanner G H w t f ∧
   totalWeight H w ≤ B * totalWeight Q w ∧
   (totalWeight Q w = 0 → totalWeight H w = 0) ∧
   competitiveLightness H Q w ≤ B
   ```

   with `t=(1+eps)*(2*k-1)`, `H=output G Q w t ... tape h`, and
   `B=1+64*(f:ℝ)*extremalLightness (Fintype.card V) (t+1)/h`.
   The accepted source/object/22362-constant closure are bound in [accepted-theorem-binding.json](accepted-theorem-binding.json). The object is reused at its existing path, not copied into a project cache or recompiled.

2. **Existing concentration endpoint**

   ```lean
   polynomial_inaccurate_probability
     (G Q : SimpleGraph V) (w : Sym2 V → ℝ) (t : ℝ)
     (q f h s : ℕ) (hf : 0 < f)
     (hQ : IsFTConnectivityPreserver G Q q)
     (F : Fin (q+1) → SimpleGraph V)
   ```

   It bounds the probability of `¬AccurateTrace ... (assignmentTape a) h (input G Q w)` under

   ```lean
   executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
     (polynomialRepetitions (Fintype.card V) s) (input G Q w)
   ```

   by `((Fintype.card V : ℝ)^s)⁻¹`. `polynomialRepetitions n s = 32*(s+5)*n+1`.
   The connectivity-preserver budget is **q**, the same q indexing the supplied family, not f. This hypothesis is used by the existing query-count/saturation proof. The endpoint accepts this same arbitrary F; it does not ask for a newly constructed family or a transport between forest representations.

3. **Finite-law monotonicity**

   ```lean
   LightEFTSpanners.FiniteProbability.Law.prob_mono
     (p : Law α) {P Q : α → Prop} (h : ∀ a, P a → Q a) :
     p.prob P ≤ p.prob Q
   ```

   This is applied to the very same `executionLaw` on the very same assignment type. There is no change of measure, executable-output law, PMF/measure correspondence, or assumed equality of different executions.

## Pointwise bridge and proof direction

Fix G, Q, w, q/f/h/k/s/eps and F before the probability is taken. Put

```lean
m := polynomialRepetitions (Fintype.card V) s
μ := executionLaw (V:=V) (J:=ForestComponentIndex F) f hf m (input G Q w)
H a := output G Q w t (componentEligible univ F) (componentHost F)
  (assignmentTape a) h
```

`assignmentTape a` is literally the existing tape constructor, `fun _ e j => List.ofFn (a e j)`, for
`a : Assignment V (ForestComponentIndex F) m`. All three uses share the same F, component indices, eligible hosts, host function, candidate list, threshold, h, and weight function.

For each a, let `Package a` be the full four-part conjunction above, and `Accurate a` the exact trace predicate in the concentration endpoint. The accepted deterministic theorem gives

`Accurate a → Package a`

by substituting `tape := assignmentTape a`, `hQG := hQ.1`, and all unchanged structural/weight hypotheses. Consequently

`¬Package a → ¬Accurate a`.

The draft's `hmono` supplies that explicit implication to `Law.prob_mono`. It then composes the resulting inequality with the existing `polynomial_inaccurate_probability` bound. No global `AccurateTrace` or generic pointwise `hgood` premise remains in the new declaration; `hacc` is introduced only inside this pointwise contraposition proof.

The direction matters: the old `polynomial_output_failure_probability` covers only correctness and ratio. An upper bound on that smaller failure event does not automatically bound failure of the stronger complete package. This draft instead uses the accepted complete deterministic conjunction directly; it adds no factor-four union bound and drops no raw-weight or zero-weight clause.

The local lets `t`, `B`, `μ`, and `H` are definitional aliases. The call to the accepted theorem has the exact argument order shown above; its local lets reduce to the draft's event. Any elaboration adjustment needed later must be reviewed and its failed attempt preserved, rather than treated as an already checked result.

## Assumptions retained and strengthened

- Finite V with decidable equality; G and Q are simple graphs.
- `hQ : IsFTConnectivityPreserver G Q q` strengthens the former subset hypothesis and supplies `hQ.1 : Q ≤ G`.
- The same supplied family F consists of acyclic subgraphs of Q.
- Each non-seed input edge has at least `2*f+h` component-eligible hosts.
- Every original edge's supplied-forest incidence is at most two.
- f, h, k and eps are positive; w is nonnegative everywhere and positive on G's edges.
- s is any natural number. No new `2 ≤ n`, `0 < s`, positive-denominator, spanning-family, or constructive packing premise is inserted.

The bound is expressed exactly as the existing API's inverse natural power. Its totalized meanings at n=0 and s=0 are retained; the concentration endpoint already handles n<2 through preserver saturation/empty input. This draft does not introduce an additional sampling or small-n proof.

The conclusion concerns the fixed mathematical `executionLaw` and `SampledGreedy.output`. It does not prove that a stored, executable or paid implementation has that law. F and the host-count/congestion certificates remain inputs; Q is not constructed or paid for and is not assumed minimum-weight. Authenticated artifact provenance, clean validation, implemented sampling/runtime, and paid seed/packing remain separate open items.
