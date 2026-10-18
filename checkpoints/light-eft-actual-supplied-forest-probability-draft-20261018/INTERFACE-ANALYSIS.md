# Encoded supplied-forest package — source-level interface analysis

This is analysis of exact saved source declarations, not an elaboration result or a Lean environment query. The proposed source is untested. [Interface snapshots](interface-declarations.txt) preserve the inspected declarations, and [bindings](interface-bindings.json) identify their source/object bytes.

The proposed theorem is `LightEFTSpanners.StoredForestCandidates.polynomial_actual_supplied_forest_package_failure_probability`. Its physical module is `LightEFTActualSuppliedForestProbabilityStage.PolynomialActualFailureProbability`.

## Fixed types, law and predicate

Vertices are `Fin n`. The supplied forest representation is the literal function

`edges : Fin (q+1) → List (Fin n × Fin n)`.

The forest family everywhere is exactly `StoredForestHosts.family edges`. Its literal definition gives `i`th graph `ExecutableVoting.graph (StoredSample.edgeSet (edges i))`; the proof does not unfold that family, substitute another graph representation or assert that arbitrary forest data represents an independently chosen family. The stored interpreter receives `((List.ofFn edges).map StoredEdges.encode)` in the same index order.

Let `wR d = (w d : ℝ)`, `tR = (1+(eps:ℝ))*(2*k-1)`, and

`B = 1 + 64*(f:ℝ)*extremalLightness n (tR+1)/h`.

For a typed edge finset `E`, use the entire predicate

```
IsEFTSpanner G (edgeGraph E) wR tR f ∧
totalWeight (edgeGraph E) wR ≤ B * totalWeight Q wR ∧
(totalWeight Q wR = 0 → totalWeight (edgeGraph E) wR = 0) ∧
competitiveLightness (edgeGraph E) Q wR ≤ B
```

Its association matches the accepted probability theorem exactly. In particular, neither the raw weight bound nor the zero-weight implication is dropped in favor of only the ratio.

The number of repetitions is exactly `m = polynomialRepetitions (Fintype.card (Fin n)) s`. Both inequalities use the same law

```
executionLaw (V:=Fin n)
  (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf m
  (LightEFTSpanners.input G Q wR)
```

and the same assignment `a` and `assignmentTape a`. No distributional change or second sampling space is introduced.

## Exact existing transfer contract

`StoredForestCandidates.assignment_failure_le` has argument order

```
edges seed w hw tQ h banks es hd law P
```

with implicit `n,m,q`. It accepts any `P : Finset (Sym2 (Fin n)) → Prop`. Its conclusion is

`Pr[¬OutputSatisfies n P (actual execute result)] ≤ Pr[¬P (mathematical edges result)]`.

The actual call is the existing `StoredForestCandidates.execute` with the forest list above, both `Q` and initial `E` equal to `StoredEdges.encode seed`, exact encoded rational weights, `tQ = (1+eps)*(2*(k:ℚ)-1)`, and `((rawInputs (banks a) es).map StoredForestBank.encode)`.

`OutputSatisfies n P raw` means there exists a typed endpoint list `out` such that `raw = StoredEdges.encode out` and `P (StoredSample.edgeSet out)`. It is an existential semantic relation to the actual returned raw list. This draft does not charge, implement or invoke a decoder. The existing transfer proves good mathematical edges give a witness for good raw output, hence **bad raw output implies bad mathematical edges**. That is the required direction for the probability inequality.

The bank function is exactly

```
Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m →
  Sym2 (Fin n) → StoredDrawLookup.TypedBank n
```

The correspondence premise `hd` remains literally the existing one: for every assignment `a`, every endpoint pair `e ∈ es`, and every `j ∈ StoredForestHosts.indices edges`, the list of typed draw edge sets in `hostInput edges (banks a) s(e.1,e.2) j` equals `List.ofFn (a s(e.1,e.2) j)`. This preserves the entire ordered draw list, not just its size, support or distribution. It is not weakened to eligible indices or average agreement.

## Two exact representation equalities

The draft retains, rather than constructs:

1. `hseed : StoredSample.edgeSet seed = Q.edgeFinset`.
2. `horder : (es.map fun e => s(e.1,e.2)).reverse = LightEFTSpanners.input G Q wR`.

The first rewrites the seed finset in the transfer's mathematical edge selection to the same `Q.edgeFinset` used by the accepted theorem. The second rewrites the exact candidate sequence, including reversal and multiplicity, to the accepted weight-sorted non-seed input. No candidate ordering algorithm, seed approximation, extra nodup assumption or representation construction is supplied by this proof.

`SampledGreedy.output` is definitionally `edgeGraph (SampledGreedy.edges Q.edgeFinset wR tR eligible host tape h (input G Q wR))`. Thus unfolding it matches `P` on the transfer's mathematical edge result after these two equalities and the rational threshold cast.

## Accepted bound and casts

The accepted theorem's argument order is

```
G Q q f h k s wR (eps:ℝ) hQ (StoredForestHosts.family edges)
  hF hcount hcong hf hh hk hepsR hwR hwposR
```

It already bounds failure of this full package under the same law. The proposed proof applies `assignment_failure_le`, then transitivity with that theorem. It adds no new concentration argument, no new accuracy premise and no arbitrary `hgood` premise.

Rational nonnegativity/positivity are transported exactly to the reals using the existing `exact_mod_cast` pattern. The exact threshold identity is

`(((1+eps)*(2*(k:ℚ)-1):ℚ):ℝ) = (1+(eps:ℝ))*(2*k-1)`.

The draft uses `push_cast; rfl`, matching the existing rational-threshold bridge pattern. There is no rounding error or approximation budget. The final `simpa only` uses `hseed`, `horder`, this threshold identity, `SampledGreedy.output` and `Fintype.card_fin`. Future elaboration must still confirm the implicit assignment length/index instances and definitional reductions of the local `t`/`B` lets. Those are untested elaboration obligations, not additional mathematical assumptions.

## Remaining explicit hypotheses and edge cases

The statement retains `IsFTConnectivityPreserver G Q q`; every supplied forest lies inside `Q` and is acyclic; all non-seed input edges have at least `2*f+h` eligible components; every graph edge has host congestion at most two over the same `Fin (q+1)` family; `f,h,k` and rational `eps` are positive; weights are nonnegative everywhere and positive on input edges. The accepted theorem supplies the package from exactly these inputs. No separate existence or payment for `Q`, the forests, their certificates, seed or banks is proved here.

The conclusion is the existing totalized bound `((n:ℝ)^s)⁻¹`. It retains the accepted `n=0` and `s=0` conventions; no positive-`n` hypothesis or informal real exponent substitution is added. With `n=0`, typed endpoint lists are necessarily empty and representation/order obligations remain explicit; the same existing law and totalized real operations are used. The zero-seed-weight implication is preserved verbatim even though the stated positive input weights constrain when it is relevant.

The probability is over assignments of the existing literal finite law, with banks as an explicitly corresponding function of those assignments. It is not a theorem about an independently implemented bank sampler. Paid sampling/serialization, seed approximation and payment, packing construction/payment, and final runtime composition remain open. The inherited cache/signature provenance qualifications are unchanged. This draft closes only the encoded-output interface **if** it elaborates and passes its separately reviewed future validation.
