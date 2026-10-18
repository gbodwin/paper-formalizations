# Joint flag table to execution assignment — interface analysis

This is mathematical/source analysis, not a Lean execution or environment query. The supplied proofs are **unelaborated drafts**. [Source snapshots](interface-declarations.txt), [project interface bindings](interface-bindings.json), and [mathlib interface bindings](mathlib-interface-bindings.json) identify the inspected definitions and existing objects.

## Exact index order and law

Fix `n,f,m : ℕ`, `hf : 0 < f`, a finite decidable host type `J`, and an arbitrary candidate list `l : List (Sym2 (Fin n))`. The intended application sets `J = ForestComponentIndex F`; no forest/packing or graph hypothesis is needed for this law bridge.

The flag cube is literally

```
Fin l.length → J → Fin m → Sym2 (Fin n) → Bool
```

with coordinate type `Fin l.length × (J × (Fin m × Sym2 (Fin n)))`. The order is **candidate occurrence, host, repetition, original edge identity**. `candidateAt l p = l[p.val]` gives the candidate key; it need not be injective. Occurrence indices remain distinct when keys repeat.

The original-edge universe is all `Sym2 (Fin n)`, **including diagonal identities**. This matches `StoredFlagSample.sourceLaw` and `SampledGreedy.bernoulliLaw`, which use `Finset.univ`; replacing it by `G.edgeFinset`, a host's edges or an active non-seed set would change this statement. Existing tests later clip original sampled identities to the reached graph. That clipping is not moved into the source sampler.

The source law has three literal product layers:

1. `StoredFlagBatch.sourceLaw n f m hf`, over repetitions of original-edge flags;
2. `hostSourceLaw`, a `productLaw` of that batch for every `j : J`;
3. `jointSourceLaw`, a `productLaw` of those host blocks for every `p : Fin l.length`.

`jointSourceLaw_mass` states the full atomic mass:

```
∏ p, ∏ j, ∏ i, ∏ d,
  if bits p j i d then 1/(2*(f:ℝ)) else 1-1/(2*(f:ℝ))
```

Thus independence is constructed by the finite mass, not asserted as a coupling/accuracy hypothesis. Every host gets a full independent repetition batch even if it is unused at that candidate. No sparse eligible-host sampling optimization is claimed.

## Finite schedule and its cost frontier

`samplingSchedule` is the list product of:

- `(List.finRange l.length).reverse`;
- `(Finset.univ : Finset J).toList`;
- `List.finRange m`;
- `(Finset.univ : Finset (Sym2 (Fin n))).toList`.

The first coordinate is processed from the last occurrence toward the head, matching the logical tail-first update order. Host and original-identity order is the exact supplied `Finset.toList` order; repetitions are in `Fin` order. Draft theorems assert complete membership, no repeated coordinate, and exact length

`l.length * Fintype.card J * m * Fintype.card (Sym2 (Fin n))`.

This is finite mathematical data. In particular, `Finset.toList`/host enumeration is not a charged serialization implementation. The schedule exposes the full table size, including unused hosts and original identities. It does **not** prove that materializing/sampling this table satisfies any final runtime target. Implementing biased-coin draws of probability `1/(2*f)`, charging sampling and enumerations, serializing keyed banks, or replacing full-table draws with efficient on-demand draws needs separate work.

## Decoder, duplicate keys and unvisited keys

`decodeHost bits j i = BernoulliFlags.selected (bits j i)`. The draft `decodeHost_typed` explicitly connects it to the existing sampler representation:

`decodeHost bits j i = StoredSample.edgeSet (StoredFlagSample.typed (bits j i))`.

`StoredFlagSample.typed_edgeSet` supplies that equality. It is a semantic typed-list representation, not a paid decoder call.

The assignment decoder is exactly

```
decodeAssignment [] bits = fun _ _ _ => ∅
decodeAssignment (e::es) bits =
  Function.update
    (decodeAssignment es (fun p => bits p.succ)) e
    (decodeHost (bits 0))
```

This matches the project's `executionLaw` recursion: draw the tail assignment, draw a fresh independent host block, then `Function.update` at the head key. It does not apply updates left-to-right on the input list.

`decodeAssignment_head` is unconditional in `es`: the head block wins at key `e` **even when `e ∈ es`**. Recursively, the leftmost occurrence wins among duplicates. The discarded tail blocks were still independent draws, as in `executionLaw`; no duplicate occurrence is silently removed from the sampling schedule. There is no `l.Nodup` hypothesis. Accuracy theorems may separately require nodup lists, but the law equality itself does not.

`decodeAssignment_outside` gives exactly the empty function at every key outside `l`. This is essential. For example, take `n=1`, `J=PUnit`, `m=1`, and `l=[]`. `executionLaw []` assigns the empty sample at the diagonal key with probability one. Sampling a full candidate-key table and simply decoding every key instead would include that identity with probability `1/(2*f)>0`, so it would give the wrong event probability. The occurrence table plus empty initializer avoids that error.

For a pointwise duplicate example, take `l=[e,e]`, first-occurrence flags selecting an identity and second-occurrence flags not selecting it. The tail-first decoder retains the first selection; a left-to-right updater retains the second. Identically distributed independent blocks can give the same final marginal in this special duplicate case, so this example diagnoses **pointwise update order**, not a false claim about their marginal laws or a paper counterexample.

## Reuse of existing probability contracts

The inspected theorem is precisely

```
StoredFlagBatch.original_probability n f m hf P
```

equating the event law of `fun i => BernoulliFlags.selected (bits i)` under `StoredFlagBatch.sourceLaw` with

```
drawLaw (SampledGreedy.bernoulliLaw (V:=Fin n) f hf).toPMF.toMeasure m
```

The draft `batch_decode_law` applies `Law.prob_map`, then this existing theorem for every event, and obtains equality of finite laws. It does not redo Bernoulli concentration or assume a batch coupling.

The existing `freshBatchLaw` is `batchLaw (testDrawMeasure f hf m)`, while `testDrawMeasure` is `drawMeasure` of the Bernoulli law's measure. It is measure-defined rather than written as a literal `productLaw`. `host_decode_law` uses coordinatewise product pushforward, the existing batch theorem, and the singleton-product identity below to obtain exactly `freshBatchLaw`, with the same host type and repetition count.

## Small generic API steps supplied in the draft

The project has `Law.prob_map`, `Law.prob_bind`, `productLaw`, and `productLaw_measure`, but no matching generic coordinatewise pushforward or occurrence split in those inspected files. The smallest needed transport steps are supplied with explicit proof drafts:

1. `Transport.product_map`: `(productLaw p).map (fun x i => g (x i)) = productLaw (p.map g)`. This is proved by mass extensionality, expanding map/bind/pure, `Fintype.prod_sum`, `Fintype.prod_ite_zero`, and function extensionality. It does not assume `g` injective or a coupling.
2. `Transport.batch_eq_product`: `batchLaw μ = productLaw (Law.ofMeasure μ)`. It follows directly from `Measure.pi_singleton` and `ENNReal.toReal_prod`. This avoids assuming an unproved `ofMeasure`/`toPMF` round trip.
3. `Transport.fin_cons_probability`: split a product over `Fin (k+1)` into an independent head and tail, using the actual `Fin.consEquiv`, `Equiv.sum_comp`, product-type sums, and `Fin.prod_univ_succ`.

`mass_ext` and `eq_of_prob_eq` are small finite-law extensionality helpers. The latter's event-equality premise is discharged by `StoredFlagBatch.original_probability` and later by the proved draft induction; it is **not** a hypothesis of the proposed joint bridge. All generic steps have source-level proof terms in the draft, with no admitted lemma or placeholder. Their API elaboration remains untested.

## Arbitrary-event equality proof

`decoded_assignment_probability n f m hf l P` states

```
(jointSourceLaw n f m hf l).prob (fun bits => P (decodeAssignment l bits)) =
  (SampledGreedy.executionLaw (V:=Fin n) (J:=J) f hf m l).prob P
```

Its only mathematical inputs are the indices, finite/decidable host type, positive `f`, list and event. There is no nodup, positive `n`/`m`, statistical accuracy, bank correspondence or coupling hypothesis.

For `[]`, both sides are the event probability of the constant empty assignment. For `e::es`, split the outer occurrence product, apply the induction hypothesis to each event with the head block fixed, interchange the two finite sums, and replace the decoded host block law by `freshBatchLaw`. `Law.prob_bind` and `Law.prob_map` then give the literal `executionLaw` cons clause. This proves the required tail-first dependence on the old assignment rather than treating the update as if it acted on an unrelated state.

`decoded_assignment_law` additionally packages the result as exact map-law equality. This map is generally many-to-one because of overwritten/unused coordinates; the proof never assumes a global flag-cube/assignment bijection.

Empty candidate lists, `n=0`, `m=0` and empty `J` use normalized empty products and the same decoder definitions. No exceptional positive-cardinality assumption or informal limit is added. Future Lean validation must confirm the casts/definitional reductions in the dependent `Fin l.length` recursion, the generic finite-sum rewrites and the measure/product singleton identity; these are untested elaboration obligations.

## Relation to the accepted actual-output theorem

Any assignment event can instantiate `P`, including the accepted full four-part actual-output failure event with its explicit seed/order/bank premises. Equality alone does not construct the keyed banks or charge their serialization. The accepted theorem's hypotheses are not silently discharged by this bridge. A later composition needs an explicit representation path from sampled flag records to the keyed banks, with duplicate lookup semantics reconciled and its costs paid.

The three accepted staged modules are preserved byte-for-byte and are **not imported or recompiled** by this minimal law bridge. It uses only the existing frozen batch/law machinery. Charged sampling, serialization, seed approximation, packing, final runtime composition, and inherited provenance qualifications remain separate obligations.
