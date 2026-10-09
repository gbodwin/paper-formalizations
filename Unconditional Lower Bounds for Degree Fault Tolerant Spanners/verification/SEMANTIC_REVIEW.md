# Semantic review of the repaired lower-bound result

Reviewed against Bodwin and Lopez, *Unconditional Lower Bounds for Degree Fault
Tolerant Spanners*, arXiv:2607.07576v1. Final source confirmation: 9 October 2026.
The PDF SHA-256 is
`cbf9a322032cd3c672b663ef8547e74a76435ce6df81ab0c3ad77e70d66f8699`.
The exact 19 source-file hashes are in `checkpoint-source-hashes.json`.

**Result: the repaired new lower-bound argument has a faithful end-to-end
formalization. No remaining mathematical gap was found in its stated scope.**
Independent source-to-Lean review covered every implementation module, actual
graph representations, quantified premises, and the full dependency chain.
Separate compilation, declaration-wide axiom auditing, and official kernel
replay also passed. These checks have distinct roles: kernel validity does not
by itself establish that a statement expresses the paper's intended claim.

## Main contract

For every natural k>=1, `theorem_five_uniform_parameters` chooses one positive
real constant c before the independently quantified N and f. For every N>=2
and 1<=f<=N, it constructs an actual finite simple graph on exactly N vertices.
Every f-degree-fault-tolerant stretch-(2k-1) spanner of that graph has at least
c*f^(1-1/k)*N^(1+1/k) edges. The witness is c=1/2^(k+3), so c depends only on k.
The final inequality uses real exponents and the actual unordered edge set.

There is no assumed hard graph, matching certificate, geometric obstruction,
nearby prime, padding lemma, dense witness, or favorable parameter choice in
the final theorem. Each is proved or constructed internally. The exact prime
family also proves the stronger constant 1/4 for arbitrarily large graph sizes.

## Definitions and nonvacuity

- H and G have the same finite vertex type and H<=G. Faults are spanning edge
  subgraphs F<=G, with at most f neighbors at every vertex; F need not be a
  subgraph of H. Faults delete unordered edges, not vertices.
- For positive integral stretch, `isDegreeFaultSpanner_iff_edist` proves the
  walk definition equivalent to extended shortest-distance inequalities.
  Disconnected distances are infinity. G itself is always an admissible
  spanner at stretch at least one, so the universal claim over H is nonvacuous.
- `Nat.card H.edgeSet` counts unordered graph edges, not ordered incidences or
  an externally supplied count. Finiteness prevents an infinite-type zero
  cardinality convention from making the bound vacuous.
- Unit-weight graphs suffice for the existential lower bound. The code does
  not claim to implement the general weighted upper-bound problem.

## Proof-chain review

1. `Incidence` proves that canonical line records represent exactly the
   manuscript's distinct affine subset-lines for k>=2. Injectivity is proved,
   so duplicate slope-labelled lines are not silently counted. Actual graph
   bijections give the vertex, neighbor, and unordered edge counts.
2. `SlopeAlgebra` and `GeometryWalk` use Vandermonde independence, group repeated
   slopes, telescope displacement, and extract the alternating representation
   from actual graph walks. There is no assumption p>=k or girth conjecture.
3. `ShortReach` proves endpoint uniqueness and supplies an arbitrary endpoint
   when reachability is empty. `PathStraightening` proves equivalence to actual
   slope-restricted simple paths, with the exact cutoff 2*(lineLength+1)<=k.
4. `Construction` includes the protected edge in the matching and proves both
   sides' uniqueness. `CycleObstruction` and `ObstructionAssembly` show that
   every actual short cycle through the protected edge meets this matching.
5. `Blowup` proves actual cloud cardinalities, pointwise fault degree, and a
   surviving projection avoiding the entire base matching. The missing-edge
   contradiction uses genuine graph walks, including loop erasure.
6. `PaperTheorem` assembles the actual incidence/cloud graph without additional
   geometric premises. `Parameters` and `RealBound` derive the exact-family
   inequality and its real-exponent form.
7. `AllSizesParameters`, `Padding`, and `DenseWitness` handle nearby primes,
   isolated-vertex padding, and all remaining dense parameters internally.
   The dense witnesses use complete blocks plus isolated remainder vertices,
   with a separate complete-graph case when the block quotient is zero.
8. `AllSizesRealBound` converts the uniform integer-power inequality using
   positive k and factor, and nonnegative real bases. `AllSizesTheorem` handles
   k=1 separately and places the constant before N and f in the quantifiers.

The statement map records all 17 in-scope numbered items. Lemmas 10 and 13 use
compositions of representation and graph-assembly theorems; the relevant bridges
are proved and included in the aggregate module even when the final theorem can
use an algebraic representation directly.

## Correction and explicit boundaries

The source incidence counts at k=1 are false: actual subset-lines collapse to
one whole-field line, giving K_(p,1). The formal construction therefore requires
k>=2. Complete graphs repair the main theorem's k=1 case for every admissible
N and f. The justification and dated correction are in `../CORRECTIONS.md`.

Lemma 9 is formalized in the point-rooted alternating-walk form used by the
source proof. Broad line-rooted wording can depend on whether non-backtracking
is imposed at the cyclic seam. Every actual cycle application in the main proof
has the required point-rooted form; no needed dependency is omitted. This
convention issue is not presented as an additional confirmed theorem error.

The meaningful all-size domain is N>=2 and 1<=f<=N. For k>1, allowing f to grow
arbitrarily at fixed N would contradict the maximum number of simple-graph
edges. The parameter convention is explicit rather than hidden in an asymptotic
constant. Theorems 2 and 4 are cited background, outside this paper's new proof
and outside the formalized scope. No algorithmic runtime claim is made.
