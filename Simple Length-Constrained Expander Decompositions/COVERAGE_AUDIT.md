# Statement-by-statement coverage audit

Source: [arXiv:2510.10227v1](https://arxiv.org/pdf/2510.10227v1). Printed page numbers are one less than PDF page numbers. Repeated statements are counted once: **17 results (6 theorems, 11 lemmas) and 17 definitions**. Theorem 2.1 is cited background; the other five theorems are the paper's main results.

## Verdict

**The main-result proof chains are complete with the disclosed corrections. This is not literal certification of every original mathematical claim.** The exact certified proof commit is [ab37e45d850a2cb182193cec7ab9d1ca4b6da20b](https://github.com/gbodwin/paper-formalizations/commit/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b); [its exact CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38064342543) passed at 15:52:55 UTC on 10 October 2026. All 47 modules compile, all 612 declarations pass the permitted-axiom audit, all 47 modules pass independent kernel replay, and eight hash-pinned semantic reports cover the proof chain. This coverage audit changes documentation only.

- Theorems 1.2 and 1.4 retain their printed all-real s·n^O(1/s) forms, with the conventions below.
- Theorem 1.3 has its printed exponent for integer s. Its literal all-real exponent is formally false; a proved rounded/smooth all-real repair is supplied.
- Theorems 4.1 and 5.1 have the original 2/s exponent for integer s and proved 4/s replacements for all real s. **Their sharper original all-real 2/s claims remain unproved, not refuted.**
- The exact generic Lemma 4.2 constant and the literal Appendix A construction are not claimed. Complete constructive replacement arguments prove the needed main conclusions without assuming those statements.
- Cited Nash–Williams is bypassed; the partial separated-volume functional and arbitrary rooted-tree wrapper are unused omissions, not dependencies concealed as assumptions.

## Uniform mathematical scope

Finite simple undirected graphs; actual nonnegative real edge lengths; integral capacities and node budgets. General results allow arbitrary integral node weights and capacities (stronger than the source's degree cap and polynomial capacity bound). Unit-capacity degree specializations use the original graph's degrees. Actual weighted-walk existence and universal strict walk separation implement near/far distance; no separate shortest-distance infimum equivalence theorem is asserted.

The proofs permit h≥0 and φ≥0, extending the printed h≥1 and φ>0. Cut sequences are finite. Sparse cuts require positive maximum separated volume; the union ratio assumes positive total attained volume, while its sparse-sequence specialization assumes nonemptiness. Zero is permitted as a decomposition. These conventions avoid division by zero and cover empty/already-expanding inputs. For the union output, the exact product h′s′=h(s−1) is used even when s′=(s−1)/2<2; the underlying cut predicates are defined for these output parameters.

## Complete numbered inventory

Status “proved” means an explicit finite inequality/construction, not an unformalized asymptotic notation. “Replaced” means the original object/constant is not asserted, and the stated alternative is proved. API files below are pinned to the certified commit.

### Definition 1.1 · printed page 2

**Implemented; real domain repaired.** Matching labels plus exclusion of every earlier walk of length at most s. Real threshold is exactly equivalent to floor(s).

Checked source: [ParallelGreedy.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ParallelGreedy.lean), [RealParameterArboricity.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealParameterArboricity.lean).

### Theorem 1.2 · printed page 2

**Proved with conventions; all real s ≥ 2.** Unit capacities, original degree weights: decomposition cost ≤256s n^(8/s) φm for all real s, and ≤64s n^(4/s) φm for integer s. The printed s·n^O(1/s) form is retained. Zero output is allowed.

Checked source: [DegreeDecomposition.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DegreeDecomposition.lean), [RealDegreeTheorems.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealDegreeTheorems.lean).

### Theorem 1.3 · printed page 3

**Integer theorem proved; literal real exponent false.** Actual partition into ceil(8s n^(2/s)) forests for integer s ≥ 2. For real s ≥ 2, ceil(8 floor(s) n^(2/floor(s))) ≤ ceil(8s n^(4/s)). The K_{a,a} family at s=5/2 disproves a uniform O(n^(4/5)) forest bound.

Checked source: [ForestPartition.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ForestPartition.lean), [RealParameterArboricity.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealParameterArboricity.lean), [BipartiteCounterexample.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/BipartiteCounterexample.lean).

### Theorem 1.4 · printed page 3

**Proved with conventions; all real s ≥ 2.** Nonempty sparse sequence, unit capacities, original degree weights. Exact scaled union and output parameters; loss 2048s n^(8/s) φ for real s, 2048s n^(4/s) φ for integer s. Printed s·n^O(1/s) form retained.

Checked source: [DegreeUnion.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DegreeUnion.lean), [RealDegreeTheorems.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealDegreeTheorems.lean).

### Theorem 2.1 · printed page 5

**Cited background bypassed.** Nash–Williams arboricity characterization is neither assumed nor reproved. A sparse elimination order constructs an actual forest partition instead. The standard characterization concerns nonempty vertex subsets; the printed unrestricted subset wording is not adopted.

Checked source: [SparseOrder.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/SparseOrder.lean), [ForestCover.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ForestCover.lean), [ForestPartition.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ForestPartition.lean).

### Definition 2.2 · printed page 5

**Implemented.** Natural-valued ordered demand, total size, and h-near positive support. Near means existence of an actual weighted walk within the bound.

Checked source: [Demands.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Demands.lean), [Metric.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Metric.lean), [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition 2.3 · printed page 5

**Implemented in stronger scope.** Natural node weights are unrestricted in general theorems, rather than required to be at most capacity-weighted degree. Original degree weights are used in the unit-capacity specializations.

Checked source: [Demands.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Demands.lean), [DegreeDecomposition.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DegreeDecomposition.lean), [DegreeUnion.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DegreeUnion.lean).

### Definition 2.4 · printed page 5

**Implemented.** Separate outgoing and incoming sums are each at most A(v), equivalent to the printed maximum condition.

Checked source: [Demands.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Demands.lean).

### Definition 2.5 · printed page 6

**Implemented with explicit zero convention.** Nonnegative real edge increases and capacity-weighted cost. Zero is permitted as a decomposition; sparse cuts require positive demand volume. Cuts are represented on Sym2 with cost restricted to actual graph edges.

Checked source: [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition 2.6 · printed page 6

**Implemented.** applyCut is the actual length function w+hC; walks use those edge lengths.

Checked source: [Metric.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Metric.lean).

### Definition 2.7 · printed page 6

**Implemented.** Strict separation means every walk has weight strictly above the threshold. No abstract distance oracle or supplied triangle inequality is assumed.

Checked source: [Metric.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Metric.lean).

### Definition 2.8 · printed page 6

**Full-separation case implemented; partial functional omitted.** CutWitness requires every positive demand entry to be separated. The separate partial-sum sep_h(C,D) functional is not defined because no repaired theorem needs partial separation.

Checked source: [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition 2.9 · printed page 6

**Implemented with attained maximum.** demandVolume is a bounded natural maximum; exists_volume_witness constructs an integral respecting near demand of exactly that volume, with every positive pair separated.

Checked source: [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition 2.10 · printed page 6

**Implemented with positive denominator.** SparseCut requires positive volume and cost ≤φ·volume. This agrees with the quotient for positive volume; zero-denominator sparsity is not silently totalized to zero.

Checked source: [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition 2.11 · printed page 7

**Implemented; finite maximality proved.** Finite list with actual prefix-updated lengths. A maximal sequence is constructed in at most the number of initially h-near ordered pairs, hence at most n² rounds.

Checked source: [FiniteTermination.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/FiniteTermination.lean), [NonnegativeCutSequence.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/NonnegativeCutSequence.lean).

### Definition 2.12 · printed page 7

**Implemented.** IsExpander is absence of positive-volume sparse cuts for the actual current length function.

Checked source: [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition 2.13 · printed page 7

**Implemented with zero output allowed.** Actual unscaled output cut, total cost bound and expansion after h*s times that cut. Zero permits already-expanding and empty graphs.

Checked source: [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean), [DirectDecomposition.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DirectDecomposition.lean).

### Definition 3.1 · printed page 8

**Implemented.** Strictly increasing matching labels on actual walks; increasing_isPath proves the required short walks are simple paths.

Checked source: [ParallelGreedy.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ParallelGreedy.lean), [IncreasingPaths.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/IncreasingPaths.lean).

### Lemma 3.2 · printed page 8

**Proved.** Short cycles cannot have a unique maximum-label edge; this follows from the earlier-walk exclusion and matching property.

Checked source: [ParallelGreedy.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ParallelGreedy.lean).

### Lemma 3.3 · printed page 8

**Proved.** At most one short monotone path per endpoint pair, and at most n² in total. General radius r satisfies 2r≤s+1, including r=(s+1)/2 for odd s.

Checked source: [ParallelGreedy.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ParallelGreedy.lean), [DispersionCount.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DispersionCount.lean).

### Lemma 3.4 · printed page 9

**Proved with nonempty-graph convention.** Constructed matching permutations and actual hikers have exactly 2m traversals. If nr≤2m, r>0 and the vertex type is nonempty, an exact length-r increasing walk exists; the short version is a path. At n=0 the literal source existence conclusion needs this convention.

Checked source: [MatchingPermutations.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/MatchingPermutations.lean), [Hikers.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Hikers.lean), [HikerCount.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/HikerCount.lean), [IncreasingPaths.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/IncreasingPaths.lean).

### Lemma 3.5 · printed page 9

**Proved in explicit finite form.** A constructed finite edge hitting set plus deletion and weak counting yields medium_counting. No path-hitting-set assumption is supplied. Nonempty vertices and positive integer radius are explicit.

Checked source: [DeletionCount.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DeletionCount.lean).

### Lemma 3.6 · printed page 9

**Proved in explicit finite form.** Exact fixed-size sample incidence and subgraph transfer yield (nr)(m+1−r)^r < 2N(nr)^r when nr≤m, r>0 and n>0. With r=s/2 this gives the printed asymptotic lower bound. No probability oracle or assumed counting inequality.

Checked source: [FixedSizeSampling.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/FixedSizeSampling.lean), [DensityBound.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DensityBound.lean).

### Theorem 4.1 · printed page 11

**Integer exponent proved; all-real exponent repaired.** Finite nonnegative cut sequence with positive total attained volume. Exact output (1+1/(s−1))ΣC, h′=2h, s′=(s−1)/2. Ratio loss 512s |A|^(2/s) for integer s; 512s |A|^(4/s) for all real s. The sharper printed all-real 2/s bound is not proved or refuted here.

Checked source: [UnionBoundConstants.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/UnionBoundConstants.lean), [RealUnionSparsity.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealUnionSparsity.lean).

### Lemma 4.2 · printed page 11

**Exact generic statement omitted; replaced.** The arbitrary arboricity-oracle bound with literal constant 8α(|A|,s) is not proved or assumed. Repaired directed copies, sparse orientation, support-preserving integral extraction and explicit density yield the bounds above, including all losses.

Checked source: [IntegralDispersion.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/IntegralDispersion.lean), [UnionSparsity.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/UnionSparsity.lean), [UnionBoundConstants.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/UnionBoundConstants.lean).

### Theorem 5.1 · printed page 11

**Integer exponent proved; all-real exponent repaired.** Finite maximality and exact summed witness-volume edge count construct an unscaled decomposition with slack 8s(2|A|)^(2/s) for integer s, 8s(2|A|)^(4/s) for real s. The sharper printed all-real 2/s claim remains unproved, not refuted. No union-bound premise is needed.

Checked source: [DirectDecomposition.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DirectDecomposition.lean), [RealCutSequence.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealCutSequence.lean).

### Lemma 5.2 · printed page 12

**Proved; equality repaired to inequality.** sparseCut_size_bound proves cost≤φ|A| from actual maximum volume. The proof’s equality signs are replaced by ≤, as sparsity only supplies an inequality.

Checked source: [Demands.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Demands.lean), [Cuts.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/Cuts.lean).

### Definition A.1 · printed page 13

**Literal definition invalid; replacement implemented.** Ordered demand cannot equal symmetric undirected counts, and separate row/column capacities do not fit one copy budget. Separate outgoing/incoming copies give 2|A| vertices, an actual matching and exactly |D| edges.

Checked source: [SourceCorrections.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/SourceCorrections.lean), [DirectedDemandMatching.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DirectedDemandMatching.lean).

### Lemma A.2 · printed page 14

**Repaired counterpart proved.** Actual maximum witness demands and support-disjoint stages give an auxiliary graph with exactly 2|A| vertices, summed-volume edge count and reverse-order parallel greediness. The printed |A|-vertex version is not adopted.

Checked source: [DemandMatchingFamily.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DemandMatchingFamily.lean), [MatchingMetricBridge.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/MatchingMetricBridge.lean), [SequentialDemandGeometry.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/SequentialDemandGeometry.lean), [CutSequenceMatching.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/CutSequenceMatching.lean).

### Definition A.3 · printed page 14

**Literal rooted-tree object omitted; replaced.** Incoming-neighbor pairing in a proved sparse orientation replaces arbitrary rooted-tree sibling matching. Odd leftover children pair with their parent; the resulting support consists of actual one/two-edge configurations.

Checked source: [PairingLists.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/PairingLists.lean), [SparseOrientation.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/SparseOrientation.lean), [OrientationDispersion.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/OrientationDispersion.lean).

### Lemma A.4 · printed page 15

**Literal tree wrapper omitted; analogue proved.** orientationDispersion_large proves at least half the auxiliary edge count as paired demand, together with a per-copy incidence bound. The separate statement for an arbitrary rooted tree and its chosen perfect matchings is not formalized.

Checked source: [PairingLists.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/PairingLists.lean), [OrientationDispersion.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/OrientationDispersion.lean).

### Definition A.5 · printed page 15

**Fractional-as-integral definition invalid; replaced.** Scaling by 1/(2α) can yield a half unit, outside Definition 2.2. The replacement derives scaled row/column budgets and extracts a supported integral demand with at most a factor-two mass loss.

Checked source: [SourceCorrections.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/SourceCorrections.lean), [PushforwardDemand.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/PushforwardDemand.lean), [DemandExtraction.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DemandExtraction.lean), [ScaledIntegralExtraction.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/ScaledIntegralExtraction.lean).

### Lemma A.6 · printed page 15

**Literal constant omitted; repaired mass bound proved.** exists_integral_dispersion yields an integral respecting demand with m≤8(K+1)|D|, K=ceil(8s(2|A|)^(2/s)). The original 1/(4α) formula depends on the incompatible literal matching/fractional definitions and is not asserted.

Checked source: [IntegralDispersion.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/IntegralDispersion.lean).

### Lemma A.7 · printed page 15

**Repaired geometry and witness bound proved.** Constructed demand is integral, A-respecting, originally 2h-near and strictly h(s−1)-far after the exact scaled union. The input demands are actual maximizing witnesses. The printed hypotheses mention only arbitrary separated demands, insufficient for the claimed maximum-volume lower bound; this witness qualification is essential.

Checked source: [DispersedPairGeometry.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/DispersedPairGeometry.lean), [UnionWitness.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/UnionWitness.lean), [RealUnionWitness.lean](https://github.com/gbodwin/paper-formalizations/blob/ab37e45d850a2cb182193cec7ab9d1ca4b6da20b/Simple%20Length-Constrained%20Expander%20Decompositions/LengthExpander/RealUnionWitness.lean).

## Unnumbered proof obligations and algorithmic claims

- The actual hiker permutation construction and total travel 2m are proved; the “each hiker walked a path” prose is only used after the proved short-path conversion. Longer increasing walks are not silently assumed simple.
- Heredity under subgraphs, exact finite sample counts, sparse elimination, acyclic forest cover, and unique assignment of each edge are proved. No desired arboricity conclusion is supplied as a premise.
- Maximum cut witnesses are attained, stage supports are disjoint, the auxiliary edge count is the sum of their volumes, and prefix length monotonicity is proved. These are actual derived facts.
- Pairing mass, per-copy incidence, the exact 2A(u) projection fiber, fractional budgets, supported integral extraction and strict final separation are all derived. No union witness is assumed.
- Maximal-sequence termination uses a decreasing finite near-pair count. Maximality proves expansion after the unscaled sum. The printed larger-rescaling step is false; a formal one-edge nonmonotonicity counterexample and a separate two-edge numerical example document the obstruction. The latter full numerical example is not itself encoded in Lean.
- The ratio-of-sums inequality replaces the printed sum-of-ratios implication. Both the valid inequality and elementary arithmetic counterexample are checked.
- Odd integer s is handled by the general radius condition 2r≤s+1. The full-counting and density theorems retain the sharper radius-dependent inequality; the public uniform wrapper states the weaker advertised 2/s bound.
- The introduction cites earlier fast flow, distance-oracle, parallel work/depth, and near-linear-time decomposition algorithms. Those external algorithmic results and the informal flow/cut characterization are background, not proved here. The paper states no new runtime bound for its new existential proof.
- This formalization proves finite construction/existence and a bound of at most n² sparse-cut rounds. It uses classical noncomputable choices and does **not** supply an executable efficient algorithm, a sparse-cut oracle, or bit-complexity bound.

## Remaining original claims and presentation limits

The unproved original mathematical claims are precisely the sharper all-real 2/s versions of Theorems 4.1/5.1, the arbitrary-oracle exact 8α version of Lemma 4.2, and the unused literal rooted-tree statements listed above. None is used to justify a certified main theorem. The literal matching and fractional-demand definitions require the documented repairs; Lemma A.7 additionally needs maximizing witness demands for its volume lower bound. Theorem 1.3's unrestricted real exponent is formally disproved.

Lean proof and private Site identity are distinct. The Site links the exact certified proof commit and CI, and preserves the full original article alongside labeled corrections. Static JavaScript/anchor/control tests passed; actual browser visual/accessibility QA remains unverified. See `VERIFICATION.md`, `CORRECTIONS.md` and `verification/coverage-inventory.json` for the reproducible record.
