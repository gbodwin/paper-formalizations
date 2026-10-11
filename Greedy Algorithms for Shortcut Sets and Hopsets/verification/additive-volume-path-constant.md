# Exact constant obstruction for the additive-volume question

2026-10-11. Ordinary mathematical proof. Its reciprocal review is recorded in candidate-retirement-semantic-review.json. This is a lower bound on a possible absolute constant, not a counterexample to the existence of some such constant. No numerical experiment is used in the argument.

## Model

Take the directed path on n >= 3 vertices numbered 0,...,n-1 with edges i -> i+1. Give each vertex its singleton covered chain. Within-chain preprocessing is empty and satisfies the actual interface. Take the legal state H empty. The original first-entry filter never removes an edge: the only vertex of a destination chain is its first reachable entry. Every originally reachable pair (s,t), s<=t, is important. Its actual normalized distance is t-s+1. The maximum important distance is L=n.

This family lies in the strongest supplied-chain context of the proposed inequality. It is not an assertion about which cover a particular equal-size packing constructor chooses at the paper's canonical threshold.

## All-candidate marginal formula

Every legal candidate is (i,j) with 0<=i<j<n. An existing path edge has j=i+1 and zero marginal. Every route using a new forward dart is the unique old prefix from s to i, that dart, and the unique old suffix from j to t. Such a route exists precisely for s<=i and j<=t. The DAG allows at most one use of the dart.

For these pairs, old distance is t-s+1; new distance is

    (i-s+1) + (t-j+1).

The difference is b=j-i-1. Pairs outside this rectangle cannot use the dart and retain their old distance. There are a=i+1 choices for s and c=n-j choices for t. The exact decrease in the unchanged raw potential is therefore

    Delta(i,j) = a*b*c,   a>=1, b>=0, c>=1, a+b+c=n.

Conversely every such integer triple is realized by i=a-1 and j=a+b. Thus the all-candidate maximum is the maximum of this three-factor product, without an omitted class of edges or demands.

For a positive product, if two factors differ by at least two, moving one unit from the larger to the smaller increases their product: (x-1)(y+1)-xy=x-y-1>0. The optimum therefore has the three factors differing by at most one. Writing n=3q+r, 0<=r<3, gives

    Delta* = q^(3-r) * (q+1)^r.

For n=3q, it is exactly q^3.

## Necessary additive-volume constant

The proposed inequality L^3 <= C*(Delta*+n), specialized to n=3q, becomes

    27q^3 <= C*(q^3+3q).

For any fixed real 0<C<27, choose an integer q>=1 with q^2>3C/(27-C). Then the displayed inequality fails. Equivalently L^3/(Delta*+n)=27q^2/(q^2+3) tends to27. Any universal constant valid for the strongest all-context question must therefore satisfy C>=27.

This does not refute the additive-volume conjecture with a larger constant. The path itself has genuine cubic progress. It emphasizes that the earlier sufficient active-regime condition L^3>=2Cn cannot be silently replaced by the paper's canonical condition L^3>n. Even the strongest possible C in this proposed form would not make that implication with coefficient1. A separately proved final-window argument or an explicitly modified stopping threshold would still be needed.
