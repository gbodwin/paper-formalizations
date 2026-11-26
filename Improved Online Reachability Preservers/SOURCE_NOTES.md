# Source notes

These notes concern [arXiv:2410.20471v1](https://arxiv.org/pdf/2410.20471v1).
The SODA abstract agrees on the displayed rates. The full proceedings text was
unavailable for comparison.

Section 2.2 describes a set of nonempty vertex sequences. The path-system
definition in [8] uses a multiset and requires each vertex to occur at most
once on a path. Separate copies can participate in a 2-bridge. Lean uses
indexed simple paths and permits empty positions as padding of mass zero.
At positive vertex budgets, every maximizing family has nonempty paths.
Filling an empty position with a singleton increases the incidence mass
and preserves the bridge exclusions at the same cutoff.
[Bridge Girth, Definition 6](https://arxiv.org/pdf/2212.11944v4)
· [Checked nonemptiness](OnlineReachabilityPreservers/LocalOrderExtremal.lean).

## The exact path count needs the indexed convention

With distinct nonempty simple input paths, the exact budget \(p=n^2\) is
already impossible for \(n\ge3\) under half-bridge exclusion through size
three. Section 2.2 explicitly counts degenerate bridges. At most \(n\) rows
can be singletons. Every longer row has a different first ordered pair,
since equal first pairs give a half-2-bridge.
The budget would force every off-diagonal ordered pair to occur. Choose
three distinct vertices \(x,y,z\). Whichever of the rows starting with
\((x,z)\) and \((y,z)\) arrives later is the river of a half-3-bridge.
The first step goes between \(x\) and \(y\), and the other row gives the
last step. Full exclusion through size three also forbids the witness.

For positive \(n,p\), if repeated labels are allowed within a path,
distinct constant rows of increasing lengths have unbounded mass and
exclude every full bridge. The cited simple indexed convention avoids
both problems. With distinct simple paths and an *at most* budget, deleting
empty and singleton rows from any simple indexed system preserves either
exclusion at cutoffs of at least two and loses at most \(p\) incidences.
Every retained row is distinct and the arrival order is inherited.
[Exact count obstruction, budget comparison, and unbounded sequence mass](OnlineReachabilityPreservers/DistinctPathBudgets.lean).

When the positive exact counts admit a distinct nonempty simple family, a literal
maximum exists. An unused vertex could extend one path. A bridge cannot
use the added vertex, since each bridge corner occurs on two distinct
paths. Hence the maximum reaches both original counts. At input mean
length above four, the frozen lower length cap forces each output row
to have at least two vertices. Half-two exclusion makes these rows
distinct. At mean length at most four, disjoint paths, distinct
singletons, and directed bipartite blocks give distinct witnesses.
In the odd vertex boundary case, one singleton at each block vertex
supplies the extra unit of degree. This gives the frozen caps relative
to the original mass, including at the literal exact-count maximum
for half cutoff four and full cutoffs three through six.
[Feasible literal maximum](OnlineReachabilityPreservers/DistinctPathBudgets.lean)
· [Literal cleaning](OnlineReachabilityPreservers/FrozenDistinctCleaning.lean).

## Lemma 25 has a false denominator

For an upper bound \(m\), mean at least \(a\), and threshold \(t<a\), the printed
proportion \((a-t)/(m-a)\) can exceed 1. Take \(x=(1,1,2,2)\), \(m=2\),
\(a=3/2\), and \(t=0\). The printed proportion is 3. The corrected denominator is \(m-t\).
If \(k\) values meet the threshold, the total is at most \(km+(n-k)t\).
Thus \(n(a-t)\le k(m-t)\). Lemma 26 only requires a constant fraction in its
uses, for which the corrected bound suffices.

## Theorem 38 prints two different recurrences

The numerator of the update read from Lemma 37 is \(7b-2b^2-2\).
Theorem 38 defines its update with numerator \(7b-b^2-2\) and otherwise the
same denominator \(11b-4b^2-3\). From \(b=2/3\) they give \(16/23\) and
\(20/23\), respectively. The latter exceeds the stated upper endpoint
\(0.701\) in one step. The intended numerator gives the printed cubic
\(4b^3-13b^2+10b-2\) by clearing the denominator in the fixed-point equation.
The last paragraph also requests an exponent strictly above the limiting
exponent. Approximation for convergence should be from below. Its proposed
exponent slack changes signs between the two consecutive displays.
[ExponentLimits](OnlineReachabilityPreservers/ExponentLimits.lean) verifies
the root bracket, the increase of the corrected sequence from below, and
the limits of both online exponents. The limiting incidence theorem absorbs
each finite coefficient into a positive vertex power in the middle range
of path counts. The initial cubic bound handles the two other ranges.
[Unrestricted limit](OnlineReachabilityPreservers/LocalOnlineLimit.lean).

## Lemma 42 doubles the displayed vertex exponent

Write \(M=\ell p=dn\) and \(h=Cp/(\ell d^2)\). The third term of the
comparison \(\ell^2d^2\lesssim\ell^{1/b}d^2h^{1/b}\) yields
\(M^{2b+2}\lesssim n^2p^{2b+1}\). The resulting vertex exponent is
\(1/(b+1)\). Lemma 42 prints \(2/(b+1)\) in the statement and the
concluding rearrangement. Theorem 43 uses the correct value through
\(2-2b'\) for \(b'=(2b+1)/(2b+2)\).
[BootstrapArithmetic](OnlineReachabilityPreservers/BootstrapArithmetic.lean)
checks the rearrangement from that term, with explicit positive parameters,
and its agreement with the recurrence.
[OfflineArithmetic](OnlineReachabilityPreservers/OfflineArithmetic.lean)
checks the full three-term rearrangement over the iteration's exponent range.

## The displayed derivative in Lemma 31 has overlapping cases

Take \(n_1=16\), \(\ell=1\), \(d=4\), \(a=8/11\), \(b=7/10\), and \(x=8\).
The first and third intervals both contain \(x\). Their values are
\(C\) and \((6/11)2^{17/11}C\), respectively. The preceding envelope
is \(Cx\) near \(x=8\).
[SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean) checks the overlap
and the two values for positive \(C\). The [acyclic moment proof](OnlineReachabilityPreservers/SecondMoment.lean)
orders the lengths and bounds clipped powers directly.

## The displayed derivative in Lemma 40 has overlapping cases

Take \(n_1=256\), \(\ell=4\), \(d=16\), \(h=4\), \(b=7/10\), and \(x=24\).
The first and third intervals both contain \(x\) and give slopes \(4C\)
and \(32C/\sqrt{24}\). The preceding envelope is \(4Cx\) near \(x=24\).
The [checked overlap](OnlineReachabilityPreservers/SourceAudit.lean) and
[offline moment proof](OnlineReachabilityPreservers/OfflineMoment.lean)
give the discrepancy and a derivation of the estimate from a subcritical power.

## The path split can create a forbidden bridge

Take the ordered path family `[(0,1,2,3), (3,0), (2,1)]`.
There is no 2-, 3-, or 4-bridge. Splitting the first path into the consecutive
halves `(0,1)` and `(2,3)`, before the other two paths, creates a 4-bridge.
Its arcs are `(2,3)`, `(3,0)`, `(0,1)`, and its river is `(2,1)`. The last
arc precedes the river. This disproves preservation under the displayed split
in the general path-system scope of Lemmas 23 and 39. The example has no common
vertex order.
[SplitAudit](OnlineReachabilityPreservers/SplitAudit.lean) checks both the absence of
any original bridge and the presence of the new half-4-bridge.
[SplitPreservation](OnlineReachabilityPreservers/SplitPreservation.lean) proves
that disjoint consecutive splits preserve the bridge condition at every size
in the acyclic scope. [Regularization](OnlineReachabilityPreservers/Regularization.lean)
uses this to prove the upper caps with at most twice the ambient budgets.

Lemma 10 of the cited *Bridge Girth* measures regularity against the
cleaned witness's own averages. The proof of Lemma 23 here fixes the
averages of the starting maximizer, and Lemma 39 refers to the same
argument. Appendix B of *Bridge Girth* also asserts that its path split
preserves bridge exclusion. The checked example above disproves that
intermediate assertion for arbitrary local orders. The existence of a
cleaned witness is a separate claim.
[Bridge Girth, Lemma 10](https://arxiv.org/pdf/2212.11944v4#page=15)
· [Bridge Girth, Appendix B](https://arxiv.org/pdf/2212.11944v4#page=62).

The midpoint counterexample can also run to termination under the printed
averages. Start on eight vertices with the paths
`[(0,4,5,1,2,6,7,3),(3,0),(2,1),(7,6,5,4)]`. Every vertex has degree two,
the mean path length is four, and every bridge is excluded. The lower caps
already hold. Only the first path is longer than the mean. Replacing it by
its two consecutive halves gives the chain \(2\to3\to0\to1\) and river
\((2,1)\), with the last arc earlier than the river. After the split every
vertex still has degree two and every path has length at most four.
The split increases the path count from four to five.
The same chain occurs in the evaluated factor-four block construction on
a padded, fully bridge-free input with eight vertices, 37 paths, and 46
incidences. Its exact block widths are 23 for degrees and four for lengths.
The padded system uses repeated singleton rows under the indexed convention.
Both inputs admit larger fully bridge-free systems at their original budgets.
The examples refute pointwise bridge preservation under the displayed
operations. The original-average existence conclusion at half cutoff four
has a replacement proof for indexed simple paths. Higher half cutoffs and
the remaining finite full cutoffs are tracked in the statement map.
[Checked average-width examples](OnlineReachabilityPreservers/AverageSplitAudit.lean).

For Lemma 23 at cutoff four, let \(M\) be the mass of the simple indexed
input, \(L=\lfloor4M/p\rfloor\), \(S\) the incidence mass on paths longer
than \(L\), and \(T\) the sum of length excesses above \(L\). Low mass,
small excess, and \(S\ge29M/50\) with large excess have separate
constructions. In the remaining case, each surviving nested reversal
requires two incidences at one vertex. The first is in a late piece of
an overlong path. It has at most one target by the later reverse-partner
bound. Either removing the targets leaves enough mass on the overlong
pieces alone, or one color of a two-color conflict cover leaves enough
mass after selecting the heaviest shorter pieces within the remaining
path budget. The final degree split preserves half exclusion through
four. Quadratic trimming with the exact original vertex width and
peeling at the original means give both budgets, all four original caps,
and at least \(M/5000\). The two budgets are positive and \(M\) is at
least each of them, as at the unrestricted indexed maximum.
[Nested conflict accounting](OnlineReachabilityPreservers/FrozenHalfFourConflicts.lean)
· [Checked half-four cleaning](OnlineReachabilityPreservers/FrozenHalfFourCleaning.lean).

For a fixed collection of ordered, disjoint pieces of a half-4-free family,
half exclusion through size four is equivalent to excluding a retained
nested reversal. Two partners must reverse strictly nested intervals, the
inner partner must arrive later than the central path, and all four steps
must survive, with the two central steps in different pieces. Among
repeated parents, a repeated river parent forces a forbidden parallel pair.
The remaining repeat forces the nested pattern. For simple paths with
positive budgets and mass at least both counts, the stated exclusion lets
the two splits, restriction, and peeling give all four fixed caps, both
original budgets, and at least one sixteenth of the mass. The midpoint example exhibits
the nesting in an eligible original family.
Reordering arrivals does not always remove this pattern. The four paths
`[(0,1,2,3),(3,0),(4,2,1,5),(5,4)]` exclude every full bridge in every
arrival order. Each of the two length-four paths is the inner partner of
the other. Whichever arrives first has a later inner partner. This
six-vertex family also admits a larger bridge-free competitor at the same
budgets.
[Conditional half-bridge cleaning](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean).

Even reordering individual pieces after the midpoint split can fail.
The paths `[(1,6,0),(2,5),(0,2,4,6,3,1),(5,3,4)]` exclude half-bridges
through size four in this order. Every vertex has degree two and the
original mean path length is \(7/2\). The only path above that mean splits
into \(A=(0,2,4)\) and \((6,3,1)\). Write \(B=(5,3,4)\) for the unchanged
last path. The 3-bridge \(2\to5\to4\) has river \(A\) and last arc on \(B\),
so half exclusion requires \(A\) before \(B\). The 4-bridge
\(3\to1\to0\to4\) has river \(B\) and last arc on \(A\), requiring the
opposite order. Both bridges persist after every other printed operation
has terminated. The two constraints obstruct this split and every arrival
permutation of its pieces. A separate cleaned witness meets both original
budgets and all four frozen caps.
[Checked split and order obstruction](OnlineReachabilityPreservers/HalfFourSplitOrderAudit.lean#L103).

Mirroring cuts between adjacent shared vertices gives another way to keep
the original caps. Full exclusion through size three makes the reversed
intervals into chains and pairs a cut with at most one other cut. Projecting
back from these pieces preserves the last-arc arrival condition through
half-bridge size five. A collision during degree splitting would erase at
least two arcs in the projected chain. At half cutoff five this would leave
a full bridge of size at most three, which the input excludes. Using these
splits in the dense case and a separate bridge-free witness in the sparse
case keeps both original budgets, all four frozen caps, and at least
\(M/119\) for simple inputs with full exclusion through size three and a
half cutoff between three and five.
[Mirrored cuts](OnlineReachabilityPreservers/SynchronizedPathSplits.lean)
· [Projection with a collision](OnlineReachabilityPreservers/BridgeVertexProjection.lean)
· [Frozen half-bridge cleaning](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).

The pruning argument in [8], Lemma 20 also works for the half-bridge
condition when processed in arrival order. An omitted incidence marks a
retained earlier incidence at the same vertex. Reusing a mark would give a
2-bridge or a 3-bridge whose last arc was earlier than the river. Lean proves
that at least half the incidences at each vertex survive and that each pair
of surviving paths has at most one common vertex. Under this last condition,
disjoint order-preserving path splits keep both bridge conditions through
size four, even when the paths have no common vertex order. Disjoint
order-preserving pieces suffice through size three without unique
intersections. The half-bridge statements keep the parent path order.
Locally ordered vertex copies preserve unique intersections. They also
preserve full exclusion at every size by erasing repeated vertices on the
projected chain. They preserve half exclusion through size four because
identifying opposite corners of a projected four-bridge would imply a
2-bridge. Neither vertex-split preservation claim needs unique intersections.
The two splits retain all mass
of the pruned system, at most double the ambient counts, and give the
upper caps used in the bootstrap. Restricting the copies back to the
original budgets and pruning low incidences gives the four caps
relative to the pruned input averages. Those averages are at least
half of the original averages.
[Checked pruning](OnlineReachabilityPreservers/OppositeIntersectionPruning.lean)
· [Checked splits](OnlineReachabilityPreservers/CyclicSplits.lean)
· [Local upper caps](OnlineReachabilityPreservers/LocalRegularization.lean)
· [Bridge Girth, Lemma 20](https://arxiv.org/pdf/2212.11944v4).

For actual contiguous pieces, the mirrored-cut argument also lifts a
size-six bridge when the input excludes full bridges through size three.
The slot argument first distinguishes parents of neighboring slots and
slots separated by one other step. The three antipodal pairs of slots
remain. In each pair, the two possible orders of disjoint contiguous
pieces would both give an original full 3-bridge if the parents agreed.
This applies to the actual consecutive width blocks under unique
intersections, where opposite-cut constraints are vacuous. For positive
budgets and mass at least both counts, the cleaned witness meets both
budgets and all four frozen caps and retains at least one sixteenth of
the input mass. The half-bridge version through size six assumes full
exclusion through size four to justify the vertex-copy projection.
The earlier packing that can reorder positions need not make contiguous
pieces in the original order. The six-vertex noncontiguous example
remains a counterexample to using only the opposite-cut constraints.
[Six-bridge lift](OnlineReachabilityPreservers/CyclicSplits.lean)
· [Six-bridge cleaning with unique intersections](OnlineReachabilityPreservers/ContiguousSixCleaning.lean)
· [Noncontiguous example](OnlineReachabilityPreservers/CyclicSplitLimits.lean).

At full cutoff six, opposite-intersection pruning followed by restricting
to a quarter of each support permits the contiguous construction on an
unrestricted maximizing family of indexed simple paths. If the quarter
support is too sparse, a single row or a family of singletons supplies
the required mass at this constant. The resulting witness keeps both
budgets and at least one 392nd of the maximum. Its four caps are measured
against its own averages.
[Output-average theorem](OnlineReachabilityPreservers/LocalAverageCleaning.lean).

At half cutoff five, opposite-intersection pruning also gives unique
pairwise intersections. The half-five projection lemmas preserve the
condition under both splits of that family. Restricting to a quarter of
each support leaves room for the copies. The output has both original
budgets, at least \(M/392\) of the unrestricted indexed maximum, and all
four factor-four caps relative to its own averages. This uses the
averages in the statement of the cited cleaning lemma. The proof's
original-average version remains open at unrestricted half cutoff five.
[Half-five output-average cleaning](OnlineReachabilityPreservers/HalfFiveAverageCleaning.lean)
· [Cited Bridge Girth cleaning statement](https://arxiv.org/pdf/2212.11944v4#page=15).

Output-average cleaning at half cutoff five also works for the feasible
literal maximum over distinct nonempty paths. If every row of the indexed
witness has length at least two, half-two exclusion already makes the rows
distinct. Otherwise the output length cap below gives output mass at most
four times the output row count, so \(M\le1568p\). One spanning path or a
complete directed bipartite block of length-two paths supplies a distinct
witness with uniform degrees and lengths within both budgets. This retains
at least \(M/7056\) with all four caps relative to its own averages. The
same transfer applies at cutoff four in either mode and full cutoff six.
[Output-average caps for literal path sets](OnlineReachabilityPreservers/OutputAverageDistinctCleaning.lean).

The original-average conclusion at full cutoff six has a separate
proof. A reverse comparison within one width piece gives a conflict
when its opposite interval crosses two pieces. The conflict is at
the later endpoint of the split interval. Full exclusion
through three allows at most one incoming and one outgoing conflict
per incidence. After selecting an independent set, the retained pieces
satisfy the hypothesis of the contiguous full-six lift. In the mixed
case, a heavy incidence with an outgoing conflict to a light piece
either has no predecessor or has a heavy predecessor. Include the
former and delete their light targets. For the latter, include the
predecessors and remove their neighbors from the remaining heavy candidates. Selecting the heaviest light
pieces within the remaining path budget then retains at least \(13M/25\)
before vertex trimming and peeling. The other mass cases use the
same inequalities as for half cutoff four. The cleaned full-six witness
keeps at least \(M/5000\), both original budgets, and all four original caps.
[Opposite-cut conflicts](OnlineReachabilityPreservers/FrozenFullSixConflicts.lean)
· [Incidence selection](OnlineReachabilityPreservers/FrozenFullSixRepair.lean)
· [Full-six cleaning](OnlineReachabilityPreservers/FrozenFullSixCleaning.lean).

For half cutoff five, a forbidden five-bridge in the vertex-split family
projects its third and fifth corners to the same original vertex. The river
arrives before the second arc. With unique intersections,
the last two arcs cannot use that same pair of original vertices in opposite
directions. Uniqueness also rules out a repeated parent among the roles of
a bridge of size at most five after a path split. This gives a witness of mass at least \(M/16\) with both
budgets and all four original-average caps.
[Projection and cleaning with unique intersections](OnlineReachabilityPreservers/HalfFiveProjection.lean).

With repeated intersections, consecutive degree blocks order the two
copies of the shared corner. In a proposed half-five bridge the river's
copy precedes the second arc's copy. The third arc is a later reverse
partner of the fourth at this corner. The two incidences have different
colors, and the original degree at the corner exceeds the width. Keeping
one color on the overfull vertices prevents the new bridge. Bounding
degree excess and trimming the light copies gives an \(M/5000\) witness
after clipping at most \(7M/50\) incidences to the length cap.
[Degree repair](OnlineReachabilityPreservers/HalfFiveDegreeRepair.lean)
· [Length excess and vertex budget](OnlineReachabilityPreservers/HalfFiveCleaning.lean).

The unique-intersection lift through half cutoff five also applies to the
subfamilies obtained by pruning opposite intersections. The overlong
subfamily contains few rows, which reduces the path peeling charge.
It gives \(M/216\) when its original mass is at least \(2M/3\), and
\(M/2000\) when its mass is at least \(7M/12\) and its total excess at
the original length cap is at least \(7M/15\).
[Overlong path criteria](OnlineReachabilityPreservers/FrozenOverlongPaths.lean#L274).
If pruning all paths keeps at least \(13M/24\), the two-support trimming
bound gives \(M/288\). A nonempty row contributes a surviving last vertex,
and each removed incidence charges a distinct opposite link. These facts
give the same bound with at least \(M/12\) nonempty rows or at most
\(11M/24\) opposite links.
[Pruned family criteria](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L650).

An opposite comparison can cross a length cut in either the earlier or
the later parent, with the reverse comparison wholly inside a piece of
the other parent. At the shared corner the two participating piece
incidences have different reverse-partner colors. Deleting one color
covers these comparisons, and the disjoint-piece lift preserves half
exclusion through size five. Let \(E\) count distinct participating
piece incidences and \(U\) be the total degree excess above
\(\lfloor4M/n\rfloor\). Trimming the path pieces to the original budget
loses at most \(2M/31\) in the dense case, and deleting the smaller color
loses at most \(E/2\). During these path operations, no vertex gains
degree because pieces from one parent are disjoint.
When \(20E\le3M\), the degree repair finishes the cleaning. When
\(100U+50E\le43M\), clipping degrees suffices. Each branch retains
\(M/5000\) with both budgets and all four original caps. A mass guarantee
for the path repair outside these and the other checked conditions remains open.
[Crossed opposite comparisons](OnlineReachabilityPreservers/HalfFivePathRepair.lean)
· [Path budget and joint clipping criterion](OnlineReachabilityPreservers/HalfFivePathCleaning.lean).

The two repairs can use the same original reverse-partner colors. Mark
the union of the crossed path-cut incidences and all incidences at vertices
above the original degree width. Delete one color from that union. The
remaining pieces preserve half-five exclusion. If a vertex still has
degree above the width, its pieces all use the retained color at that
vertex. The degree split then preserves exclusion through five. With
union size at most \(4M/5\), one color keeps at least \(3M/5\)
before the exact row and vertex trims. Peeling gives \(M/5000\) within
both original budgets and all four original caps.
[Shared deletion and both trims](OnlineReachabilityPreservers/HalfFiveSharedWidthCleaning.lean).

The shared deletion works up to a union size of \(22M/25\) when the row
support is selected by its combined retained weight. Each incidence
outside the union contributes two and each inside contributes one. The
total weight is \(W=2M-A\), where \(A\) is the union size. A full row
piece has weight at least the original length width \(L\). Keep the
full pieces and the highest-weight remainders, so the omitted weight
\(Y\) satisfies \(4LpY\le W^2\). One color on the retained pieces
then has at least \(83M/160\) incidences. Choosing the row support before
the degree split preserves the same color repair and makes the vertex
trim depend on the retained mass. The result keeps \(M/5000\) and all
four original-average caps within both original budgets.
[Weighted row selection](OnlineReachabilityPreservers/HalfFiveWeightedWidthCleaning.lean).

When vertices above the original degree width carry at least 71 percent
of the mass, the actual copy count gives another half-five witness. Choose
the deletion color with fewer incidences at those vertices in the retained
row pieces and delete it throughout the shared marked union. The degree
split preserves each retained incidence and its row.
If those vertices had original mass \(S\), retained mass \(K\) in those
pieces, and the omitted row pieces had original mass \(Y\), then
\(S\le2K+Y\). With degree width \(D=\lfloor4M/n\rfloor\), the number \(Q\)
of allocated copies over those vertices satisfies \(DQ\le S+K+Y\).
The actual copy count and the row budget leave at least \(M/5000\) after
peeling, with both budgets and all four original-average caps.
[Cleaning by the overfull vertex mass](OnlineReachabilityPreservers/HalfFiveHeavyWidthCleaning.lean).

The half-five conflict graph can have two incoming conflicts at one
incidence. Take the paths
`[(4,1),(5,1),(0,3),(0,6,1,2,4,5),(3,2)]` in this order. They exclude
half-bridges at every size. Cutting into width-three pieces gives the
river \(0\to1\) on the early piece of the fourth path. Both chains
\(0\to3\to2\to4\to1\) and \(0\to3\to2\to5\to1\) become
forbidden half-five bridges. Their reverse comparisons target the same
incidence at vertex 1. This rules out an incoming-degree-one bound for
the arrival-oriented half-five conflict relation.
[Checked half-five incoming conflicts](OnlineReachabilityPreservers/VertexSplitAudit.lean).

Consecutive common vertices on two oppositely ordered paths define an
undirected link. If the family excludes full bridges through size three,
a simple cycle of \(r\) such links yields a full bridge of size at most
\(r\). A shortest reversible detour between two vertices of a row avoids
that row on every link. In such a detour each link owner occurs in one
consecutive run, which can be compressed to one step of the bridge.
Full exclusion at every size gives a forest. The pruning step charges
each removed incidence to a distinct link using half exclusion through
size two. It therefore loses at most \(n-1\) in the full-bridge-free case
for \(n>0\). At finite full cutoff \(k\ge3\), every cycle of links has
length greater than \(k\).
[Cycle-to-bridge proof](OnlineReachabilityPreservers/OppositeLinkForest.lean#L331)
· [Finite cutoff](OnlineReachabilityPreservers/OppositeLinkForest.lean#L410)
· [Charge in half mode](OnlineReachabilityPreservers/OppositeLinkForest.lean#L468)
· [Pruning loss](OnlineReachabilityPreservers/OppositeLinkForest.lean#L528).

For simple inputs at full cutoff six or half cutoff four, mass \(M\ge8E\)
at least both positive budgets gives a cleaned witness of mass at least
\(M/32\) at that cutoff, with both original budgets and all four frozen
caps. When \(M\le8\max(n,p)\), the proof uses the explicit low-mass
witnesses. At higher mass, pruning keeps at least \(7M/8\), and the
original widths expand each support by at most \(39/31\). Restriction
keeps at least \((31/39)^2\) of the pruned mass before removing low
incidences, which costs at most \(M/2\).
[Full cutoff six](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L136)
· [Half cutoff four](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean#L340).

An input excluding full bridges at every size already has \(E\le n-1\).
At higher mass this gives the required pruning bound automatically. The
size-six conclusion therefore holds at every mass at least both
positive budgets for such a simple input family.
[All-size input](OnlineReachabilityPreservers/ContiguousSixCleaning.lean#L151).

Using the actual rounded widths permits more loss at these cutoffs.
When \(M>8\max(n,p)\), each width times its original budget is at least
\(31M/8\). Separate quadratic bounds for the vertex and path blocks
let a family of sublists with unique intersections keep at least
\(M/288\) after peeling when its mass is at least \(13M/24\). The same
conclusion follows when opposite links number at most \(11M/24\).
The low-mass construction covers the remaining budgets. A second
sufficient condition allows deleting up to \(M/24\) while making all
remaining reversals cross a partition of the paths into two classes.
Both conclusions use the original four caps and budgets. They cover
cutoff four in both modes and cutoff six in full mode.
[Rounded capacities, repaired classes and pruning](OnlineReachabilityPreservers/FrozenMatchedPartners.lean#L514).

Clipping uses a separate count of ordered comparisons and preserves
the original row labels. In the indexed simple-path convention, half exclusion
through size two gives at most \(n(n-1)\) ordered comparisons across all
rows. At the original upper length cap \(L\), the coefficient \(4L-2\)
times the incidence loss is at most twice that count. For positive budgets
with \(p\le227\) or \(n(n-1)\le235p\), this bound and the low-mass construction give
\(M/104\) of the unrestricted maximum within both original budgets and
all four caps, at any full cutoff of at least two and half cutoffs two
through four. The general cyclic cases outside the checked hypotheses
remain open.
[Clipping at the original width](OnlineReachabilityPreservers/FrozenClippingBudgets.lean).

Degree clipping also keeps the original row and vertex labels. A common
vertex after the first one in the earlier row determines a later
reverse partner, which is unique under half exclusion through size
three. Counting these occurrences bounds the cost of clipping degrees
and lengths together. For positive budgets with either \(n\le157\) or
\(p\le156\), a cleaned witness retains \(M/104\) of the unrestricted maximum with the original
budgets and all four original-average caps at every full and half cutoff
of at least two. The dense branch at cutoff three or higher uses the two
rowwise clipping operations. The other branches use the low-mass
witness or the size-two construction.
[Clipping both dimensions](OnlineReachabilityPreservers/FrozenDegreeClipping.lean).

The length and degree counts also bound mass when the two budgets are
far apart. Cauchy--Schwarz gives \(M^2\le p(2n(n-1)+M)\) from the row
count at cutoff two and \(M^2\le n(p(p-1)+3M)\) from the vertex count at
cutoff three. The budget inequalities \(n(n-1)\le28p\) and
\(p(p-1)\le40n\), respectively, give \(M\le8p\) or \(M\le8n\).
The low-mass construction then retains at least \(M/8\), both original
budgets, and all four original-average caps. Its witness excludes full
bridges of every size. The result applies to the unrestricted maximum
in either mode with positive budgets.
[Squared-mass bounds and cleaning](OnlineReachabilityPreservers/FrozenUnbalancedBudgets.lean).

A rectangle with vertex set \(A\) and path set \(B\) in an unrestricted
maximizer of mass \(M\) has mass at most \(M/t\) whenever \(t>0\),
\(t|A|\le n\), and \(t|B|\le p\). Each bridge in a disjoint union stays
in one copy, where the arrival order is the original order. Padding
with unused vertices and empty paths fits the exact budgets. In
particular, at most \(M/4\) of the mass lies simultaneously on paths
above the original upper length cap and vertices above the original
upper degree cap. The bound holds in both modes at every cutoff.
[Extremal copy bounds](OnlineReachabilityPreservers/ExtremalCopyBounds.lean).

The vertex-budget condition extends in half mode when \(p\le n\).
The squared-degree estimate gives \(M\le12n\) if \(p(p-1)\le108n\)
and the input excludes half-bridges through size three. For
\(8n<M\le12n\), use disjoint square grids. Each point lies on one
horizontal path and on both directions of its column. Horizontal rows
arrive first. A chain with a vertical river stays in one column, where
the other direction goes the wrong way. A chain with a horizontal
river must end on a later vertical path. Thus the same witness
excludes half-bridges at every size. The side length is
\(\lceil M/(4p)\rceil\), and the number of disjoint grids is the smaller
of the counts allowed by the two budgets. The resulting witness
retains at least \(M/8\) and meets all four original-average caps.
[Degree-three grids](OnlineReachabilityPreservers/HalfGridCleaning.lean).

In a grid of any positive dimension, all but the last coordinate
have only forward rows. The two directions of the last coordinate
arrive after those rows. A chain whose river uses the last coordinate
has all other coordinates fixed and can only move in the opposite
direction. For any other river, the last arc must use the last
coordinate, because another arc in the river's direction on the same
line would repeat the river. Thus the grid excludes every half-bridge.
For \(D\) directions and width \(w\), one block has \(w^{D-1}\) vertices,
\(D w^{D-2}\) paths, and degree \(D\) at every vertex. Set
\(D=\max(2,\lceil M/(4n)\rceil)\) and \(w=\lceil M/(4p)\rceil\).
For positive budgets, \(2n\le M\), \(p\le M\), and room for one block
on each side, disjoint copies meet the four original-average caps
and retain at least \(M/8\).
[Arbitrary-dimensional grid witness](OnlineReachabilityPreservers/AxisGridCleaning.lean).

Every bridge of size \(r\) uses \(r\) distinct vertices and \(r\)
distinct path indices. Thus a full cutoff of at least \(\min(n,p)\)
already excludes every full bridge. The all-size cleaning theorem
then applies to the unrestricted maximum for positive budgets and
gives \(M/40\) with both original budgets and all four frozen caps.
The same finite-label witness format gives the \(M/16\) result through
cutoff three in both modes. With an empty budget or a cutoff below
two, the indexed maximum equals \(np\), and it already meets the
caps. An empty set of labels makes its corresponding cap vacuous.
[Finite-budget cases](OnlineReachabilityPreservers/FrozenBoundaryCases.lean).

The same splitting step can fail at larger bridge sizes with unique
intersections. On seven vertices, take the six paths `[(0,1,2,3), (3,4),
(4,0), (5,2), (1,6), (5,6)]`. There are 14 incidences, every vertex
has degree two, and the average path length is \(7/3\). The printed
deletion and vertex splitting stages leave this family unchanged. The
only path longer than the original average splits at its midpoint. The
new chain is \(5\to2\to3\to4\to0\to1\to6\) with river \((5,6)\),
and its last arc precedes the river. Lean checks that the original family
has unique intersections and excludes every bridge. The arbitrary-size
cleaning existence lemma for cyclic families needs a different argument.
[Checked half-7 example](OnlineReachabilityPreservers/UniqueSplitAudit.lean).

The factor-four block split from the frozen cleaning argument can also
create a full size-seven bridge before trimming and peeling in the dense
branch. Add 161 private vertices before the four-vertex path in the
example, and take the disjoint union with the side-40 layered lattice.
The ambient budgets are \(n=16{,}793{,}600{,}168\) and
\(p=4{,}096{,}000{,}006\). The incidence mass is
\(M=167{,}936{,}000{,}175>8\max(n,p)\), with one common vertex at most
for any pair of rows. Lean checks full exclusion at every size and
that opposite-intersection pruning keeps the entire input. The actual
block widths \(\lfloor 4M/n\rfloor=39\) and
\(\lfloor 4M/p\rfloor=163\) leave the cyclic part's vertex copies
together and create the same seven-bridge. This identifies a failure
of the block-splitting step on a dense input. The extremal cleaning
existence claim remains open.
[Checked dense block split](OnlineReachabilityPreservers/FrozenWidthSplitAudit.lean#L538).

Cuts between precedence components give another sufficient hypothesis
for cleaning cyclic paths. The precedence graph has an arc for each
strict comparison on an original path. Along a projected chain, the
component ranks are nondecreasing. When a parent occurs twice in
different pieces, the rank separation puts the first entrance before
the last exit in that parent. Shortcutting this section keeps the river
and the last arc's parent, so ordering the pieces by parent also
preserves the half-bridge arrival condition.

If each simple path contains at most \(\lfloor M/p\rfloor\) vertices
in any one component, whole visits pack into pieces of width
\(\lfloor4M/p\rfloor\) within four thirds of the path budget.
With positive budgets and \(M\) at least both budgets, the cleaned
family keeps at least \(M/16\) and satisfies both budgets and all four
original-average caps. Full exclusion is preserved at the input cutoff,
including exclusion at all sizes. Half exclusion additionally uses an
upper cap on all input degrees, a cutoff of at most four, or full
exclusion through two less than the half cutoff.

The same cuts work if each component visit fits the full upper length
cap \(L=\lfloor4M/p\rfloor\). Each pair of adjacent packed pieces has
combined length at least \(L+1\). Counting disjoint adjacent pairs
gives at most three halves of the path budget. When \(M\ge 2n\), the
degree split expands the vertex budget by at most \(9/7\).
Restriction and peeling then keep \(M/54\) with both original budgets
and all four caps. If \(M<2n\), the sparse construction suffices.
The bridge guarantees and the half degree-splitting conditions stay
the same.
[Component split and cleaning proofs](OnlineReachabilityPreservers/ComponentSplitCleaning.lean).

If visits longer than \(L\) contain at most \(M/56\) incidences, remove
each such visit as a whole. The test uses the original precedence
components. The new precedence graph only loses comparisons, so its
components subdivide the original ones. The retained mass is at least
\(55M/56\), and every remaining visit fits \(L\). In the dense case the
two support ratios give a rectangle with at least \(55M/108\) incidences
before peeling. Peeling at the original averages loses at most \(M/2\).
The resulting \(M/108\) guarantee includes both budgets and all four
original-average caps. Full exclusion survives at any finite cutoff or at
all sizes. Half exclusion uses the same three degree-splitting conditions.
The unrestricted cyclic existence question remains open.
[Removing long original visits](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1028)
· [Full exclusion at all sizes](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1105)
· [Half exclusion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1122).

At cutoff \(k\), ordered disjoint pieces of one path can be cut wherever
there is no return from a later piece to an earlier one in at most
\(\max(0,k-3)\) precedence edges. A repeated river parent must occur at
an interior arc, since a first or last arc shares a corner with the
river. A short return then starts or ends at the nearer corner of the
interior arc. When two arc parents recur in reverse piece order, the
return uses only the steps strictly between those arcs. Forward
repetitions can be shortened while keeping the river and last arc's
parents. This preserves half exclusion in parent arrival order.
[Full bridge criterion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1289)
· [Half bridge criterion](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1303).

If the precedence graph has no directed cycle of length at most
\(k-2\), all contiguous cuts meet this test. In the degree split, the
original river endpoints are distinct. A collision of projected detour
corners with one exterior arc would give a size-two bridge with the
river. Every remaining collision closes a walk of length at most
\(k-3\). Excluding those cycles alone preserves half exclusion in
the degree split with the original arc and river indices. The width-block construction gives
both budgets, the original four caps, and \(M/16\) in either bridge mode
on a simple family of mass at least both positive budgets. If rowwise
deletions of at most \(M/18\) incidences suffice to eliminate the short
cycles, it gives \(M/32\) under the same original caps. The support
restriction keeps at least \((9/16)(17/18)M=17M/32\), and peeling loses
at most \(M/2\). The existence of a suitable cleaning for every cyclic
input is still open.
[Half exclusion after a degree split](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1355)
· [Factor-four cleaning](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1552)
· [Cleaning after deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1600).

The width-cut criterion compares the quotients of original row positions
by the width \(\lfloor4M/p\rfloor\). The degree-copy projection preserves
those positions, so only pairs in different blocks need the bounded
return test. Full exclusion follows with this local premise. For half
exclusion the degree split also needs one of four conditions. These are
the absence of cycles through \(k-3\), a cutoff at most four, full exclusion
through \(k-2\), or degrees already within the upper cap. Short cycles
can remain if they create no bounded return across a cut. The same
retention and caps hold after rowwise deletions costing at most \(M/18\)
when the surviving rows satisfy the local condition at the original width.
[Degree-splitting conditions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1506)
· [Cleaning with the local return condition](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1537)
· [Local condition after deletions](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1579).

The cuts need not be equally spaced. A boundary in a row is safe if no
pair of vertices straddles it with a return of at most \(\max(0,k-3)\)
precedence edges. Consecutive vertices with the same last safe boundary
form a run. Pack these runs into pieces of the original upper width.
The rank uses the original positions even if longer runs are removed
first. The ordered-cut proof preserves the river and last arc's parent.
[Safe boundary](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1629)
· [Exact rank comparison](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1666)
· [Pruning bound](OnlineReachabilityPreservers/ComponentSplitCleaning.lean#L1802).

Splitting a vertex can also break the half exclusion, even with unique
intersections. In arrival order take the paths `(4,2), (0,2), (0,1), (1,2),
(2,3), (3,4)`. The only vertex above average degree is `2`. Its four
incidences split into two blocks of size two. Assign the earlier block to
copy `5` and the later block to copy `2`. The new chain is
\(0\to1\to2\to3\to4\to5\) with river \((0,5)\), and its last arc is earlier
than the river. In the original family the only alternate simple chain
for a river is \(0\to1\to2\), whose last arc is later than \((0,2)\).
Erasing repeated vertices after projecting the new chain therefore loses
the required last arc. Lean checks the original half exclusion at every
size and the half-6-bridge in the actual consecutive incidence blocks.
[Projection theorem](OnlineReachabilityPreservers/BridgeVertexProjection.lean)
· [Checked vertex split](OnlineReachabilityPreservers/VertexSplitAudit.lean).

Without unique intersections, two consecutive size-two blocks can already
create a half-5-bridge. In arrival order use `[(3,2),(0,2),(1,2),(2,3),(0,1)]`
on four vertices. The four incidences at vertex `2` split into the earlier
copy `2a` and the later copy `2b`. The half-bridge is the chain
\(0\to1\to2b\to3\to2a\) and river \((0,2a)\). The original family
excludes every half-bridge. This sets the limit for arbitrary simple paths
of the checked vertex-split preservation through cutoff four.
[Size-five vertex split](OnlineReachabilityPreservers/VertexSplitAudit.lean).

## A common vertex partition preserves the bridge exclusions

Restrict every path to each part of a fixed partition of the vertices.
Every arc step stays in one part. In a bridge, adjacent arcs share a corner
and the river starts at the first corner, so all its pieces use that part.
Within one part, the pieces have distinct parents and retain their parents'
arrival order. The projection gives a bridge with the same size and, for a
half-bridge, the same earlier-last-arc relation. The partition preserves
both the total mass and each vertex degree.

The resulting path count must fit the budget. With positive budgets \(n,p\)
and original mass \(M\ge\max(n,p)\), let \(L=\lfloor4M/p\rfloor>0\).
A subfamily of \(r\) paths
can use a partition into parts of size at most \(L\) when
\(r\lceil n/L\rceil\le p\). Truncating every original path to length \(L\)
is another way to cap lengths without creating bridges. Either method gives
a cleaned witness with both original budgets, all four original-average caps,
and at least \(M/16\) incidences when the capped subsystem retains at least
\(3M/4\). If degrees still exceed the upper cap, the proof needs a vertex
split. This step preserves full exclusion at every cutoff and half exclusion
through cutoff four. With degrees already capped, peeling alone works at any
cutoff. A general guarantee of a suitable length-capped subsystem remains open.
[Partition and budget proofs](OnlineReachabilityPreservers/VertexPartitionCleaning.lean)
· [Truncation and frozen caps](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).

## The cited consecutive-edge overlay can admit an alternate path

The paths `[(0,1,2,3), (3,0), (2,1)]` have no bridge of any size. Their endpoint
demands are \((0,3),(3,0),(2,1)\), and their consecutive edges consist of
the four-cycle \(0\to1\to2\to3\to0\) and the chord \(2\to1\). The cycle
alone preserves all three demands. In particular, the original chord and
the route \(2\to3\to0\to1\) give two distinct simple paths for the last
demand. This falsifies the inference of uniqueness from bridge-freeness
alone. Corollary 42 of [8] invokes Theorem 37, so the cited proof of its
comparison with the acyclic extremum inherits the gap from Lemma 40.
The same uniqueness inference appears in Lemma 18 of arXiv v1 and in
Lemma 40 of v2 through v4. The corresponding v1 comparison is Corollary 20,
which invokes Theorem 15.
[Checked counterexample](OnlineReachabilityPreservers/SplitAudit.lean)
· [Bridge Girth v1, Lemma 18](https://arxiv.org/pdf/2212.11944v1#page=18)
· [Bridge Girth v4, Lemma 40](https://arxiv.org/pdf/2212.11944v4#page=35).

The upper direction of Lemma 14 holds on arbitrary digraphs. For positive
vertex and demand counts, let \(M\) be the fully bridge-free maximum mass
under the indexed simple-path multiset convention of [8]. The actual
offline preserver satisfies \(|E(H)|+p\le M+2n\), hence \(|E(H)|\le3M\).
The compression of the pruned condensation has exactly \(p\) rows. Their
incidence count is the number of retained quotient arcs plus \(p\). Each bridge
uses distinct rows, so excluding bridges through size \(p\) already
excludes every size. An empty demand list gives the empty preserver.
[Checked general upper bound](OnlineReachabilityPreservers/OfflineBridgeExtremalUpper.lean#L56).

The extremal converse holds by a vertex elimination argument. Restrict
the paths to the vertices that remain. A longest simple consecutive
chain with distinct row labels ends at a vertex that can leave on at
most two rows. Two unused rows would give a bridge using their heads
and the chain between them. Two used rows other than the last would
give a bridge using the corresponding earlier steps on the chain. An
unused row and a used row before the last also give a bridge, by
comparing the unused row's head with the used step.
Assign the chosen vertex the largest remaining number and discard its
incidence in each row that still has a successor. Each vertex loses at
most two incidences, and the retained subsequences increase in one
order. Each nonempty row keeps its last vertex. For maximum mass
\(M\ge6n\), at least \(M/2\) survives. For smaller mass, the spanning path
gives a linear lower bound. Together these give a DAG on exactly
\(n\ge2\) vertices with exactly \(p\le n^2\) distinct demands whose every
preserver has at least \(M/24\) edges.
[Consecutive-chain bound](OnlineReachabilityPreservers/OfflineConsecutiveEndpoint.lean#L197)
· [Common-order subsequences](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L209)
· [Checked extremal converse](OnlineReachabilityPreservers/OfflineBridgeConverse.lean#L315).

With a common vertex order, a detour that uses the same path twice can be
shortened to one step along that path. A detour with distinct path indices
gives a bridge. The acyclic overlay therefore forces every consecutive arc.
[Checked acyclic construction](OnlineReachabilityPreservers/AcyclicOverlay.lean).

The seven-vertex family also gives an alternate overlay route under unique
intersections. Its last demand survives deletion of \((5,6)\) by using
both ends of the long path.
[Checked unique-intersection example](OnlineReachabilityPreservers/UniqueSplitAudit.lean).

The cited overlay construction can also lose an arbitrarily large factor.
For any integer \(C\ge1\), Lean constructs a fully bridge-free simple path
family whose consecutive overlay has a preserver with
\(C|E(H)|+p<\lVert S\rVert\) for the \(p\) distinct endpoint demands.
The base paths advance by a slope and its square in two coordinates. A
bridge would have zero weighted variance in its slopes. Its first arc
and river would then share a slope and their source vertex, specifying
the same path. Private vertices and two return paths close each base path
into a directed cycle. A return path as river has no alternate first
edge. A chain for a base river that uses a return would use the same base
path twice. The two SCC connector forests
therefore serve all the overlay demands using only a linear number of
edges.
[Checked unbounded gap in the cited overlay](OnlineReachabilityPreservers/OverlayLowerAudit.lean)
· [Checked bridge exclusion for the added return paths](OnlineReachabilityPreservers/CyclicReturnOverlay.lean).

For the common-order extremum, Lean checks a lower bound at the original
sizes with exactly \(p\) distinct demands for \(n\ge2\)
and \(p\le n^2\). A bipartite graph supplies a separate bound linear in
\(p\) when the consecutive overlay's path-count subtraction is substantial.
[Exact distinct-demand lower bounds](OnlineReachabilityPreservers/OfflineDemandLower.lean).

The same lower construction applies if each original path can be cut into
at most \(b\) increasing blocks in one common vertex order. Keep one
longest block per path. Each kept block is a subsequence of its own
original path, so every bridge in the kept family lifts to a bridge in
the original family. At least \(M/b\) incidences survive, and the acyclic
lower construction gives a graph on the original vertices with exactly
\(p\) distinct requests forcing at least \(M/(12b)\) edges. One common
numbering with at most one descent per path gives factor 24. For two
full-length reversed paths, each of their \(n-1\) adjacent pairs gives
a descent in exactly one path, under every numbering. These two paths
exclude all full bridges and already attain the maximum mass \(2n\),
so a bounded number of blocks in the original family cannot be assumed.
Pruning opposite intersections first leaves at least half the mass and
gives factor 48 when the pruned paths have such a one-descent numbering.
[Ordered-block lower bound](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean)
· [Fully bridge-free reversed paths](OnlineReachabilityPreservers/OppositePruningGain.lean).

The number of blocks can grow without bound even after opposite-intersection
pruning. For every positive dimension \(d\), index the paths by the
\(3^d\) ternary words. At each coordinate, the three words that agree off
that coordinate use the steps of a directed triangle. Every path visits
the coordinates in order and uses two adjacent vertices in each one.
A bridge within one coordinate would need the river's first step.
A bridge reaching a higher coordinate would need to leave its first
coordinate in the river's row to recover that coordinate's original label.
These facts exclude all full bridges. Distinct rows meet at most once, so
pruning keeps every path in any arrival order.

In any common numbering, every coordinate triangle has a descending step.
Some path has at least \(\lceil d/3\rceil\) descending steps and hence
needs at least \(1+\lceil d/3\rceil\) increasing blocks. At \(d=4\),
no common numbering gives all 81 paths at most two blocks on the 324
vertices. The mass is \(2n\), so the spanning-path lower construction
already gives a constant-factor comparison for this family.
[Unbounded block requirement](OnlineReachabilityPreservers/TriangularCoordinatePaths.lean#L485).

A common order also suffices when each row keeps any nonempty increasing
subsequence, with a bound on total retained mass across all rows. For a
concrete choice, form the precedence graph with an arc for each strict
comparison on any input path. Keep one vertex on each path for each
strongly connected component it visits. A topological order of the
condensation orders all kept rows. If each path meets each component
in at most \(b\) vertices, this again forces at least \(M/(12b)\) edges at
the original counts. The more general proof uses the total number of
path-component incidences. Selecting one vertex per visit can retain an
arbitrarily small fraction of the mass. For every \(L\), a family of three
fully bridge-free paths has mass \(3L+7\) and just three visits. Pruning
opposite intersections retains all three paths as given.
[Increasing subsequences](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L69)
· [Component visits](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L184)
· [Bounded component intersections](OnlineReachabilityPreservers/OfflineOrderedBlocks.lean#L261)
· [Unbounded loss of selecting one vertex per visit](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L445).

Write \(J\) for the total number of path-component visits. The visit
construction yields a DAG forcing \(J\le 12|E(H)|\). When
\(J\ge 12(n-1)\), that graph also forces \(n-1\le |E(H)|\). Otherwise
the spanning-path construction forces both bounds. For \(n\ge 2\) and
\(1\le p\le n^2\), every preserver of the selected graph's \(p\) distinct
demands therefore satisfies \(n+J\le 14|E(H)|\). This gives the conditional
converse \(M\le 14C|E(H)|\) when \(M\le C(n+J)\). It also applies when each
component's mass is at most \(C\) times its vertex count plus its count of
visiting paths. When the component condition is verified on the
opposite-pruned system, the original mass is bounded by \(28C|E(H)|\).
[Aggregate bound](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L240)
· [Component-wise bound](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L270)
· [Bound after pruning](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L308).

The component condition can fail by an arbitrarily large factor even after
pruning. Take a lattice family with \(q=L^6\) original paths and add the
private return paths. The expanded system has \(n\le 11q\), \(p=3q\),
\(J=3q\), and \(M=(L+7)q\). Each path lies within one component and distinct
paths meet at most once, so pruning retains all incidences. The example
limits the component condition for a supplied family.
[Checked aggregate obstruction](OnlineReachabilityPreservers/OverlayLowerAudit.lean#L509).

Order and select the subsequences independently inside each component.
All comparisons across components follow the condensation order. If the
chosen local subsequences retain at least \(M/L\) of the original mass across
components, the resulting DAG forces at least \(M/(12L)\) edges at the
original budgets. Rows with no chosen vertex contribute a singleton.
Restriction to one component preserves its internal reachability and the
full bridge exclusion. A uniform retention bound for those component
subproblems would give the same bound for the whole family.
[Combining the local selections](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L56)
· [Internal reachability](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L152)
· [Component reduction](OnlineReachabilityPreservers/OfflineComponentOrders.lean#L208).

The base lattice paths alone also give a superlinear offline lower bound
when the vertex and demand counts are comparable. Ordering vertices by
layer and then lexicographically makes the path system acyclic. Its
consecutive overlay on \(4(L+1)L^5\) vertices forces \(L^7\) edges for
\(L^6\) distinct feasible demands, for every integer \(L\ge1\). Lean can fill
any unused demand slots with other reachable pairs while retaining all
original reachability requirements.
[Checked finite lattice lower bound](OnlineReachabilityPreservers/OverlayLowerAudit.lean).

For simple path systems with no full bridges through size four, Theorem 43
bounds their mass by \(B K n\) when \(p^2\le K n\) and by \(B K p\) when
\(n^2\le Kp\), with one absolute constant \(B\). A spanning directed path
forces \(n-1\) edges in the first regime, and a bipartite DAG forces at
least \(p/6\) edges in the second. Extra distinct demands fill the demand
set to exactly \(p\). Together these prove the extremal converse in both
linear regimes, allowing cyclic path systems.
[Checked converse in two demand regimes](OnlineReachabilityPreservers/OfflineConverseRegimes.lean).

The same three paths in their listed order also give an alternate route in
the final reveal round of the ordered construction of [8] Lemma 45.
Theorem 3's checked lattice proof forces each route directly from the
available slopes. [Checked insertion lower bound](OnlineReachabilityPreservers/StrongAdversary.lean).

## Persistent virtual terminals can connect different trees

The conference version of [24] states a deterministic early algorithm.
Its Section 2.1.3 adds a super source and sink for each group demand
before invoking ordinary online Steiner forest. Keeping these free
attachments across rounds can make a later pair connected by a route
that leaves its tree through earlier virtual terminals.

Lean checks a two-tree example with roots `12` and `13` and all group
representatives at leaves. The paid edges serve the first groups `{0,2}`
and `{1,3}` through the tree rooted at `13`. The second request has
endpoints `4` and `5` and needs the unpaid arc from `14` to `10` in the
tree rooted at `12`. Both root-side attachments are present there.
Earlier virtual terminals give a detour from `0` through the other
tree to `1`. The claim that ordinary connectivity recovers a
group solution under persistent attachments is false. A separate argument
is needed for the deterministic competitive guarantee. The full arXiv
version states a randomized result and uses group Steiner forest with
flows that stay in a single root copy.
[Checked example](OnlineReachabilityPreservers/SteinerGroupAudit.lean)
· [Conference paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2021.5)
· [Full arXiv version](https://arxiv.org/pdf/2103.04543v3).

## The early cutoff and the random seed

Section 5.1 defines a nontrivial request using reachability in the
current preserver. Section 5.2 also describes a cutoff after the first
\(T\) demand pairs. If early arrivals are filtered by the randomized
preserver, the resulting early input can depend on the same coins
used to estimate its expected cost. A bound on fixed demand sequences
does not by itself cover this filtering.

The checked algorithm counts distinct non-self requests in arrival
order and gives the first \(T\) to the early routine. The trace is
fixed before the random samples. If the late phase starts, Lemma 20
still gives \(T\le |Z|^2\) for every feasible offline solution \(Z\).
Earlier feasible requests, repetitions, and self-requests all
remain served. The expected rate and per-realization prefix
guarantees are checked for this construction.
[Complete construction](OnlineReachabilityPreservers/SteinerComplete.lean).

## The source in Lemma 35 can follow a directed cycle

Take the base path `(0,1)` and the paths `(1,2)` and `(2,0)`. With
the fixed vertex `2` and window length one, `1` is a near predecessor
and `0` is a successor. Both vertices remain in the induced base path,
whose source is `0`. The system has unique intersections and no bridges
of any size. A directed 3-cycle invalidates the step asserting that every
induced base path starts in the near-predecessor set.

After pruning to unique intersections, every close-pair charge with its
right endpoint on the base has its left start earlier on that base. This
permits counting only tuples whose right endpoint lies after a near
predecessor. Lean checks that the suffix from the earliest near predecessor
contains all of these endpoints and induces a family with a source in the
predecessor set on each path. The source-restricted estimate bounds those
incidences. The other on-base endpoints precede a near predecessor on their
base. Charge collisions of these endpoints to the earlier base and the
last near predecessor on the later base. Two distinct collisions with the
same charge would form a half-3-bridge or a half-4-bridge through the fixed
vertex. Both groups have the same incidence bound, giving the paper's
expectation for all on-base tuples. In Appendix B, all close-pair charges
have both endpoints off the base. The filtered offline count gives the
local-order upper bound and recurrence of Theorem 43.
[Checked cycle](OnlineReachabilityPreservers/SplitAudit.lean)
· [Checked close-pair charges](OnlineReachabilityPreservers/LocalBranching.lean)
· [Checked source restriction and upper count](OnlineReachabilityPreservers/LocalOnBaseCounting.lean)
· [Backward collision count](OnlineReachabilityPreservers/LocalFullOnBaseCounting.lean)
· [Full expectation](OnlineReachabilityPreservers/LocalOnlineAverage.lean)
· [Unrestricted offline bound](OnlineReachabilityPreservers/LocalOfflineBound.lean).

## Matters requiring proof or clarification

- Lemma 13's pigeonhole step can pick two paths whose only intersection with
  the earlier path is their common terminal. The reverse-arrival degree in
  Lemma 12 also counts the path just inserted. An incidence proof restricted
  to new-edge tails avoids the terminal configuration. It gives the restricted
  edge bound and, for distinct requests with average degree at least two,
  gives Lemma 13 with constant 24.
  [Checked reverse-arrival selection and incidence estimate](OnlineReachabilityPreservers/RestrictedIncidence.lean).
- Lemmas 23 and 39 use splitting steps, which increase vertex or path count
  before any additional restriction. The displayed proof does not establish
  its exact output budgets or show that the lower caps survive a restriction
  to those budgets.
  In a common vertex order and with incidence mass at least both original
  counts, restricting the expanded system in each coordinate preserves at
  least nine sixteenths of the mass. Pruning then preserves at least one
  sixteenth of the original mass and gives both upper and lower caps.
  Lean verifies both original budgets and the two bridge conditions at every
  size in this common-order setting. A spanning path and singleton padding
  make both density assumptions automatic at a common-order maximum with
  positive budgets. The same caps hold through size four
  under unique intersections in local orders, and at every cutoff up to size
  three for arbitrary simple paths. In the latter case the general ordered-list
  maximum is finite, with both density assumptions following from the
  common-order witness.
  For simple paths excluding half-bridges through size four and with mass
  at least twice both counts, opposite-intersection pruning and cleaning
  keep one thirty-second of the mass within both original budgets. The
  lower caps are one eighth of the original averages and the upper caps
  are four times those averages. Half exclusion survives, and full
  exclusion survives when present in the original family.
  [Common-order extremum](OnlineReachabilityPreservers/CommonOrderExtremal.lean)
  · [Unrestricted extremum through size three](OnlineReachabilityPreservers/LocalOrderExtremal.lean)
  · [Checked local cleaning](OnlineReachabilityPreservers/LocalBalancedRegularization.lean).
- At cutoff four, the existential bounds relative to the witness's own
  averages hold for the unrestricted maximum in either bridge mode. In the
  dense case, removing opposite intersections and restricting each support
  to at most a quarter of its original budget leaves room for both splits.
  Pruning then puts every degree
  and path length between one quarter of its splitting width and that width,
  so each lies within a factor of four of its output average. For small
  budgets or low mass after restriction, a spanning path or singleton
  paths supply the witness. Both budgets hold and the output mass is
  between \(M/392\) and \(M\).
  [Checked output-average bounds](OnlineReachabilityPreservers/LocalAverageCleaning.lean).
- For full bridge cutoffs from three through five, opposite shared intervals
  decompose into chains of adjacent shared vertices. Reversing a shared
  interval pairs each chain link with its counterpart on the other path.
  After splitting vertices, place width cuts between chain positions and mirror
  every cut at its counterpart. Path pieces retain their original relative
  orders. This at most doubles the number of cuts. In a bridge of size at most five,
  every two slots around the river and arcs are adjacent or have one slot
  between them. The mirrored cuts preserve full exclusion up to that size.
  In the dense case, restricting both budgets retains at least \(121M/238\)
  incidences before peeling. Peeling at the original
  one-quarter averages loses at most \(M/2\). Disjoint paths or singleton
  paths cover the sparse case. The final witness retains at least \(M/119\)
  and meets all four original-average caps.
  [Checked full-bridge cleaning](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).
- For simple paths that exclude half-bridges through a cutoff of at least
  two, the consecutive edges inject into the off-diagonal vertex pairs.
  This bounds the incidence mass by the number of such pairs plus the
  number of paths. If the mass is between the larger budget and eight times
  it, a sparse family, paired paths, or directed bipartite blocks meet both
  original budgets and all four original-average caps. The paired paths
  have opposite orders in each disjoint vertex block. The bipartite blocks
  have paths of length two and all edges point from one side to the other.
  Each witness excludes every full bridge and retains at least one eighth
  of the original mass. This includes every unrestricted maximum in either
  mode when either positive budget is at most eight. The unrestricted
  cyclic statements at higher half cutoffs and the remaining finite
  full cutoffs stay open.
  [Checked low-mass construction](OnlineReachabilityPreservers/LocalFrozenLowMass.lean).
- The opposite-intersection condition alone can fail at size six. One example
  has unique intersections and excludes every full bridge before splitting.
  Two disjoint pieces of one path create a size-six bridge. In half mode,
  the chains used to pair cuts can branch even when every half-bridge is
  excluded. These examples identify the limits of the splitting proof.
  [Checked splitting examples](OnlineReachabilityPreservers/CyclicSplitLimits.lean).
- The proof of Lemma 23 writes \(\beta\) for the half-bridge-free extremum
  \(H\). The statement of Lemma 39 writes \(H\) for the full-bridge-free
  extremum \(\beta\) it is used to estimate.
- In Lemma 24, the paths `(0,1,2)` and `(2,1,0)` share three vertices without
  a bridge. Lean proves the ordering and fiber bound for arbitrary simple paths
  by choosing one witness for each middle path and using the 2-bridge exclusion
  to rule out repeated corners in the proposed 4-bridge. Full bridge-freeness
  gives strict order at the right. The paths `[(0), (2,1), (0,1,2)]` have
  one middle path and two witnesses for the same outer paths. For Lemma 26,
  Lean prunes opposite intersections before counting distinct triples. The
  pruned system retains at least half the original mass, its witnesses are
  unique, and every counted triple occurs in the original system. This yields
  the unrestricted initial bound of Lemma 27. The common vertex order of
  growth paths gives uniqueness directly.
  [General fiber and example](OnlineReachabilityPreservers/CyclicIntersections.lean)
  · [General chain count and initial bound](OnlineReachabilityPreservers/GeneralInitial.lean).
- Lemma 28 writes a difference of a right-hand intersection position with
  itself in the definition of close pairs. Its collision argument instead
  bounds the difference between the two right-hand intersection positions.
  The [finite branching count](OnlineReachabilityPreservers/ClosePairs.lean)
  uses this corrected condition, including a zero right displacement, and
  preserves the identity of each branching segment through its start vertex.
  The definition follows the detailed Appendix A.3 sampling. All paths
  meeting the base can branch. The overview in Section 3.3 describes only
  paths earlier than the base, which is a different restriction.
- Appendix B's branching-degree assertion applies off the base path for the
  \(Q\) count. Using the convention that a branching segment contains its
  start, several segments can share that start on the base. The proof shows
  both vertices of each \(Q\) tuple are off the base under full bridge-freeness
  and a common vertex order.
- Lemma 34's first two moment displays omit the \(+d\) in the linear
  contribution \(n_x(\ell+d)\) from Lemma 31. The inequality before the
  case analysis restores it. The sampled moment estimate retains both terms.
- Lemma 35 describes the number of tuples charged to each important
  incidence as \(\Theta(xd)\). The count uses an upper bound because the
  qualifying middle path and order conditions can remove choices.
  In a common vertex order the induced family has its own source-restricted
  incidence proof. The cyclic case needs the restrictions above.
- Lemmas 40–42 print a free exponent \(a\) on the first power of \(p\). The
  integrand and the starting/target bounds use \(p^{1/2}\). The recurrence
  uses \(2/3\le b<1/\sqrt2\). This is within the range where the integral
  estimates use sublinear powers of \(p\).
- Theorem 18 displays \(T^{1/2-\varepsilon}\), while Theorem 7 and the
  subsequent use in Sections 5.1–5.2 use \(T^{1/2+\varepsilon}\).
  The [cited online buy-at-bulk paper](https://arxiv.org/abs/1509.03212)
  gives the latter exponent with polylogarithmic factors in the graph size.
  The replacement unit-cost rule attains
  \(K(1+\log n)^{h+4}T^{1/2+\varepsilon}\,\mathrm{OPT}\) in expectation on
  each fixed feasible prefix of distinct non-self demands. The template height
  \(h\) and constant \(K\) depend only on \(\varepsilon>0\). The bound includes
  the empty prefix. The Steiner application can absorb the graph polylogarithm
  into its final exponent slack.
  [Checked demand-dependent bound](OnlineReachabilityPreservers/SteinerCompetitive.lean).
- Lemma 2.12 in the full version of [24] prints both height-reduction
  cost inequalities in the direction opposite to the bounds used by its
  Theorem 2.5. The comparison used there bounds the auxiliary optimum by
  the original optimum times the height-reduction factor, and bounds the
  cost of expanding a purchased auxiliary tree by its auxiliary cost.
  Lemma 5.2 of the cited source already prints the first inequality in
  reverse, and its Appendix A proves the direction needed by the reduction.
  It prints the expansion inequality in the needed direction.
  [Grigorescu–Lin–Quanrud, full version](https://arxiv.org/pdf/2103.04543v3#page=15)
  · [Height-reduction source](https://par.nsf.gov/servlets/purl/10210282#page=13).
- Theorem 1's table has a different pairwise rounded presentation
  (\(0.73,0.54\)) than its theorem and abstract (\(0.72,0.56\)).
  The sharper expression has its first two exponents related by
  \(a\mapsto (a,2-2a)\). For \(p\ge\sqrt n\) that term decreases as
  \(a\) increases. Near and below \(\sqrt n\), use a small-demand bound
  to justify uniform rounding. Rounding alone does not absorb arbitrary
  \(n^{o(1)}\) loss when \(p\) is of order \(\sqrt n\).
  At the dense end, \(p\) of order \(n^2/\log n\) also leaves no fixed
  power of \(n\) to absorb the loss. The graph cap \(n^2\) alone does not
  bridge the gap between this sharp asymptotic statement and the rounded bound.
  The no-log acyclic estimate gives the rounded graph bound after two
  iterations with \((a,b)=(62/85,1006/1437)\).
  The limiting bound keeps a fixed small-demand coefficient and chooses a
  vertex-count-dependent slack from the finite iteration bounds.
  [Checked online bounds](OnlineReachabilityPreservers/OnlineSharp.lean).
- The pairwise instantiation of Algorithm 3 checks the number of pairs and
  the edge count after the expensive phase and searches for the smallest
  certified integer quota up to the number of condensation arcs. Every proven
  upper bound on the adaptive prefix certifies a quota. The dyadic proof uses
  the smaller of the initial and sharp rate envelopes to keep the first
  quota linear even with vertex-count-dependent slack.
  [Checked pairwise assignments](OnlineReachabilityPreservers/PairwiseNonAdaptive.lean).
- The hit phase draws with replacement and then deduplicates the sampled
  vertices. For a demand \((s,t)\), it uses the vertices reachable from
  \(s\) that can reach \(t\). This region contains every vertex on a simple
  \(s\)-to-\(t\) path. In a cyclic graph two hub legs can concatenate to a
  walk. Their original edges still certify the required reachability.
  [Checked sampling and routing](OnlineReachabilityPreservers/SteinerHubs.lean).
- The phase composition skips a hit when the hub phase already serves it.
  The hub charge therefore uses the hub trace itself. In the generic phase
  assembly, the early routine can affect which misses arrive after a positive
  cutoff. The thin thresholds are independent of this trace. For Theorems 8
  and 21, the complete evaluator splits the fixed distinct non-self trace
  before sampling and runs the late assembly with cutoff zero. The thin trace
  then depends only on those arrivals and the hubs, independently of the early
  seeds and thin thresholds. A missed thick pair triggers a full-graph
  purchase charged to the bad hub event.
  [Checked phase composition](OnlineReachabilityPreservers/SteinerAssembly.lean)
  · [Complete evaluator](OnlineReachabilityPreservers/SteinerComplete.lean).
- The [second-moment estimate](OnlineReachabilityPreservers/SecondMoment.lean)
  of Appendix A is checked for a common vertex order under the inductive
  subfamily bound. The [finite online iteration](OnlineReachabilityPreservers/OnlineBound.lean)
  uses the acyclic expectation estimates and handles the window exceptions.
  The intermediate discrepancies concern the printed arguments and formulas.
