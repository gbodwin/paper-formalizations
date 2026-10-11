# Positive shared-copy lifting theorem

This component constructs actual unweighted graphs outside the previous
perfect-path outer interface. Shared outer edges and nonunique inner shortest
paths are allowed. The input graph may be disconnected, and repeated port
labels and empty parameter domains are handled literally.

For an n-vertex input F and a terminal set S of size s, suppose every subgraph
preserving the actual S-by-S native distances keeps at least m edges. For
every natural r, `SharedCopyLift.subset_lift` constructs a graph with

    vertices = r^2 n + 2 r s,
    terminals = 2 r s,
    every preserving subgraph has at least r^2 m edges.

The theorem's input lower-bound hypothesis is explicit; the output graph,
terminal set, metric argument and copy-wise edge accounting are all proved.
It is a transformation theorem, not an unconditional new asymptotic bound.
For positive r,s the forced-edge/terminal-square ratio supplied by this
statement is m/(4s^2), so this result alone does not amplify normalized gain.
The original stronger square-root-log-deficit unweighted existential remains
open. A metric-safe construction whose critical routes traverse several
copies is still needed for the proposed amplification route.

## Construction and proof

The more general construction has left terminals A-by-B, copies of F indexed
by B-by-C, and right terminals C-by-D. The input port maps are A-to-V(F) and
D-to-V(F). A left terminal (a,b) connects to the a-port in every (b,c) copy;
a right terminal (c,d) connects to the d-port in every (b,c) copy.

Contracting connectors projects any output walk to a genuine input walk,
with exact projected length plus connector count equal to original length.
The coarse left/middle/right coordinate forces at least two connectors.
Thus the cross-terminal extended distance equals the input distance plus two,
including infinity for unreachable pairs. A shortest preserved cross route
uses exactly two connectors and therefore remains in the copy (b,c) selected
by the two endpoint indices. Its actual inner edges form a native-distance
preserver inside that copy. A disjoint injection of all copies' darts into
the output darts adds the genuine edge lower bounds.

No unique shortest-path, layeredness, connectedness, outer edge ownership,
or supplied output witness is assumed. This is why the component can serve
as a starting point for constructions using shared outer incidence.

## Verification boundary

Source SHA-256: effefd0f0bf8e03bab28170c79cb297cd19ee103b910e8f07e3f94c08d178941.
All 115 parent mathematical modules at 66127d51 are byte-unchanged.
Strict warning-as-error source compilation, all 95 defining-module
declaration axiom checks, and an independent official module kernel replay
passed. The full 116-module DP root audit checks all 2,074 declarations,
and all four repository paper indexes pass. The separate exact-source [semantic review](shared-copy-lift-source-review.json)
passed. Only propext, Classical.choice and Quot.sound were used.

The frozen end-to-end audit at 40db5842 remains a qualified corrected/partial
PASS and is not extended by this component. Exact successor CI is pending at
publication; its terminal receipt is recorded separately after completion.
