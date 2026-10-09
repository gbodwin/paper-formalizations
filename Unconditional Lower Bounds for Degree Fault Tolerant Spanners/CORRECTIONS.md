# Source correction and formalization conventions

Source: Greg Bodwin and Aleksey Lopez, *Unconditional Lower Bounds for Degree
Fault Tolerant Spanners*, [arXiv:2607.07576v1](https://arxiv.org/abs/2607.07576v1).
The pinned PDF has SHA-256
`cbf9a322032cd3c672b663ef8547e74a76435ce6df81ab0c3ad77e70d66f8699`.
The original published PDF is unchanged.

## 8 October 2026: the incidence construction needs k >= 2

Section 2.1 permits k >= 1. [Lemma 6, printed page 4](https://arxiv.org/pdf/2607.07576v1#page=5)
then claims that its graph has 2n vertices and n^(1+1/k) edges, where n=p^k.
Lines are defined as actual subsets of the point space, rather than labelled
copies indexed by a slope parameter.

At k=1, every slope vector is (1). For every x in F_p, the set
{x + lambda : lambda in F_p} is all of F_p. Thus all choices of x and t define
the same line. The incidence graph is K_(p,1), with p+1 vertices and p edges,
whereas Lemma 6 claims 2p vertices and p^2 edges. For example p=2 gives three
vertices and two edges, rather than four vertices and four edges. The counting
argument identifies only the p choices of basepoint and overlooks the additional
p identical slope labels. The density statement of Lemma 16 inherits this issue.
This boundary error was independently checked and reported to Greg on 8 October.

The corrected construction and its counting claims assume k >= 2. In the Lean
representation, dimension is d+2, and injectivity of canonical line records into
actual point subsets is proved. No duplicate labelled lines are silently counted
as distinct subsets.

The main lower bound remains true at k=1. Use K_N separately. The empty fault
set is admissible for every fault budget. A stretch-one spanning edge-subgraph
must retain every input edge, since the endpoints of a missing edge have no
replacement walk of length at most one. Hence every such spanner has exactly
N choose 2 edges, and N^2 <= 4*(N choose 2) for N>=2.
`complete_one_spanner_edge_count`, `complete_graph_quadratic_lower_bound`, and
`all_sizes_k_one_case` implement this repair. It applies to every fault budget,
including the full final domain 1<=f<=N.

The companion website edition should restrict the Section 2.1 construction and
Lemmas 6/16 to k>=2, add this separate k=1 proof, and retain this dated changelog.
This is an editorial correction to the website edition, not an alteration of the
published PDF.

## Explicit conventions and extensions

The following clarify the formal statement; they are not additional confirmed
errors in the paper's main theorem.

- The all-size theorem uses N>=2, k>=1, and 1<=f<=N. Its positive constant
  c_k=1/2^(k+3) is chosen before N and f. Nearby primes, isolated padding, and
  the dense regime are proved internally. The exact prime family retains its
  stronger constant 1/4. No all-N interpolation is assumed.
- Lemma 9 is used in its point-rooted alternating-walk form. The broad wording
  for walks rooted at a line vertex leaves a cyclic-seam convention ambiguous.
  Every actual simple-cycle use in the main proof has the required point-rooted
  representation; this is not presented as a new counterexample to the theorem.
- The short transverse reachability cutoff is exactly 2*(lineLength+1)<=k,
  including odd k and zero-length paths. The algebraic predicate is proved
  equivalent to actual slope-restricted simple paths.
- Fault graphs are spanning edge-subgraphs of the input graph G, with at most f
  incident faulty edges at each vertex. They need not be subgraphs of the
  proposed spanner H. Distances after faults use infinity for disconnection.
- The protected edge is included when proving the base matching property.
  Cloud-path projection avoids the entire base matching before loop erasure.
- Theorems 2 and 4 are cited background results, not new claims or assumptions
  of this paper's lower-bound proof. They are not claimed formalized here.

Verification status is recorded separately. A correction record, source hash,
or semantic review alone does not certify compilation or kernel replay.
