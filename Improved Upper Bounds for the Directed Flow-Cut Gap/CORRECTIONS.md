# Proof issues and repair status

Source: [arXiv:2604.03412v3](https://arxiv.org/abs/2604.03412v3), 9 July 2026.
Checked on 9 October 2026. These issues concern printed auxiliary statements or
constructions; they do not refute the headline directed flow-cut bounds.
The original published PDF and source archive are unchanged.

## Lemma 18: retain demand endpoints

Vertex cuts are defined using internal vertices, but Lemma 18 requires its
witnesses to lie on paths in G\X. This can delete a remaining demand's endpoint
without actually cutting that demand.

For any integer L>=5, take the chain 0→1→…→L+2, with n=L+3. The three reachable
initial demands are A=(0,L+1), B=(0,L+2), C=(1,L+2); all other demands are
unreachable. The first minimum-candidate mass is 3, and the algorithm starts a
new epoch. Allowed optimal weights for A and B put 4/L on vertex 1 and
(L−4)/(L(L−1)) on each vertex 2,…,L. For C put 1/L on vertices 2,…,L+1.
Unreachable demands have zero candidate mass.

Select A and a level strictly between 0 and 4/L. Exactly vertex 1 enters X.
At the next round, current mass is 2−4/L while minimum candidate mass outside X
is 1, so no epoch switch occurs for natural or binary logarithms. Nevertheless,
none of the remaining demands has a path in G\X. Lemma 18(2) forces an empty
witness system, contradicting its positive lower bound in (3). The family is
unbounded in n; asymptotic constants do not remove it. For any other fixed log
base, take L sufficiently large.

The correct residual graph for a pair (s,t) retains both endpoints:
G\(X\{s,t}). `Basic.lean` proves this exact cut/disconnection equivalence.
Repairing the entire witness construction and its downstream use is still open;
the definition-level bridge alone is not a repaired proof of Lemma 18.

## Theorem 29: contraction must preserve endpoint demands

Take vertices v,u,t, edges v→u, u→v, u→t, unit costs, and weights
w(v)=w(t)=0, w(u)=1. Vertex v is nonterminal and eligible for the printed
low-weight contraction. The original demand (v,t) has internal distance 1 and
requires cutting u.

After contracting v, the graph has u→t and possibly a self-loop at u. No
reachable pair has positive minimum internal distance. The subsequent weight
and cost changes admit the empty reduced cut, which omits u and fails to cut
(v,t) in the original graph. Even vacuously including the deleted v in the
inverse mapping does not help, since v is the demand endpoint.

TerminalPorts.lean proves a permanent-representative construction with exactly
three vertices per original vertex, actual path lifting and loop-erased
projection, exact endpoint-demand distances and cut feasibility, and exact
weight/cost preservation. ShortcutContraction.lean now proves actual shortcut compression/expansion,
removed-mass weight loss, doubled fractional feasibility, and endpoint-preserving
cut/cost pullback. Clipping, normalization, capacity replication and the full
size analysis remain to be assembled; the full reduction is not yet claimed
repaired.

## Theorem 33: scale every multiplicative update

On printed page 32, x=w(e)α is assumed at most 1, then the proof uses
log(1+1/x)=Θ(1/x). This is false as x tends to zero. For x=2^(−m), the logarithm
grows linearly in m while 1/x grows exponentially.

The unscaled update can itself fail: on a two-edge chain with weights
ε=1/(2n), 1−ε and isolated padding, total weight is 1 and the gap factor is 1.
A cheapest-edge cut oracle multiplies the two selected-edge costs by 1+2n and
approximately 2. It selects the ε-edge in a Θ(1/log n) fraction of sufficiently
many rounds, exceeding the required polylogarithmic multiple of 1/n.

The replacement uses a common positive learning rate η<=αw(e), updating a
selected cost by 1+η/(αw(e)). The weighted potential grows by at most 1+η,
and log(1+η/(αw(e)))>=η/(2αw(e)). This gives the bound

q_e/T <= 2αw(e) [1 + log(W/w(e))/(ηT)].

`MultiplicativeWeights.lean` proves the positive-weight oracle-to-family
reduction, choosing η=min(1,αw_min) and a sufficient positive integer T so
q_e/T<=4αw(e). ZeroWeights.lean extends the finite-family theorem to arbitrary
nonnegative weights and approximation factors. A penalty argument derives
zero-weight avoidance from the original oracle; it is not an extra premise.
VertexRounding.lean instantiates this theorem using actual graph cuts and an
explicit rounding-factor premise. The main approximation factor, edge-model
bridge, preprocessing, bounded family size and runtime remain separate obligations. This is a replacement update rule and
proof, not just a changed inequality in the printed argument.

## Lemma 26: account only for genuinely deleted vertices

WitnessThinning.lean gives a corrected numerical greedy scan. A surviving index
skipped by thinning is controlled by the failed threshold test, while only
actually deleted indices contribute to the deleted-weight budget. No monotonicity
of distances along the carrier path is assumed. Under the explicit prefix and
increment bounds, the actual selected list satisfies L/(4B)<=q−1<=L for B>=1
and L>=64B. Selecting a suitable graph prefix and assembling the full endpoint
witness system remain separate obligations.

## Constant correction in Theorem 32

The threshold w(v)>=n^(−c/(1+c))/4 bounds cost(v) by
4 n^(c/(1+c)) cost(v)w(v). The first displayed cost(X1) comparison instead
places a factor 1/4 where 4 is needed. Correcting this factor leaves the
claimed asymptotic exponent unchanged.

`verification/check_counterexamples.py` checks the finite endpoint examples
with rational arithmetic and records representative logarithmic comparisons.
The symbolic arguments above explain their asymptotic scope; numerical checks
are supplemental and are not substitutes for Lean proofs of the repairs.
