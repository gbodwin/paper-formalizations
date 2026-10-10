# An inactive-regime obstruction to unrestricted cubic progress

2026-10-10. Ordinary mathematical proof with independent source review. This is not a Lean theorem. The constructed state is already stopped. It does not refute the active-regime cubic claim, the source phase lemma, or the nearlinear main theorem. Finite diagnostics are supplementary only.

## Statement

For every height h>=2 there is a DAG with a legal chain cover/preprocessing and empty shortcut state, maximum important normalized distance L=h+2, for which every one-edge raw potential decrease is at most

    (h+1)(h+2)+2.

Thus no positive absolute c can guarantee decrease >=c L^3 for every such instance at every L. The construction has n=4^(h+1) after harmless isolated padding, and n>=L^3 for h>=2. Consequently the family is outside the relevant strict active regime L^3>n and does not contradict the paper's phase bound or output-size theorem.

## Construction and already checked distance facts

Use the binary-tree family from [the reviewed active-tree construction](../active-chain-counterfamily/near-maximum-obstruction.md), setting stretch parameter k=0 (so all upward links are direct). The source code `check.py` constructs exactly this specialization with explicit topological order.

Take a perfect binary tree of height h, with root o, leaves at depth h. For each node u introduce the two-vertex chain C_u=(x_u,y_u), with x_u -> y_u. For each nonroot u add y_u -> x_parent(u). Add a separate singleton chain {r}, with r -> x_leaf for every leaf. For each node u and every strict ancestor a of u other than o, add y_u -> y_b where b is the sibling of a. No sibling-of-u cross edge is added.

Tree height increases strictly on each edge between different tree chains. The singleton r precedes all tree vertices. Hence the graph is a DAG. There are T=2^(h+1)-1 tree chains, M=T+1=2^(h+1) chains including {r}, and 2T+1 core vertices. Internal chain preprocessing is already present with one hop.

For a non-r source s=x_u or y_u, the exact reachability/entry description is the k=0 specialization of the existing review:
- own chain from s onward, whose important entry is s;
- both vertices on every strict ancestor chain, entry x_a;
- only y_b on every sibling b of a strict ancestor other than o, entry y_b.
No other tree chain is reachable. This set is closed under all outgoing edges. Every parent important entry has a two-chain route; every more distant ancestor entry x_a has a three-chain route using y_u -> y_b -> x_a, where b is sibling of the child of a lying above u; every side entry y_b has a two-chain route. Thus every non-r important distance is <=3. Every own-chain important distance is exactly1 and every other important distance is >=2.

Source r reaches every x_u, so every important tree target is x_u. An r-valid path cannot use an original cross edge ending y_b: it would enter C_b at the wrong entry, and chain height strictly increases on that edge. Thus r-valid paths are ordinary leaf-to-ancestor climbs. For a tree node a of depth d,

    d(r,x_a)=h-d+2,

and the global maximum is L=h+2. The source r's own demand has distance1.

## Upper bound for every legal inserted edge

Let e be any original-closure edge. Reachability and entry selectors do not change when e is added. Distances cannot increase. Already present edges and within-chain edges have zero marginal, because the only strict forward within-chain pair x_u -> y_u is already present. There are no edges entering r. It suffices to consider e between distinct chains.

### Non-r source rows: total decrease at most2

Every non-r important distance was at most3. A strict decrease can only be from3 to2: the immutable endpoint-label floor rules out a decrease below2 for distinct endpoint chains, while own-chain demands remain at1. Therefore any strictly improved non-r demand (s,t) has a new valid route using exactly two chains. This route must use e, or its old normalized distance would already have been at most2.

If e starts at r, no non-r source can use it, so this contribution is zero. Otherwise write C_u,C_v for e's two distinct tree endpoint chains. Original reachability and the explicit topological order imply height(C_u)<height(C_v). Since the new two-chain route contains e, its chain set is exactly {C_u,C_v}. The source chain has height at most height(C_u), and the target chain has height at least height(C_v), so the source belongs to C_u and the target to C_v. There are at most two sources in C_u, and each has at most one important target on C_v. Hence at most two distinct important demands can improve, by at most one each. Their total raw drop is at most2.

This argument covers every legal e, including edges ending at late vertices; it does not assume the edge itself is an important demand.

### Source-r row: total decrease at most(h+1)(h+2)

An improved r-valid minimum route must use e. An edge ending at y_a from another chain is invalid for r, since r's entry on C_a is x_a. Thus any useful e ends at x_a for some tree node a. All original edges before and after its unique use are r-valid, and therefore all original interchain steps are ordinary upward tree links; original cross edges remain invalid because the entry selectors are unchanged. Acyclicity prevents using e twice.

After the inserted edge reaches x_a, the route can reach only ancestor chains of a by original valid steps. Thus only the at most h+1 important targets x_b with b an ancestor of a can improve in r's row. Each old distance is at most L=h+2, so the entire row decrease is at most(h+1)(h+2).

Combining both source classes proves the claimed upper bound. For h>=4 this is at most2h^2, while L^3>h^3, so bestDrop/L^3<=2/h ->0. This is a quantified obstruction to an unrestricted all-L cubic lower bound, not merely failure of its hereditary proof.

## Chain-cover numerical regime and non-claim

Pad the covered core by isolated uncovered vertices to n=M^2=4^(h+1). This changes no important demand, normalized distance or positive marginal. Every path contains at most one uncovered vertex. The cover has M<=2n^(2/3), all supplied chains remain disjoint, and internal one-hop preprocessing meets the four-hop interface.

For h=2, n=L^3=64. The inequality n>=L^3 propagates with h because n quadruples while ((h+3)/(h+2))^3<4. Thus all h>=2 satisfy L<=n^(1/3). The actual threshold algorithm would already be stopped, so the family makes no active-step or greedy phase-length counterexample claim. The additive and moment bounds already proved in Lean remain compatible.

## Evidence boundary

`finite-checks.json` records exact all-candidate enumeration through the tested finite heights. It checks raw best drops, not only the proposed upper bound. The quantified argument above passed an independent source-only review; its receipt is in `review.json`. No Lean construction or upper-bound theorem for this family has been written.
