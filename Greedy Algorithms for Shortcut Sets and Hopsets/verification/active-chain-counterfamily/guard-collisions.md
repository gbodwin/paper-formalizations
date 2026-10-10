# Off-path guards: a proved supply lemma and a quadratic collision obstruction

Date: 2026-10-10. Mathematical analysis of source-dependent chain Algorithm 2 in arXiv:2511.20111v2. The separation lemma and the explicit collision family have different verification scopes, stated below.

## Result

Two elementary statements are proved below.

1. **Positive residual lemma.** A guard inaccessible from a pivot on the i-th chain of an original-source valid path forces every minimum path to that guard to use at least d(s,z)−i chains absent from the original path. Thus a cheap rebased minimum for an early pivot supplies linearly many genuinely off-path chain vertices, even if all guard choices collide.
2. **Collision obstruction.** For every integer m≥3 there is an explicit empty-H supplied-cover instance with maximum important distance L=3m+1, and one unique minimum path for a maximum pair, whose early/late rectangle contains m² strict triangle failures. Every rebased minimum has cost 3. Every one has the same unique last disallowed edge into the same guard chain, and the last-bad-edge construction returns the same guard z, with d(s,z)=L. The instance can satisfy the paper's numerical cover conditions and L³>n.

This refutes a reduced argument that counts distinct last-bad-chain guards as if they were distinct failed source/target pairs, or distinct failed sources. It does **not** refute cubic progress. In fact this family has an explicit off-path rectangle with raw-potential drop at least m²(m−1), asymptotic to L³/27.

The universal cubic bound remains open in this report. No claim about the paper's final theorem follows from the collision obstruction.

## Model and source alignment

Use the model in ChainDistance, ChainImportantPairs, ChainGuard, ChainInteriorSavings, and ChainRectangleCharging. Let G be a finite DAG, with disjoint reachability chains and legal internal preprocessing. Let H consist of legal original-closure edges. Original reachability, not augmented-path source choices, defines the earliest reachable chain vertex e(s,C).

For each source s, an augmented edge is retained when its endpoints have the same chain label, its target is uncovered, or its target is e(s,C) for its chain C. A valid path uses these retained edges. Its cost is the number of distinct covered chains visited. Write d(s,t) for the actual minimum cost at the fixed state H. The important demands are (s,e(s,C)), and the raw potential is the sum of their d-values. Shortcut insertions keep the original selectors fixed.

The positive result below applies to arbitrary legal H. The explicit family has H empty and its required internal chain edges already in G. The family is for an explicitly supplied cover; it does not claim that the paper's cover-selection implementation chooses it. It has many singleton chains, so it also does not resolve a stronger hypothesis requiring all chosen chains to have a large common cardinality r.

The relevant paper passage is the definition of normalized valid paths and the proof of Lemma 5.7. The unproved ingredient is the source/target multiplicity needed for one large raw-potential decrease, not the already-proved replacement lemma for a shared segment in actual minimum paths.

## 1. Positive lemma: an inaccessible guard supplies off-path chains

Let P be an s-valid augmented path visiting distinct chains C₁,…,C_R in that order. Let u be any vertex of its C_i segment, including its first or last vertex; the statement does not require a particular endpoint of the segment. Let z be reachable from s in G but not reachable from u in G. Let Q be any augmented s-to-z path using only original or legal closure edges.

**Avoidance statement.** Q meets none of C_(i+1),…,C_R.

**Proof.** Suppose Q met some C_k with k>i, at a vertex y. Let x=e(s,C_k), the first vertex of P's C_k segment. The suffix of P from u reaches x in original G, because every augmented edge is legal in original reachability. Since Q begins at s, y is s-reachable. Earliestness of x in the reachability-ordered chain gives x→*y in G. The suffix of Q gives y→*z in G. Thus u→*x→*y→*z, contrary to the assumed inaccessibility of z from u. This argument does not require Q itself to be s-valid. ∎

In particular, let Q be an actual minimum s-valid path to z, so count(Q)=d(s,z). Only C₁,…,C_i among P's chains can occur on Q. Therefore

    |chains(Q) \ chains(P)| ≥ max(0, d(s,z)−i).

This counts distinct chains, hence supplies at least that many distinct vertices outside P by choosing one vertex from each such chain. It is stronger than merely saying z lies off P.

**Guard corollary.** Suppose P is a minimum s-valid path to an important target t and count(P)=d(s,t)=L. Put δ=d(u,t). If i+δ<L, then the first alternative in the proved guard dichotomy is impossible, since the prefix of P gives d(s,u)≤i. Consequently there is a guard z with

    (s,z) important,   z→*t,   u cannot reach z,
    d(s,z) ≥ L−δ+1.

Every minimum path Q to this z has

    |chains(Q) \ chains(P)| ≥ L−δ+1−i.

For example, if i≤L/3 and δ≤L/3, there are at least L/3+1 off-P chains (with the usual integer interpretation). The conclusion is obtained by retaining the original source s throughout; it asserts no rebased optimality for portions of Q.

**What it does not give.** These off-path vertices are legitimate candidate sources, but no lower bound on their rebased distances to a useful target set has been proved. Nor does the lemma show that their actual minimum paths share an interior segment. Those are the missing hypotheses needed to apply ChainRectangleCharging. The same off-path chains can serve as witnesses for many different guards or failed pairs.

## 2. Explicit quadratic collision family

Fix m≥3. The core vertices are

    s;
    a₁,…,a_(3m);
    w₁,…,w_(3m−1);
    z,b.

The edges are exactly:

- s→a₁→⋯→a_(3m);
- s→w₁→⋯→w_(3m−1)→z→b;
- a_i→b for 1≤i≤m;
- b→a_j for 2m+1≤j≤3m.

All vertices except z,b are singleton chains. The remaining chain is C=(z,b). There are

    n_core=6m+2 vertices,    M=6m+1 chains.

A topological order is s, then a₁,…,a_(2m), then all w-vertices, then z,b, then a_(2m+1),…,a_(3m). Thus G is a DAG. The only nontrivial chain already has its internal forward edge z→b, giving one-hop internal preprocessing. Take H empty.

### 2.1 Original reachability and filters

Source s reaches all core vertices, and its selector on C is z. Hence all a_i→b edges are forbidden in the s-filter. All the displayed path edges and b→a_j edges are allowed in that filter.

For i≤m, a_i reaches b through its cross edge but cannot reach z or any w-vertex: all edges leaving the a-arm either move forward on that arm or enter b, and everything reachable from b lies on the late a-arm. Hence e(a_i,C)=b. Each a_i→b→a_j, for i≤m and j≥2m+1, is a valid a_i-path.

For i>m, a_i cannot reach C. A source w_ℓ reaches its remaining w-arm, z,b, and the late a-arm; its selector on C is z. Sources z and b have their own source vertex as selector on C. These facts describe every selector needed in the distance calculations.

### 2.2 Exact distances from s and global maximum

All a_j are important targets for every source that reaches them, since they are singleton chains. For s,

    d(s,a_j)=j+1               (1≤j≤3m),
    d(s,w_ℓ)=ℓ+1              (1≤ℓ≤3m−1),
    d(s,z)=3m+1,
    d(s,s)=1.

Indeed the ordinary a-arm has cost j+1. Its cross exits to b are forbidden in the s-filter. Every alternative valid path to a late a_j travels the entire w-arm and C before entering the a-arm, at cost at least 3m+2. Hence the ordinary a-arm is the unique minimum s-to-a_j path for every j. The w-arm and the path to z are the only directed paths to those targets, giving their stated costs. Vertex b is not an important target for s because C's entry is z.

For completeness, all other sources have important distances at most 3m+1:

- From a_i with i≤m, targets a_j with i≤j≤2m have their unique a-arm path, of cost j−i+1≤2m. Every target a_j with j≥2m+1 has distance exactly 3. The entry b of C has distance 2. Its own source demand costs 1.
- From a_i with i>m, the only reachable vertices are the forward a-arm; its maximum distance is 3m−i+1≤2m.
- From w_ℓ, targets on the remaining w-arm have cost at most 3m−ℓ; z costs 3m−ℓ+1; every late a_j costs exactly 3m−ℓ+2≤3m+1. There is no route to early a-vertices.
- From z or b, the own-chain demand costs 1 and every reachable singleton a_j has distance 2, using b→a_j directly.

The exact global maximum is therefore

    L=3m+1.

In particular P=s,a₁,…,a_(3m) is the unique minimum valid path for a globally maximum important pair (s,a_(3m)). There can be other globally maximum pairs; uniqueness of the maximizing pair is not asserted or needed.

### 2.3 A quadratic rectangle of forced guard collisions

Let

    U={a_i:1≤i≤m},
    T={a_j:2m+1≤j≤3m}.

Both have cardinality m, and all m² pairs U×T are important. For each i,j in these ranges, the unique minimum a_i-valid path is

    Q_ij = a_i→b→a_j,
    count(Q_ij)=d(a_i,a_j)=3.

There is no direct a_i→a_j edge. The ordinary a-arm subpath costs j−i+1≥m+2>3. A route reaching b from a later early a-vertex adds at least one extra singleton; a route leaving b at an earlier late a-vertex also adds an extra singleton. This proves uniqueness of Q_ij as well as the exact cost.

The rebased triangle inequality actually fails strictly for every such pair:

    d(s,a_j)=j+1 > i+4 = d(s,a_i)+d(a_i,a_j),

because j−i≥m+1≥4. The long original subpaths thus fail the intended comparison by an amount growing with m, not merely by a tie or a one-chain convention.

On Q_ij, the only edge disallowed by the s-filter is a_i→b. It crosses from a singleton to C at b although e(s,C)=z. Its following edge b→a_j enters a singleton and is allowed. Thus this is the unique last disallowed edge, and the constructive last-bad-edge proof in ChainGuard.incompatible_guard always returns

    guard = e(s,C)=z.

The same guard has d(s,z)=L, is unreachable from every member of U, and reaches every member of T. Consequently m² distinct strict triangle failures and m distinct failed sources can all produce just one distinct last-bad-chain guard.

This statement concerns the **constructive last-bad-edge guard**. The abstract existential conclusion of the guard dichotomy may also admit other vertices satisfying its numerical inequalities; no uniqueness among all possible existential witnesses is claimed.

## 3. Numerical cover conditions and the active regime

Pad the core with isolated uncovered vertices to exactly

    n=M²=(6m+1)².

There are enough padding slots. No original distance or important pair changes, and isolated uncovered sources have no reachable covered chain. Every path uses at most one uncovered vertex. Also

    M≤2n^(2/3),       1≤n^(1/3).

Thus the supplied cover meets the stated numerical chain-count and uncovered-path requirements. Finally,

    L³−n = (3m+1)³−(6m+1)²
          = 3m(9m²−3m−1) > 0.

The collision obstruction therefore holds while Algorithm 2's stopping condition is violated, for arbitrarily large L. It is a legal initial state for this supplied cover, rather than a conjectured positive-time greedy state.

## 4. Why the same example still has a cubic raw-potential edge

Insert e=(w_m,w_(2m)), a legal original-closure edge. Use the off-P source set

    U'={w₁,…,w_m}

and off-P target set

    T'={w_(2m),…,w_(3m−1)}.

Both sets have m vertices. Every target is a singleton chain, so all pairs are important and the new edge is allowed in every relevant source filter. For i≤m and j≥2m,

    d(w_i,w_j)=j−i+1,

because the w-arm is the unique directed route to each w-target. Every such actual minimum path contains the shared segment w_m,…,w_(2m), of m+1 chains. Its replacement removes exactly m−1 singleton chains. Hence, summing distinct actual important pairs and using monotonicity elsewhere,

    raw_potential(H)−raw_potential(H∪{e}) ≥ m²(m−1).

This is precisely the sort of same-source interior charging justified by ChainInteriorSavings and ChainRectangleCharging. It gives

    liminf_(m→∞) best_legal_edge_drop/L³ ≥ 1/27.

The guard collisions do not defeat this rectangle: the shared guard's long access arm supplies the extra sources and targets. Isolated padding changes none of these quantities.

## 5. Precisely what remains unresolved

The positive avoidance lemma is a rigorous first supply step: a cheap rebased path either composes or produces many chains genuinely outside the chosen path. The collision family shows why one cannot turn the number of failed prefix/suffix pairs directly into a comparable number of distinct guards.

To obtain general cubic progress, it remains necessary to turn the off-path chain supply into enough **distinct important pairs supported by the same insertion**, with actual distance savings. A long minimum path to one shared guard is not enough by itself: its subpaths can again become much cheaper on source rebasing, as the active-tree counterfamily already demonstrates. Recursing on guards may revisit or merge at old guards; counting a conceptual guard tree as if its vertices were distinct graph vertices is unjustified.

The proved supply bound and the explicit collisions neither settle that recursion nor provide a uniform Ω(rL²) bound for a cover of equal-size r chains. The companion check-guard-collision-family.py independently verifies all source selectors, important distances, minimizer uniqueness, strict triangle failures, constructive guard collisions, and the chosen cubic-saving edge for m=3,4,8,16,32,64. Results are in guard-collision-checks.json. These finite diagnostics support the explicit ordinary proof; the general cubic claim remains open.
