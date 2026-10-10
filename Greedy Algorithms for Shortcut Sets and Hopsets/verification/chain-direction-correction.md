# Directed-chain qualification in Corollary 5.3

Source: arXiv2511.20111v2, printed page 11 / PDF page 13.

The corollary states the constant hop bound for any two vertices on a directed chain. Its proof adds consecutive forward edges and forward path supershortcuts. The intended statement therefore requires the ordered pair to follow the chain order, equivalently to be reachable along that chain. All added edges should also be expressly required to preserve reachability.

For the chain a→b, a valid shortcut set cannot create a b→a path. Thus the reverse ordered pair does not have distance at most four. The bare existential wording only asks for an edge set H and, read without the shortcut requirement, could permit arbitrary reverse edges; the defect is the omitted direction/shortcut qualification in the intended statement and construction, rather than a refutation of an unrestricted existential claim.

Corrected statement: for every vertex-disjoint directed-chain family, there is a reachability-preserving shortcut set of the claimed size such that each forward ordered pair of vertices on any one chain has hopdistance at most four. The subsequent application uses precisely these forward pairs. An independent source review confirmed this local scope correction; it is separate from the unresolved Lemma 5.7 hereditary-optimality issue.
