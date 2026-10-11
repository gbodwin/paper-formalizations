# Checkpoint 22: exact graph setup

This five-source continuation is a background construction toward the general
density-increment argument. It is not a new proof of a numbered main theorem.

| Export | Actual conclusion | Explicit boundary |
| --- | --- | --- |
| `exists_minimum_density_induced` | Nonempty minimum-cardinality induced U retaining E(U)>=d|U|, all degrees>d | Positive real d and nonempty finite input with that density |
| `IsGeneralStarForest.fullMinorModel` and `quotient_card` | Literal full covering quotient, bounded branches, exact vertex count | Supplied actual pairwise-disjoint center/leaf branches; boundedness uses k>=1 |
| `exists_maximum_small_clean_star_forest` | Finite maximum over literal degree/edge-loss predicate; empty admissible | Does not itself imply nonempty coverage |
| `MinorModel.edge_count_le_of_branch_match` | Genuine edge injection into matching full minor | Actual branch equality, nonempty/disjoint source model, full target model |
| `clean_star_or_nonempty_maximum_forest` | Original induced dense alternative or internally selected nonempty maximum clean family | Full single-star numerical/neighbor/original-degree domain; loss coefficient 4*eps2*d |

The last theorem assumes k>=1, K>=1, d>=1, 0<=eps1<=1, eps2>=0,
eps2*d>=1, k<=eps1*d, |T|>=2*eps1*d, actual adjacency from c to every
member of T, and original degree<=K*d throughout {c} union T. Its dense
alternative has |S|<=3*k*(K*k)*d and E(G[S])>=eps1*eps2*d^2/2.
Its family alternative maximizes the center count among all actual general
star forests with those literal original-degree and complete quotient-loss
conditions. No initial family, mate certificate, growth oracle, or supplied
maximizer occurs in this theorem.

Protected-family augmentation, two-star replacement and the residual counting
argument remain to be constructed before a general density trichotomy can be
claimed. No main upper bound or new source-theorem defect is asserted.
