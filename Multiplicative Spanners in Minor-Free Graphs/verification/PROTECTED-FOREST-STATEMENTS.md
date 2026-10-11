# Checkpoint 23: protected-family extension

This six-source component proves actual residual-star augmentation and its
maximum-family consequence. It is not a completed numbered main theorem.

The finite graph is simple. The common domain is natural k>=1 and real
K,d>=1, 0<=eps1<=1, eps2>=0, eps2*d>=1, k<=eps1*d. The dense alternative
is an actual finite original-host S with |S|<=3*k*(K*k)*d and
E(G[S])>=eps1*eps2*d^2/2.

`extend_clean_forest_or_dense` takes an actual clean family, a residual center
c and a residual neighbor set T with |T|>=2*eps1*d. All degrees throughout
{c} union T are original-host degrees and are at most K*d. It constructs
the actual new star, preserves every old leaf assignment and increases the
center count by exactly one. The actual complete canonical quotient satisfies
the same 4*eps2*d loss allowance per covered vertex. No extension oracle or
branch-matching certificate is assumed.

`dense_or_maximum_clean_forest_residual` selects the finite maximum internally.
In the absence of the dense alternative, each original-degree-small residual
center has fewer than 2*eps1*d original neighbors that also lie in the
original-degree-small residual set. The selected family may be empty.

The proof uses a one-way exact old-branch invariant. This is sufficient for
the directed edge injection from the constructed minor to the canonical
full quotient. No hereditary mate assertion is introduced. The actual
2*(k-1)*eps2*d new loss is paid by the 4*eps2*d*k added clean allowance.

Two-star replacement, positive quantitative coverage, the general density
trichotomy, construction runtime and the main upper bound remain open.
