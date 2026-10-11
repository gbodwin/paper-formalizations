# Constructed square-root-f bound at exact competition 2f

Eight frozen sources, listed in twentyeighth-source-hashes.json, join the actual
seeded greedy algorithm to the existing internally constructed native Eulerian
packing. All 144 parent proof files remain unchanged at c1538fd1.

The final `exists_eft_spanner_square_root_bound` constructs Q and H with Q a true
minimum 2f-fault connectivity preserver, H an f-EFT spanner of stretch
(1+epsilon)(2k-1), and competitive lightness at most

  1 + 16 sqrt(f) (8 + 2048/epsilon * n^(1/k)).

Finite simple graph, globally nonnegative real weights strictly positive on
actual edges, f,k positive naturals and epsilon>0. The zero optimum uses the
existing explicit total real-division convention. No supplied packing, host
family, local blocking certificate or optimality premise occurs in this final
existence theorem.

Semantic checkpoints for reciprocal review:
- Restricting actual blocking pairs to T union U is legitimate because the first
  blocking edge cannot be a seed edge and its second edge cannot lie in T when
  the candidate's original blockers avoid T. The local sample cap is r, while
  the actual recursion still tolerates f faults.
- Embedded host weights and candidate identities are transported injectively.
  Empty candidate sets and singleton hosts remain explicitly covered.
- Only B(e) intersect Q can disqualify an actual seed subtree. A seed cap b and
  2b+h eligible component hosts give h valid hosts. The residual blocker cap is
  a separate r; it is not assumed to equal the actual fault budget f.
- Heavy candidates have residual blocker count at most r and cost at most
  8r L w(Q). Light candidates have more than r residual blockers, hence at most
  f-r seed blockers. They receive 2r+1 unblocked hosts and cost at most
  8f L w(Q)/(2r+1). All counting uses actual finite sets and congestion two.
- r=floor(sqrt(f)) is positive and at most f. The exact integer inequality
  f <= r(2r+1) bounds the light cost by 8r L w(Q), including f=1.
- Existing constructed doubled-subdivision forests and genuine component trees
  discharge all host-family inputs at q=2f. Finite minimization supplies Q.

This is the explicit coarse weighted-girth specialization of the square-root-f
upper consequence of printed Theorems 11/29. It does not restore the refuted
exact lambda expression. Lower-certificate issues remain separate. Runtime,
the full stated multigraph extension, and whole-paper final audit are excluded.

Strict production, root/index, declaration axiom audit, independent kernel
replays, reciprocal component review and exact full CI are distinct gates.
