# Independent main-statement coverage audit request

Exact published candidate: c2047a4109b7add39173d61013ef3d1f72ad7586,
tree ef2e7b00763e01bd4dec5da123b803bedee79eb1. Local source tree:
/workspace/shared/minor-recovery-20261012/production478/Multiplicative Spanners in Minor-Free Graphs.
All 478 source hashes are in verification/explicit-lightness478/all-source-hashes.json.

Original paper: https://arxiv.org/html/2504.16463v1
PDF: https://arxiv.org/pdf/2504.16463v1
The original source is unchanged. Review the main novel statements and the
mathematical dependencies used in their proofs, distinguishing cited background
results/conjectures from results claimed by this paper.

## Correspondence

- Main Theorem6 sparsity / Theorem13 upper / Lemma16:
  GreedyMinorFreeSparsity.greedy_minor_free_sparsity is an actual greedy spanner,
  with edge bound 2*fullDensityLoss(h)*h^(2/(r+1))*n. Its domain is all finite
  graphs, r>=1, h>0, globally positive Sym2 weights. GirthMinorFreeUpper proves
  the corresponding actual graph density/edge bound; FullDensityWitness proves
  full_density_witness and fullDensityLoss_polylog, the literal degree-nine
  logarithmic factor. No density-increment oracle is supplied.
- Main Theorem7 / Theorem13 conditional lower:
  AllCliqueOrdersLowerBound.girth_conjecture_sparse_lower_bound_all_h and
  ConnectedLowerBound.girth_conjecture_connected_lower_bound. They construct
  every sufficiently large exact graph size for each h>=3 at fixed r>=1,
  from the explicit ErdosGirthConjecture r assumption. The latter gives both
  actual edge lower bounds and connected-graph lightness against an actual MST.
  No positivity-of-linear-lower-bound assertion is made at h=1 or2.
- Main Theorem6 lightness / Theorem17:
  PositiveEdgeMinorLightness.positive_edge_minor_lightness constructs H,T,
  IsSpanner G H w ((1+epsilon)*(2*r-1)), CliqueMinorFree H h, T<=H,
  IsMinimumSpanningTree G T w and the actual lightness bound. Domain:
  connected finite G, n>=2, h>=3, r>=1, epsilon>0, w positive on actual edges.
  Delta=min(epsilon,1); bound is
  C*(logb 2 (8097/delta)+1)*(Nat.log 2 h+2)^9*h^(2/(r+1))/delta^3,
  C=2*43*30008*8097^3*(1600000*131104^7*24576^2+2*131104^3).
  This is an explicit quantitative inequality, not an IsBigO declaration.
  Check its relation to the sufficiently-small-epsilon source statement.
- GreedyMinorLightness.greedy_minor_lightness and
  GreedyMinorPolylogLightness.greedy_minor_polylog_lightness give the literal
  ordered greedy graph with retained original MST for epsilon<=1 and globally
  positive Sym2 weights. EdgeWeightTransport and PositiveEdgeMinorLightness
  remove nonedge positivity and allow arbitrary epsilon by explicit transport
  and stretch monotonicity. The capped-epsilon existence theorem does not assert
  identity with uncapped-epsilon greedy.

## Constructed lightness dependency chain

CanonicalFreshPaidPhase constructs the ordinary or injected singleton route.
CanonicalHistoryStep/CanonicalPrefixHistoryStep retain the same fresh connector
history and pay each actual phase. InitialPrefixState constructs unit-tree
initial clusters. CanonicalFiniteStream iterates actual phases; the subsequent
stream lemmas pay all injections and trim empty tails. DyadicStreamCover and
HeavyStreamsBudget cover all actual heavy edges, and HeavyGraphBudget derives
its cutoff from the actual spanning-tree weight. LowGraphBudget pays the low
edges via sparsity; UnitTreeGraphBudget partitions the literal edge set.
CorrectedUnitTreeLightness selects the epsilon-dependent integer scale.
NormalizedMinorLightness consumes the actual minor-preserving MST normalization.
No phase, hierarchy, edge-cover, final nonempty-band or cutoff oracle survives
in the public lightness theorem.

## Corrections and boundaries to audit

- Claim19: exact weighted girth is stretch+1. The printed larger threshold is
  refuted by the existing Lean triangle family. The corrected threshold now
  feeds the entire construction. The old lower-bound h>=3 correction and the
  introductory lightness-versus-sparsity counterexample remain documented.
- The paper's MST lightness convention needs connectedness (or a separately
  defined spanning-forest extension). Positive edge weights are the standard
  setting used here; no zero/negative-edge extension is claimed.
- Published478 still writes n>=2/h>=3 explicitly in its lightness endpoint.
  A later, unpublished helper proves h>=3 is automatic for connected n>=2,
  h>0 input; a singleton zero-tree-weight wrapper is being checked. Do not count
  these later bytes as reviewed/published without their exact freeze.
- Likewise a later positive-edge-only sparsity wrapper passes locally but is
  outside478; the published endpoint's global positivity is explicit.
- There is no executable-runtime upper theorem in the paper's main statements.
  Historical README runtime placeholders are not evidence of a missing claimed
  mathematical theorem. Do not claim verified executable complexity.
- Local strict checks, source/static reviews, full478 safety audit (2606 own
  declarations, nine full type/body closures), and new-module replays pass.
  Latest full CI is452;474/478 exact CI are monitored separately. No completion
  claim follows merely from these checks.

Please identify any substantive missing main statement, domain gap, vacuous
premise, hidden oracle, incorrect correction, or unjustified asymptotic claim.
A scoped verdict and exact remaining obligations are more useful than a binary
completion label. Preserve all reviewed source hashes in the receipt.
