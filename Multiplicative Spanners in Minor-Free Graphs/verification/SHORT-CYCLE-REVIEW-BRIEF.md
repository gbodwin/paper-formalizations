# Frozen short-cycle phase and residual path classification

Fifteen exact draft sources,943 lines, outside the frozen227 production packet.
Hashes are in short-cycle-phase-freeze.json. No earlier proof body changes.
All statements have individually passed strict Lean checks; frozen grouped
checks, integration/audit/replays and reciprocal source review remain separate.

## Actual path geometry and payment

WeightedPathSplit proves exact mass accounting on genuine simple concatenations
and chooses an actual first-threshold balanced split. PathRootedWalk lifts each
coarse subpath to original supported host walks. CoarsePathDetourGap lifts the
middle path inside A sup T, whose edges are strictly lighter than the actual
heavy connector e. The existing weighted-girth replacement theorem therefore
proves (g-1)w(e)+1 < middle mass; no shortest-path projection or detour cost
premise is supplied.

ShortCycleArms records three consecutive actual pieces of one simple coarse
path: a left outer arm, a middle path and a right outer arm. Each outer has
(d+1)-mass in [L,L+D+1); the middle mass is at most2(L+D+1). ShortCycleSelection
constructs both outer arms from actual longer pieces by threshold trimming.
The selected whole is literally a contiguous subpath of the original path.

ShortCycleWalks balances the middle and joins the two rooted unions with the
same original heavy edge. Every pair of host vertices has a supported walk of
weight at most R_e=2(L+2D+1)+w(e). Exact whole-path node mass, old diameter
credits and at least |S|-1 genuine internal unit connectors imply a surplus
c*delta beyond c*R_e, where delta=(g-2)ell-6D-4 and ell<=w(e),g>=2.

BoundedSurplusPayment splits on the actual finite carrier size. With a=qM,
all per-vertex heavy charges and a cb/2 reserve are paid if
  a*N+cb/2 <= c*delta,
  2c*(2(L+2D+1)+M)+cb <= N*cb,
  2a <= cb.
The core wrapper derives the geometric surplus from actual weighted girth.
It does not put a payment inequality into the core predicate. The explicit
old-family diameter/baseline credits and these numeric scale conditions remain.

ShortCycleCorePacking internally maximizes disjoint finite eligible carriers.
WeightedShortCyclePhase constructs the resulting original-host cluster family,
retains each chosen R_e, pays every original incident heavy edge (old family
coverage is explicit), and identifies disjoint original unit connectors. The
same old no-loop/no-parallel girth consequences justify the degree-to-edge
budget. A uniform family certificate is2(L+2D+1)+M, but the paid radius remains
the actual selected R_e, never silently enlarged to the uniform bound.

## Actual residual classification

SeparatedPathPieces proves that a middle path with mass>2(L+D+1) has two
threshold endpoint pieces separated by a nonempty actual gap. Simplicity of
the whole original path forces support disjointness across that gap.
WeightedJoinedArms trims the outer pieces and forms actual two-arm objects.
SamePathCoreDichotomy constructs either a short-cycle core (short middle) or a
four-arm core (long middle) from an original heavy edge between the two far
centers of a single simple path.

PathCoreResidual selects a short-cycle maximum, then a four-arm maximum in its
actual remaining vertex set. The families are disjoint. Any residual eligible
core would enlarge the relevant finite maximum. Therefore a surviving original
heavy edge on the same residual simple path must have a short outer affix at
one endpoint. Between two disjoint residual paths, both endpoints cannot be
weighted interiors. This is a graph/support conclusion, not a supplied
classification or an abstract charge bound.

## Limits

No assertion yet joins the full old level into a covering new level. Short
end affixes and small components still need absorption; deferred edges, the
simultaneous parameter choice, global credit propagation, full weighted
lightness and runtime remain open. No new theorem defect or whole-paper
completion is asserted. The independent review should check exact original
edge identities, supports, inequality directions and these boundaries.
