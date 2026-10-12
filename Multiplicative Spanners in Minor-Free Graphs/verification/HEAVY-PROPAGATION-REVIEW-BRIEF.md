# Actual heavy-owner and credit propagation (306 candidate)

Exact parent295: a9de09ac540a2a8f1a414623c3bd7382b89b7935.
Eleven new sources, 746 lines, are frozen in heavy-propagation-freeze.json;
307 source/root entries are in checkpoint39-source-hashes.json. All295 prior
mathematical bodies and all workflow/checker gates stay unchanged. All isolated
exact sources pass strict Lean; production builds/audit/replays are separate.

## Actual joins

- OwnedBlockPartition and OwnedBlockFamilies turn an owner map into literal
  block families and prove the combined nonempty/disjoint/exact-cover carriers.
- ConnectorCreditExtension proves monotone extension of actual connector
  identities across coarse graphs and carriers. Disjoint original root/block
  carriers imply disjoint original connectors. Its root ledger keeps every
  previously spent allocation while combining root and block budgets.
- RootedAssemblyCreditLedger derives that ledger from the already constructed
  one-root path assembly: selected-block and endpoint allocations are already
  spent; only the exact future reserve remains. The original root credit
  explicitly pays c*(d(root)-1)+old spare.
- ActualHeavyCreditPropagation applies the actual short-block heavy absorption
  to that root-ledger format. SimultaneousHeavyAbsorption constructs all enlarged
  root radii/walks and preserves both individual original ledgers and the pooled
  inequality after proving carriers disjoint.
- ActualHeavyOwners internally selects owners from nonempty original unpaid
  heavy-edge bags, retaining original unordered identities. The endpoints are
  reversed only so the root endpoint comes first in the absorption walk.
  ActualUnpaidHeavyAbsorption feeds these actual choices to the simultaneous
  construction and proves every inactive block's unpaid edge bag empty.
- RetainedInactiveBlocks keeps all inactive blocks as separate output carriers.
  RetainedPathBlockPooling derives their real mass-minus-one radii, confined
  original-host walks and intrinsic original credits, then pools them with the
  enlarged roots on the full disjoint Sum-indexed carrier partition.
- ActualRetainedHeavyPhase joins the actual edge choices, exact full retained
  cover, all root/inactive walks, old spent allocations, active allocations,
  remaining future reserves and inactive intrinsic credit into one inequality
  against the original vertex credits plus original unit-tree edge weight.
  Inactive blocks are retained; no heavy-edge credit is introduced.

## Scope and unresolved joins

The root carriers, path-block family, input credit invariants, original host
walks, cover and no-unpaid-residual-adjacency remain explicit inputs. The latter
are established locally by284; this packet does not yet instantiate them all
from one common full preceding core/path construction. The ledger theorem
shows the actual one-root result supplies the correct root reserve, but the
full previous-phase carrier/segmentation compatibility join remains open.

The path lower-mass parameter L in this packet need not be positive: it may be
zero for terminal short blocks. Every block still has actual mass at least one
from its nonempty path and d>=1. The upper mass K>=1, active block cardinal bound
N, and conservative root spare >=2*c*M+2*N*a+future stay explicit. Their shared
compatibility with the earlier phase budgets and asymptotic scales is unproved.
The final covered carrier is exactly old-root union plus the supplied P union;
identifying it with the entire old-label universe remains a prior-phase join.
The original core-maximality proof must still discharge hno in that same common
instance. Global multilevel credit potential, deferred/empty-root cases, weighted
lightness, runtime and final whole-paper audit remain open.

Please review original connector monotonicity/injectivity, spent-credit
provenance, subtype owner/family identities, root orientation of actual heavy
edges, literal inactive-bag emptiness, retained block walks and the single
combined pooled budget. Save review/heavy-propagation-review.json. Source review,
strict production gates, exhaustive axiom audit, official kernel replay,
remote byte binding and full exact-commit CI are separate.
