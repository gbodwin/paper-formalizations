# Remaining real reserve compatibility join

The current published318 and next mixed transport statements are valid
conditional inequalities. Their common reserve hypotheses are not yet supplied
by the earlier core constructions.

Concrete issue: four-arm/short-cycle/branching cores may retain only baseline
scale c*b/2 after their incident edges are paid. Generic small-heavy absorption
requires 2*c*edgeMax+2*N*a+future at every root. With the intended old baseline
b approximately epsilon times edgeMax, that substitution is invalid.

The source resolves this through root provenance, not a larger arbitrary
constant: BLWN1711.00821v1.txt lines687-699, Observation18, proves every remaining
unpaid Step2 edge reaches a Phase1 high-degree root. Other phases have already
paid their incident edges. Phase1 centers retain heavy-scale9*c*ell credit
(Observation5); Claim27 accounts for the at most6 heavy edges on the enlarged
diameter path. The earlier generic uniform-spare statement discarded this
root-kind/prior-payment information and must be sharpened before global use.

Next concrete construction work:
1. Preserve owner.val not in paid from exists_actual_heavy_attachments through
   exists_original_heavy_owners (the underlying witness already has it).
2. Enlarge path paid labels by the actual previously-paid non-Phase1 root labels.
   no_unpaid_residual_edge is monotone under enlarged paid labels; actual owners
   then lie only in high-degree roots. Use the literal previous paid original
   edge bag so no double spending or fictitious low-degree root count occurs.
3. Refine per-root absorption to distinguish empty assigned blocks. Empty roots
   keep their original radius/ledger and require only future<=reserve, while
   roots with actual active blocks need the heavy-scale reserve bound.
4. Join Phase1 spare with that restricted active-owner family. Phase2/3 roots
   need only their already derived selected/endpoint allocations and future.
5. The prior root-phase payments, exact original residual bag, and unit-tree
   connector identities must then pool without double counting. Tighten the
   existing whole-T upper bound to the actual connector union for the eventual
   multilevel credit potential; actual later connectors are fresh relative to
   old cluster interiors.

These are open implementation/proof obligations, not assumed certificates and
not proof errors in the current scoped conditional modules. Preserve this
boundary in every publication and final whole-paper status.
