# Frozen six-module actual induced dense-witness review

Read-only review in /workspace/shared/minor-free-spanners. Production under
repo/Multiplicative Spanners in Minor-Free Graphs/MinorFreeSpanners.
Six new modules,671 lines: NewBadWitnessClassification,SwapNeighborUnion,
InsertedWitnessDegree,NewWitnessBudget,StarPartnerDegreeSum,UnmatedDenseWitness.
Manifest checkpoint15-source-hashes.json SHA256
02ae37029a58e27c63a79bf25c4dffc73780fd79a9f7bf9be9a74b788580c05d.
Verify all101 entries and unchanged previous94 library files. Separate
strict build/root/index/allowed-axiom/replay logs are dense-witness-*.log.

Check the graph semantics and every cardinality/ordering factor:
- Actual new ordered forest-edge pairs, not merely newly bad center pairs,
  are counted. Old bad center pairs with changed unique leaves are included.
- A genuinely new witness touches an exchanged owner. At such an owner it
  either uses the inserted forest edge or injects into actual exceptional
  third centers with a common-neighbor charge. Reversal contributes the
  explicit factor two; no class is silently deleted.
- H is the literal induced host on starHitUnion C L (N(u) union N(b)),
  including the distinguished old star. Both old exchanged branches lie
  in H. Unchanged and changed new branches are transported explicitly.
- The two inserted-edge witness classes inject into actual neighbor sets
  inside H: one by the other center, one by the other leaf. Actual packing
  ownership proves leaf-injection distinctness. Degree/cardinality instance
  normalization uses genuine Nat.card invariance, not new assumptions.
- The full new-witness upper budget is 2*(degree_H(v)+degree_H(c)+2*ell*q).
  Together with the internally selected finite minimum, this constructs
  real partner vertices with M<=degree_H(v)+degree_H(c)+2*ell*q.
- Distinct actual partner centers/leaves are two disjoint injections into
  the real induced graph. Handshaking then gives M*(M-2*ell*q)<=2*|E(H)|.
  Simultaneously |V(H)|<=(ell+1)*(degree_G(u)+degree_G(b)). The final theorem
  internally constructs the minimizing family; neither a minimum oracle
  nor the graph-degree budget is a hypothesis.
- The dense conclusion M^2<=4*|E(H)| explicitly requires M>=4*ell*q.
  Nonnegative q, disjoint A,C, actual bipartition, full/mate-free input
  packing and fixed covered-leaf domain must remain visible.

Do not claim quantitative cleaning/trichotomy, final density increment,
main upper spanner bounds, or any new source defect. A prospective use of
r>=4*ell*q requires epsilon2<=epsilon1/(4ell), a polynomial rather than
fixed-constant adjustment at the source's illustrative inverse-k scales;
no final asymptotic repair is asserted. Source-only arithmetic concerns are
outside this review. Empty/ell=0 cases are valid extensions, not evidence
of a nontrivial cleaning endpoint.

Save exact six source hashes, independent scoped verdict, caveats and any
required fixes to review/dense-witness-review.json. No production edits,
new agents, compiler without owner coordination, or publication. Return
promptly after the bounded review.
