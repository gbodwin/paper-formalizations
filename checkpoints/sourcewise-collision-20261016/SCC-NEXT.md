# Proposed SCC lifting contracts — unproved

The new DAG theorem is available uniformly for arbitrary finite vertex types. To discharge the general sourcewise premise, the remaining work should establish:

1. The equivalence relation `u ~ v` given by reachability in both directions, including reflexivity via nil walks. Its finite quotient has at most n vertices, including the n=0 case.
2. Quotient arcs between distinct classes are witnessed by original input arcs. Define the ambient quotient simple graph independently from the orientation, and prove the selected quotient relation is acyclic by lifting any supposed directed cycle to mutual reachability.
3. Each component admits internal in/out trees on its vertex subtype, supported only on original arcs within that component. Prove all internal pairs are reachable in their union and the union cardinality is at most twice the component size. Sum over components to obtain at most 2*n internal arcs.
4. Quotient sources and demands are finite images, not indexed copies counted with multiplicity. Prove their cardinalities do not exceed original |S| and |P| and all quotient demand sources lie in the quotient source set. Demands with equal classes use the internal witness; no quotient self-loop is required.
5. Apply the DAG sourcewise theorem. Choose one original-arc representative for each selected quotient arc. Its image cardinality is at most the number of selected quotient arcs. Lift quotient walks by joining these representatives using the internal component witnesses, including original demand endpoints.
6. Union lifted representatives and internal witnesses. Prove actual original input-arc containment and reachability equivalence. Transfer the square-root bound using quotient cardinality monotonicity. A coarse uniform constant 4 is a target suggested by adding the 2*n internal budget to the proved DAG constant 2; it is not yet a formal theorem.

Apply the resulting arbitrary-orientation theorem again to the reverse orientation. Do not substitute the weighted-distance preserver bound, assume the SCC trees, or expose the lifting witness as a premise of the final result.
