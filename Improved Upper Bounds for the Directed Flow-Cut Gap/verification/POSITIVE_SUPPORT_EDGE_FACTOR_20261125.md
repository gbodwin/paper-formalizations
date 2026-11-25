# Exact edge-factor search on positive support

`RationalInstanceEdgeFactor.leastSupported_eq` proves that the reduced solver returns the existing exact integer factor for every rational input. The solver checks threshold demands on the original graph. Its candidate cuts use only actual arcs of positive weight. It retains their inclusion-minimal cut constraints and uses one price coordinate per positive-weight arc, as counted by `supportDimension_eq`.

Every feasible full-system counterprice restricts to a feasible counterprice on the support. Conversely, give each omitted arc a price of one plus the proposed factor times the weighted cost. Omitted arcs have zero actual weight, so this extension preserves the weighted cost. Any cut that includes an omitted arc then satisfies the normalized violation inequality automatically. The supported cuts satisfy it by the reduced system and nonnegativity of prices.

`RationalPrunedEdgeFamily.familyFor_reference` shows that using the reduced solver preserves the exact returned rational cut family. The horizon in terms of vertex count still requires the retained positive arc count to be at most the number of vertices. The exact factor search still enumerates cuts over the positive support.

The native fixture checks a four-vertex path whose zero-weight bridge must remain present when checking demands. It sees two price coordinates out of sixteen, two valid inclusion-minimal singleton cuts, and factor one. It also checks factor zero on empty support and exact factor two on the directed triangle.
