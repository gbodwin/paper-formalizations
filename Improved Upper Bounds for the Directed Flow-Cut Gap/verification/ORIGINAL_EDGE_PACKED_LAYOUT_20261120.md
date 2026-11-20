# Packed array layout across the original edge solver

`LiteralRoundSchedule` records the typed rounding input and the starting tape of every attempted row across the actual samples. It records the failing attempt before stopping. The final optional suffix agrees with `PaidVertexAmplification.runWithPlanRowWork`, and the visit count is at most the number of samples times the number of rows in the terminal plan.

`FramedEdgeTrials.polynomial` bounds the actual shared trial count by a polynomial in the original source length plus the numerical confidence degree. It uses the serialized price table and line-graph input produced from the parsed source. `CutoffArrayStorage` models the mask arrays of the easy guards and the packed schedule of the reached hard guard. `RunnerCutoffStorage` follows the actual heavy-vertex reduction, port preparation and replica branch to identify the cutoff input. Zero objective skips the downstream cutoff.

`FramedEdgePackedLayout.polynomial` combines the original edge source arrays, line and terminal cache preparation, and the array schedules for all attempted rounds. `List.Forall₂` matches each schedule to the corresponding literal visit. The per-round schedule places the reached cutoff between the gadget arrays and any successful in-round mask projection. The theorem bounds modeled fresh cells, instructions, binary reservation accounting and in-block address widths for an arbitrary initial address.

The bounds concern the modeled reservations. They leave the full inner vertex preparation, list and stack allocation, payload-addressed execution, and final structural bit-time composition open. The existing paid solver comparisons, preserved-source checks, and positive fixtures remain in the workflow.

`OriginalEdgeRoundLayoutSmoke.lean` checks a failure in the last row of the second sample, two completed samples with an unread bit, accepted empty and trailing rejected original sources, and both easy cutoff masks.
