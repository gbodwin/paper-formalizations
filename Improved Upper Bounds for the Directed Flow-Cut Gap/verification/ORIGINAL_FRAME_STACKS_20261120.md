# Explicit row and sample stacks

`PaidVertexSampling.chooseRowsWithFrameStack` visits rows in the literal tape order. Each successful call saves its result and fee in an explicit stack, whose fold applies the previous price selection and fee update. `chooseRowsWithFrameStack_reference` proves equality of the entire prior measured result. In particular, the first minimum-price cut is retained and a failed suffix still accounts for all earlier work.

`PaidVertexAmplification.runWithPlanFrameStackWork` uses this row walk for each sample and folds an explicit sample stack. Lean proves equality with `runWithPlanRowWork`, including both counters. `vertex_terminal_frame_stack_reference` and `edge_terminal_frame_stack_reference` lift the equality to the original parsers and solver entry points.

`AmplificationFrameLayout` places the reached row frames before each successful sample's saved frame and restores the sample frames in fold order. A failed sample retains its reached row frames. `FramedStackReservationWork.vertex` and `.edge` bound the solver counters, the modeled data reservations, and the modeled stack reservations in the source length, numerical confidence degree, and the two initial address widths. The reservation model counts fresh cells without reclaiming them.

The executable fixtures cover two complete tied samples, failure at the first row and in the second sample, and both original three-bit sources. Structural bit time still requires list and frame operations outside this walk and the remaining payload-addressed memory operations.
