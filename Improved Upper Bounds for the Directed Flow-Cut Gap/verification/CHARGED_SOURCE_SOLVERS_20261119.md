# Charged source solvers and fair-tape execution

[PhysicalSolverCharges](../DirectedFlowCutGap/PhysicalSolverCharges.lean)
parses the original graph, runs the physical dispatcher once, and uses its
terminal rows to solve the cut problem. The result carries the number of
fair bits read, the unread suffix, and three modeled charges. The edge
entry constructs and serializes the typed line graph. Both entries
canonicalize endpoint labels. Vertex rational fields retain their padding.

The three charges measure the paid physical prefix, the reference lookups
used to read the terminal heap, and the binary sampler's word generation,
comparisons, and trial counters. The cached pointer reader reuses the
dispatcher store. Lean proves equality with the sequential binary-pointer
reader for both the returned plan and its exact charge.

Both size and mass modes return valid results on every sufficiently long
tape for parse-accepted input. The projection onto the output and unused
tape agrees with the existing bounded solver for every literal tape.
The vertex and edge fair-tape theorems also identify the law of these
actual runs on independent fair bits with the established amplified law.

[PhysicalSolverChargeBounds](../DirectedFlowCutGap/PhysicalSolverChargeBounds.lean)
bounds the physical and lookup charges in the original vertex dimensions,
the count of demands, and the stored rational field lengths or decoded edge
field width. The sampler charge has its own polynomial bound. The proof of
total deterministic bit cost still needs to account for typed parsing and
input preparation, row conversion, rounding and candidate selection,
storage and address operations, and final output.

The short fixture checks a padded vertex input and an original edge
input through the actual charged solvers. The long fixture uses the
actual positive physical dispatcher output for both rounding modes. It
also reads the terminal store with the cached pointer reader and feeds
that plan to the binary sampler used by the charged entry.
