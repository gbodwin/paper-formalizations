# Source tables to integral cuts with a literal fair-bit tape

`EncodedSourceExecution` exposes mass and size modes for vertex and edge
cuts. The vertex path uses the existing source format. The edge path uses
the same table markers with a row-major square cost table. Both parsers
preserve stored rational padding on inputs produced by their encoders.
In the vertex path the actual binary fractional solver returns the covers
that feed rounding. `polynomialFromBinaryOutput_eq` gives exact equality
with the typed solver tree analyzed in the earlier certificates.

The four completeness theorems cover every tape of sufficient length.
They give the cut or infeasibility result, the exact number of random bits
read, and the original tape with that prefix removed. The decoded output
is valid. `EncodedSolverBits.amplifier_le_polynomial` bounds the number
of fair-bit reads using the displayed polynomial in graph dimensions,
stored field width, and confidence degree. The probability guarantees use
the fair-bit law with the proved bounded rejection default.

The execution fixture checks padded edge fields, rejection of a nonsquare
cost table, both source-to-cut paths, and a nonterminal fair-bit rejection
with a remaining suffix. The polynomial certificate charges random reads.
A finite-instruction implementation of the entire source-to-cut pipeline
and a polynomial bound for all of its deterministic bit operations remain
open.
