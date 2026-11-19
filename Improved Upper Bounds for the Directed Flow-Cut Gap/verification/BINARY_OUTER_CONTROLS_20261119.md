# Binary outer controls and the accepted cut law

The original vertex and edge solver entries now obtain their draw budget,
amplification exponent and confidence through measured binary arithmetic.
The edge budget includes the logarithmic dimension used by the dyadic
gadget. Lean checks exact equality of the three values to those used in the
existing solver law. The executed branches share their control words, and
both original-input charge polynomials count the new preparation.

The new native checks cover zero dimension, a small positive dimension and
a 129-bit virtual dimension with an 81-bit confidence degree. Actual
original-wire invocations remain in the paired and source-readback gates.

For positive requested confidence, the weak-cut sampler's successful
results have positive probability. `SelectedWeakCutLaw.verified` defines
the normalized law induced by those exact results and verifies original
threshold coverage and the original-weight deletion bound.
