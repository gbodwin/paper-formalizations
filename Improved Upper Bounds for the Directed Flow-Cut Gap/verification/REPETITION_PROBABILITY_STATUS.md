# Unverified repeated-selector probability extension

EncodedRoundingProbability adds an exact tail-probability identity for the existing first-on-ties repeated selector: the selected record exceeds a natural threshold precisely with the (extra+1)-st power of the one-draw threshold probability. It works directly with PMF outer measures, including the infinite type of full output records and counters, and assumes neither finite support nor ideal uniform tapes.

The proof uses the existing sample-list projection and support-wise minimum event equivalence. No new executable sampler, selector, runtime charge or input conversion is introduced. A generic isolated PMF proof was compiled locally with warnings as errors; production exact-source build, strict compilation, exhaustive closure axiom audit and kernel replay are required here before acceptance.

This standalone extension is not imported by the251 aggregate root and does not alter its proof sources. The one-draw graph query quality theorem, finite-bit coupling and complete representation/runtime substitution remain open.
