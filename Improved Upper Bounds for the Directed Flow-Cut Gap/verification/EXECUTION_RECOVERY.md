# Pending execution recovery

This candidate preserves the exact 174 component sources from commit
38949686912c514a50e2569fae79f57ec55513c0. That commit passed its full clean build,
module indexes, exhaustive axiom audit of 11,053 owned flow-cut declarations,
and all 174 component kernel replays in run 37992257057.

The combined binary-cover execution test had no recorded successful terminal
result. This candidate adds that unchanged set of concrete checks to CI, with
a ten-minute step deadline and progress messages before and after each case.
The first recovery candidate added only diagnostic output to the test. The
subsequent test-only compilation repairs are described below; all inputs,
mathematical comparisons and charge bounds remain unchanged. A completed proof-library CI result alone does not imply
that this separate execution test passed.

This remains a partial, pending candidate until its exact-commit CI and final
source/semantic reconciliation pass. The full paper's algorithmic runtime and
probability composition remain incomplete.

## First diagnostic result and test repair

Run 38009978711 passed the build, module indexes and declaration axiom audit,
then found two test-harness compilation issues before the sixteen-case loop:
`Finset.toList` is noncomputable, and a field-projection lambda needed its
`BinaryRational.Fraction` type annotation. The stopped-state case passed.

The repaired serializer enumerates the membership bit for every index in
`Fin m`, so it compares each chosen finite subset extensionally and remains
fully executable. The remaining raw numeric fields, event order, inputs,
expected outputs and charge/stopping assertions are unchanged. This is a test
repair, with no paper statement or proof-source change. The rerun is pending.
