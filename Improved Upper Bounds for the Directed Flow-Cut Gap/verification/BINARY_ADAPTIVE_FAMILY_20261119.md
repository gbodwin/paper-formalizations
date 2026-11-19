# Binary adaptive edge family

`BinaryEdgeFamilyCalibration.run` takes the original adjacency and stored
weight words. It computes the calibration parameters, the subunit gate and
horizon, and the original threshold demands. It calls the binary edge solver
on each actual adaptive query and keeps the updated rational price row.

`BinaryEdgeFamilyCalibration.calibrated_verified` joins validity of all
accepted cuts, the (1 - n^{-\kappa}) confidence guarantee, the original
weight frequency bound, the exact unread tape, and a polynomial in the
original dimension, stored weight width and numerical confidence for the
returned counters. Its horizon agrees with the existing
`RationalWeakFamily.edgeRounds` formula.

`BinaryEuclidean.gcd_value` and `gcd_paid` verify exact normalization by
binary division with input-width fuel. The adaptive query and advance
proofs identify the exact canonical prices and the exact accepted cut.
The same price row is used for the next query.

This result covers the calibrated explicit factor. The exact original-weight
flow-cut factor with a near-linear horizon has a separate scope. The cost
theorem uses the existing mixed operation model for graph and index
operations. The integer cutoff gate and physical source conversion
still have separate cost obligations.

The executed checks cover padded arithmetic, a zero numerator, two exact
nontrivial canonical price updates, five actual edge calls, and the
subunit family with no draws.
