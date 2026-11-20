# Binary fee accumulation through amplification

`PaidVertexAmplification.samplesWithCharges` charges the binary additions used to combine work on the literal tape. Each reached callback runs once. A failing call retains its charge and skips later calls. The value and prior paid fee agree with the earlier sample walk.

`runWithPlanScalarWork` keeps the actual sample walk and winner from the same amplification. It charges the outer binary sums and preserves the prior result and phase headers. The proved width bound uses the actual earlier fee. It applies to both successful execution and exhaustion.

The original vertex and edge entry points carry the additional charges through the measured terminal path. The vertex entry retains the earlier paid result and framing records. The edge entry preserves its result, phase headers, boundary fields and framing records, and adds the scalar work to the combined fee. Both bounds use the literal source length and numerical confidence. Inner price selection and full structural bit time remain separate obligations.

The core fixture preserved fees of 65,579 on success, 65,589 after a late failure, and 11 after an immediate failure. Both original 3-bit sources preserved their cuts and unread tapes and recorded 4,631 additional operations. A trailing vertex source retained the parser fee and incurred zero amplification work.
