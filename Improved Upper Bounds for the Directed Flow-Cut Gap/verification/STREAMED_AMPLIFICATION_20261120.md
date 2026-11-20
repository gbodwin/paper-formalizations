# Stream the minimum and fees through amplification

`PaidVertexAmplification.runWithPlanStreamWork` follows the literal tape and computes each attempted sample once. A successful suffix contributes its best cut and total fee during the return from recursion. The price comparison preserves the first cut among equal prices. The resulting state carries the current winner and the two fee totals. Tape exhaustion retains all incurred fees and skips later samples and comparisons that require a complete walk.

`runWithPlanStreamWork_reference` preserves the full earlier paid result. `runWithPlanStreamWork_paid` bounds the new fee calculations using the number of samples and the bit width of the successful earlier phase fee. The original vertex and edge entries carry the same execution together with the earlier terminal, framing and edge boundary work. Their polynomial bounds use the literal source length and numerical confidence.

The synthetic fixture checks three successful samples and exhaustion at the third sample. The original vertex and edge fixtures preserve the unread tape and earlier phase fields. The trailing vertex source reaches only framing and parsing. These results describe recorded operations in the solvers. A complete structural bit-time bound remains open.
