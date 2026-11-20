# Binary control of line-graph preparation

The shared batch fills an array in index order and records each callback fee during the same execution. `BinaryVertexReductionArithmetic.batch_reference` preserves the complete result and earlier fee. The bounded scalar work includes decoding the cursor, advancing it and adding the fees. The storage model follows the array pushes and bounds the persistent copies and binary reservations.

`BinaryLineLabels.prepareWithControl` records nested batch work and the reached reads of line labels, original adjacency and original prices. `prepare_reference` preserves the earlier result and charge. `prepare_control_polynomial` bounds the additional scalar work in the original dimension. `prepare_arrays` certifies the modeled storage of the labels, each inner adjacency row, the outer adjacency array and the price array.

The fixtures cover empty, singleton and nine-entry batches and the original line preparation with ordered and repeated demands. The two-vertex case retains the earlier fee of 5,591 and records 160,297 additional operations. The existing positive original edge fixture still selects the same edge and retains the same unread tape.

The array model describes persistent copies. Full source-to-cut bit time still requires accounting for the remaining graph transformations, list and frame storage, rounding and selection.
