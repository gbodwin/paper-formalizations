# Materialize the epoch input from the fair tape

The fixed 401-slot program filters the row-major pair list using the stored
active mask. It executes the guarded fair draws, permutes the actual active
list, and assigns the remaining grid words to that list in original label
order. The cell table and permutation both retain the original pair pointers.

`PhysicalEpochInputProgram.physical_epoch_input` identifies the exact order,
the value of each original-label grid draw, and the unread suffix of the
retained sampler. It bounds modeled operations including tape guards and
halt. `PhysicalEpochInputProgram.physical_epoch_rejected` gives the exact
short-tape failure. The inputs include the represented mask, row-major
pair list, positive grid word and unary guard length.

The positive fixture reverses `[(0, 1), (1, 0)]`, keeps grid cells two and one
on the corresponding original labels, and consumes seven bits. It runs
679 successful instructions and pays 3,154,566 modeled operations including
guard checks and halt. Separate fixtures cover short tape, zero trials,
and an empty active set. The smaller materialization fixture also exercises
a three-cycle permutation and a padded grid word.
