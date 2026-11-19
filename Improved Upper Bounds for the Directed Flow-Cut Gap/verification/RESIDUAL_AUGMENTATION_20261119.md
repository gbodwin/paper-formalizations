# Residual path search and complete flow-table augmentation

`ResidualSearchProgram.physical_path` computes the Boolean residual matrix
from the stored signed amount and capacity table. The same 388-slot program
builds the retained search context with the returned matrix address and
executes the predecessor search. The complete support list, vertex words and
endpoint words are represented inputs. For distinct endpoints, Lean
identifies the returned nonempty list with the exact encoded edges of a
simple residual path. An empty list certifies the absence of such a path.

`ResidualUnitUpdateProgram.physical_unit` implements both signed unit moves,
including canonical zero through cancellation. `ResidualCellUpdateProgram`
tests both directions in the literal path list and applies the corresponding
updates. It reuses the capacity pointer. `ResidualTableUpdateProgram.physical_augment`
updates every amount in the supplied row and column orders. Its result is a
represented table for `Flow.augment` with canonical amounts, the original
capacity widths, and the same layout consumed by residual search.

Both stages preserve the input tape and heap prefix. Each proved charge
includes its terminal instruction. The table update bound uses the simple
path length bound and the sign-specific magnitude bounds from the original
capacities. The search takes polynomial time in the represented widths and
number of vertices, including membership scans of the complete support.

The fixtures cover a two-edge path, a saturated network, a remaining direct
arc, signed cancellation, carries and borrowing, and empty tables. The
two-edge augmentation checks the exact signed matrix and each original
capacity address. At this checkpoint the path-search program and the
augmentation program have separate entry points. The loop that passes the
actual returned path to augmentation, computes the terminal cut and
composes with the outer controller remains open.
