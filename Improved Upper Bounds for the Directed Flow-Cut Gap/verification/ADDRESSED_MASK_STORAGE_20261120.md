# Binary mask indexes and addressed payload storage

`BinaryIndexList.checkedMask_value` returns the earlier ordered index list for
every retained mask. The list builder increments both the index and address as
binary words. `BinaryIndexList.list_values` verifies the links.
`BinaryIndexList.placed` verifies the two-cell reservations. The checked
decoder traverses the retained list and compares each index with the encoded
array length before returning a bounded cursor.
`BinaryIndexList.checkedMask_paid` bounds the recorded work by the length
and the bit width of the largest address and index.

`BinaryMaskProjections.core_value` and `fiber_value` preserve the original
mask and the entire legacy fee on all inputs. Each scan reads the mask and
label at every visited index, compares the encoded labels, and fills the
destination in order. The corresponding charged bounds include the list,
checks, measured index operations, binary comparisons and fee arithmetic.
The mask and label arrays use typed vector storage in this proof.

`BinaryPayloadStore` reserves a range by advancing its binary end address.
Each lookup compares encoded addresses and reads the whole stored bit word.
A write below the end shadows the old value and preserves all other
addresses. `BinaryPayloadBlockMove.run_preserves` reads an initialized
contiguous source and copies its words to a reserved range at or beyond the
end of the source in the same store. It leaves every address outside that destination intact,
including the source. `run_paid` counts the visited store, copied words,
bounds checks and increments, including when a lookup or write fails.

The executable fixture checks original port preparation at zero objective,
partial and empty replica fibers, an invalid index, and an initialized copy
with empty and padded words crossing a 101-bit address boundary. It also
checks that a missing source and a write at the first free address fail.

These results cover the projected mask routines and one addressed copy.
The complete original solver still needs payload and frame lowering and the
composition with the fixed-instruction addressed machine.
