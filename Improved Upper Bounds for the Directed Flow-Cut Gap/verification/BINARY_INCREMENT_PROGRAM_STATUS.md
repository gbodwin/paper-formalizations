# Concrete binary increment program

The fixed16-slot instruction table performs literal recursive carry propagation on an arbitrary represented Boolean word, including high-zero padding. The false-head case shares the old tail; carry recursion saves/restores actual caller frames. The top entry starts with no caller and makes its own. All source bits and earlier heap cells are retained.

The exact result is BinaryArithmetic.increment true word, with numeric value one above the input. Successful steps are at most8*stored_length+6 and allocated cells at most2*stored_length+3. Lower refinement retains the same result, caller effects and source, and pays the final halt.

PreparedBinaryIncrement constructs its own incoming representation and proves exact final heap size2*stored_length+1+cells(word), original-word preservation, and total declared preparation plus the actual lower run plus halt at most1,000,000*(stored_length+1)^3. This is polynomial in the stored length, not the represented integer.

All new proof bodies have local strict and official-replay gates, type/body safety audit and actual instruction fixtures. Fresh94-module production-import CI is required. All92 earlier proof bytes and every previous gate are retained. This checkpoint remains outside the frozen322 integration candidate.

Input construction still uses charged Boolean/list primitives; this primitive does not compile the graph/controller/packing algorithm or prove its complete physical runtime.
