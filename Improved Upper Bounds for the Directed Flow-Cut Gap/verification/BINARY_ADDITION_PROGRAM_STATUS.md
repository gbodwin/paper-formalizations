# Actual binary ripple-carry instruction program

The literal 64-slot table branches on both stored low bits and the incoming carry. It makes real recursive calls on the tails, saves the caller registers, then allocates the literal sum flag and pair. Empty-word carry branches execute the previously verified increment table with its old terminal slot replaced by a real return. A successful-stack-suffix theorem checks each actual instruction and justifies that concrete nested call.

The result is exactly BinaryArithmetic.add, including stored high-zero padding. The original two input representations remain in the same append-only heap, the source is unchanged, and the top entry creates and removes its own caller. Successful instructions are at most 12*(left_length+right_length+1), with at most 2*(left_length+right_length)+3 appended cells. The same lower bit interpreter preserves the output, real saved frames and source, and pays one final halt within completeBound(64,H,B,steps+1).

The representation premises, dense initial cursor and initial heap/word-width bounds remain explicit. The linear bound counts instructions and allocations; the lower bit-operation bound also pays heap copies, binary addresses and frames. This primitive does not assert native host timing, construct graph input, multiply binary words or replace the graph callback's abstract charge.

Local strict assembled compilation, 200 new-declaration allowed-axiom audit, exported type/body closures, fourteen actual lower-interpreter fixtures and both official new-module replays passed. The source-only review is recorded separately. All 97 inherited proof sources and every inherited workflow gate remain unchanged. Fresh 99-module production CI is required; the verified full aggregate remains 322.
