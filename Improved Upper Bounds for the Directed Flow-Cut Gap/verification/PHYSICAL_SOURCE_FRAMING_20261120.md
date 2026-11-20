# Physical source framing and edge composition

`OriginalSourceFraming.readBinary` executes a fixed instruction program that retains the three original raw tables in one bit-addressed heap. It counts length, fuel and source requests with binary arithmetic. The request count rejects truncation even when the reference machine reads its default false bit beyond the end. The framing proof retains the unused literal suffix and bounds the modeled work on every input. It preserves the stored padding and the order of all table fields.

`OriginalSourceFraming.original_tables` identifies the retained heap with the original parser’s table result. `PhysicalSourceInputJoin` reads each field through its stored address and uses the existing vertex and edge validators. Lean proves agreement with both original typed parsers, including rejection of trailing bits and invalid payloads.

`FramedDirectEdgeWire.edge_result` identifies the full result with the direct binary edge solver for every source, tape and rounding mode. `FramedDirectEdgeWire.complete` gives the same cut validity and literal tape-suffix guarantee under the existing sufficient-tape bound. `FramedDirectEdgeWire.recorded_polynomial` bounds parsing, dispatch, readback, rounding and selection on successful runs by a polynomial in source length plus the numerical confidence degree. The bound includes some structural word charges after framing. The full width-sensitive bit-time proof remains open.

The executable fixture uses the original 44-bit positive edge wire, exercises all forty-four proper truncations, and checks the selected arc and unread tape. It also exercises rejection of trailing source data, a padded zero denominator and an invalid matrix row.
