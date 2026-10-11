# Actual self-delimited input-word reader

The fixed ten-slot program starts with an empty heap and caller stack. It requests a marker bit; true is followed by one data bit and a real recursive call, while false creates the nil terminator. Saved frames retain each data-cell pointer until the literal pair allocation on return, so the represented result has the original data order and all high-zero padding.

For the explicit well-formed source prefix encode(word), followed by any suffix, the same execution makes exactly the encoded request events, returns BoolList word, and retains the literal suffix. It performs6*stored_length+5 successful instructions and allocates3*stored_length+2 cells. The whole lower interpreter run, actual saved frames and one paid terminal halt fit200,000*(stored_length+1)^3. No preconstructed encoded size, word representation or Boolean-list packing routine supplies the result.

The encoding convention and valid-prefix hypothesis remain explicit. This theorem does not validate arbitrary graph input, replace the paper’s graph callback, or compile the entire graph/controller/packing algorithm. The full input format and composition with subsequent scans are separate steps.

Local strict compilation,50 new-declaration audit,5,392-constant exported type/body closure, four actual lower-interpreter fixtures and official replay passed. Independent source review is recorded separately. Every96 inherited proof source and workflow gate is retained. Fresh97-module production CI is required;the verified aggregate remains322.
