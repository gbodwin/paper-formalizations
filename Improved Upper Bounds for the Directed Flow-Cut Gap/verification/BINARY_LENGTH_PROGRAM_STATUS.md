# Concrete stored-word binary length scan

The fixed24-slot program initializes its own empty binary counter, traverses the actual input spine and calls the literal binary increment body once for each pair cell. Every padding bit is counted. Saved caller registers retain the tail pointer across the arithmetic call; no host list length computes the returned word.

The exact final represented word is countWord(length,[]), and its decoded value is the actual stored input length. The input representation, old heap and external source are retained. Explicit successful-step and append-cell recurrences have quadratic upper bounds in stored input length. The same lower interpreter executes the entire scan, calls and allocations, with a single paid final halt.

PreparedBinaryLength constructs the initial word and discharges all representation, dense-cursor, entry and stack premises. Its declared setup plus actual lower run plus halt is at most15,000,000*(stored_length+1)^6. This deliberately coarse polynomial is not a near-linear machine-runtime assertion.

Local strict compilation,88 new-declaration audit, both full type/body closures, four actual lower-interpreter fixtures and two official kernel replays passed. Independent source review also passed. All94 previous proof sources and inherited workflow gates remain unchanged; fresh96-module production CI is required. This component remains outside the verified322 aggregate.

Initial Boolean-list packing, addition/multiplication for the budget expression, whole graph/controller/packing instruction compilation and complete physical runtime remain separate.
