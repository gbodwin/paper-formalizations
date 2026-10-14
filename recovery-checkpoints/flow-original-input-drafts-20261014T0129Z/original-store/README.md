# Original Flow store construction: UNVERIFIED additive draft

Prepared 2026-10-14. **No Lean compilation, elaboration, kernel replay, smoke test, or axiom audit has run for this draft.** No existing published or reconstructed source was modified. Nothing was published.

## Intended result

`OriginalStoreInitial.prepare` takes the original typed adjacency matrix, padded rational cost row, and ordered list of `Fin n` demand pairs. It computes literal endpoint words, builds all three roots in one append-only physical heap, and installs the initial state at dispatcher entry 13318. There is no externally supplied represented-root witness, dense-cursor witness, empty-stack witness, H, or B in its proposed readiness theorem.

Let:

- `n` be the original vertex count;
- `d` be the original number of demand occurrences;
- `S` be `LambdaRowProgram.rowBits costs.toList`, counting every stored numerator/denominator bit, including padding;
- `D` be the total length of the generated source and target endpoint words;
- `L = 3 + 6*n + 2*S + 2*n*n + 4*d + 2*D`.

The draft gives exact initial heap length `L`, exact empty-stack record count `H = L+1`, and a conservative reference-word width bound `B = L`. It does not claim that `L` is the least possible width bound.

Packing and register/cursor installation have proposed charge at most `64*L^3 + 24*L + 37`. The original-input wrapper adds all declared typed-view/label charges and 16 for its outer record assembly, yielding `64*L^3 + 24*L + 53 + viewCharge`.

The proposed final theorem adds that preparation charge to the same reconstructed final dispatcher's physical run and terminal attempt. It uses a fixed polynomial in `N = n + d + S + 1`, with `L ≤ 32*N^2` and diagonal majorant `32*N^2 + 2*N + 2`.

## Files and smallest interfaces

1. `DirectedFlowCutGap/OriginalStoreInputViews.lean`
   - `advance`: actual repeated calls to the published Boolean increment body, with structural natural-index recursion and a declared cost.
   - `advance_label`: equality to the exact `RowVertices.vertexLabel` word, not just equality of decoded values.
   - `demandFields_exact` / `demandFields_charge`: original list order and endpoint-generation charge.
   - `costFields` and `matrixFields`: typed input views and explicit structural allowances.
2. `DirectedFlowCutGap/PackedOriginalStore.lean`
   - `tableInto_spec`: seed a new word-pair table inside an existing bounded constructor state. Reuses the published `prepend` body without changing it.
   - `matrixInto_spec`: append the pointer spine required by `GraphAdjacencyProgram.Matrix`, using the published `word` and `allocate` bodies.
   - `table_demands`: proof-only extraction of `DemandList` occurrence/record witnesses and `Forall₂` encoding from the packed word-pair table.
   - `construct_spec`: common-heap representations, exact cell count and root-width bounds.
   - `prepare_spec`: paid `copyRegisters` and `copyBits` installation, explicit H/B, stack, cursor and pc.
3. `DirectedFlowCutGap/OriginalStoreInitial.lean`
   - `prepare_spec`: supplies all dispatcher input premises directly from original typed inputs.
   - `heapCells_exact`, `heapCells_bound`: exact stored-size accounting and the quadratic majorant.
4. `DirectedFlowCutGap/OriginalStoreDispatch.lean`
   - `solve_original_bit`: preserves original input roots, demand encoding, output representation, source/stack/cursor, extension, and paid terminal stop while adding construction charge.
   - `solve_original_polynomial_bit`: fixed-polynomial bound for that same run, with no represented-store/H/B input premises.

## Scope boundaries that must remain visible

- This is a **Boolean/list constructor and declared cost model**. Packing is not represented as a `Run` of the 13,320-instruction dispatcher or any newly certified finite-instruction parser.
- Original inputs are already typed `Vector`/`Fin` values. Acquisition, serialization parsing, malformed external byte handling, and proving that raw numeric indices inhabit `Fin n` remain outside this interface.
- Label construction explicitly executes Boolean increment. Its natural recursion counter comes from the supplied typed index; this is not a binary-input parser.
- `costFields` and `matrixFields` use declared structural list/record allowances, in the same kind of typed-view model used by published `RowInputBudgets.prepare`. These allowances are not a finite-instruction trace or a measured/native-time certificate for Lean's `Vector.toList` implementation.
- The original cost words are never normalized, shortened, or replaced by their values. The matrix stores every supplied Boolean cell. Labels agree literally with the dispatcher's labels.
- Natural demand occurrence/record addresses are theorem witnesses. No executable constructor decodes a word with `value` to compute a fresh address.
- The demand theorem preserves original order and multiplicity. It does not separately state `Nodup` of occurrence addresses.
- The existing dispatcher `Output` encodes only the ordered **state projection** in the covers branch, not every field of the richer high-level Result records.
- The preparation charge is added to the physical dispatch charge. It is not asserted to be one physical finite-instruction execution from raw external data.
- There is no host runtime or whole-paper completion claim.

## Dependencies and static inspection

The foundational constructor and representation sources were read from the recovered exact722 tree. The dispatcher and its polynomial envelope were read from newly reconstructed draft trees; they are not recovered published artifacts, and their own validation status is separate.

`SOURCE_BINDINGS.json` records a static import-resolution snapshot and SHA-256 hashes for the four new modules and their resolved Flow source dependencies. It is source binding, not a compiler or kernel receipt. Rebuild it if any dependency changes before authorized validation.

Static inspection found no missing `DirectedFlowCutGap` imports and no `sorry`, `admit`, `axiom`, or `unsafe` tokens in these four modules. A separate static reviewer checked the arithmetic and identified the need for `noncomputable section` around polynomial definitions; that correction was made. These checks do not establish elaboration or soundness.

## Required next validation, only after separate authorization

1. Freeze the exact published source/dependency hashes and the reconstructed dispatcher/envelope artifacts that passed their own strict gates.
2. Add these four modules to an isolated build tree in dependency order: InputViews, PackedOriginalStore, OriginalStoreInitial, OriginalStoreDispatch.
3. Run strict elaboration, kernel replay, theorem smoke checks, and a fresh-baseline-attributed axiom audit under the parent's exclusive compiler protocol.
4. Fix any elaboration or proof failures in this additive draft; then rerun every affected gate before reporting a verified advance.
5. Preserve the scope boundaries above in any eventual progress report or repository commit.
