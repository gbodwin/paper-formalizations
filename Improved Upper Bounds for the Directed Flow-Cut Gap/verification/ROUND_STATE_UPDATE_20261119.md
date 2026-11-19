# Physical state update after a sampled cut

`RoundStateUpdateProgram.update_round_state` starts with the represented
retained mask pair, index spines for the selected demand, the sampled cut,
and the represented integer weights. The fixed reference interpreter
clears that demand, unions the sampled cut, and recomputes the mass on the
surviving demands and uncut vertices.

The returned pair holds the new masks and mass. Lean identifies the
remaining demand flags, cut flags and current mass with the corresponding
fields of `EncodedRoundingState.roundData`. The weights and scale remain
those of the caller. The previous heap is a prefix of the returned heap
and the routine generates no tape events. The exact execution bound
includes the paid terminal attempt and is polynomial in the graph dimension,
stored count width, and the initial heap and address bounds.

`RetainedDemandEraseProgram` copies the necessary prefixes and shares the
untouched suffixes. `FlattenDemandMaskProgram.flatten_value` proves alignment
with the mass table order. The mass programs use actual binary arithmetic
and trim each accumulated sum. They allow padded inputs and bound the
intermediate and result widths.

The combined interpreter fixture deletes one demand in a two-vertex graph,
unions the sampled cut and checks the resulting masks and mass against
`roundData`. The fixture executes 259 successful instructions and checks that
one more attempt is needed to stop. Smaller fixtures cover the two mask
operations, indexed replacement and binary mass sums.

The controller still needs fixed-instruction construction of the sampled
cut and the represented optimizer inputs, optimizer execution, and the
outer solver transformations. The library gate replays the entire package.
The additional gate strictly elaborates the eight modules and runs their
physical fixtures.
