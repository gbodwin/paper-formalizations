# Original-graph controller and literal fair tape

The 26,259-slot program in `OriginalGraphControllerProgram` starts with adjacency rows and canonical vertex-count and grid words. It builds the original vertex and pair dictionaries, computes the demand mask with unit-cost shortest paths, and constructs the uniform weight rows, empty cut, unit scale and exact current mass. It computes the initial optimizer family and then runs the same guarded controller for repeated stabilization and epochs.

`physical_original` proves the correspondence to the literal-tape model, with an explicit instruction limit, charged halt, exact unread suffix and heap extension. It also proves rejection for every interpreter limit and initial charge when the model cannot read the required bits. The entry reads the restart ratio, sampler budget, epoch budget and restart budget from stored controls.

`OriginalGraphControllerLaw` instantiates the restart ratio and the epoch and restart budgets with the paper's integer parameters. It proves the exact ideal cut law, the exact finite fair-input law for bounded rejection sampling, completion with enough bits, support validity, and an additive event-error bound.

The executed fixtures use an original directed path at two adjacent thresholds and a complete loopless two-vertex graph. They check the unreachable pairs, the threshold equality boundary, shared uniform rows, the computed optimizer, and the zero-optimum termination of the joined guarded program with positive control budgets. At that entry, the three-bit tape survives intact. The preceding live-epoch fixture starts with a represented cache and exercises drawing, selecting, cutting, and refreshing.

The next runtime obligation is to derive the stored controls and an original-input polynomial charge, then join the graph and weighted reductions and the amplified output selection.
