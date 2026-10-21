# Ideal flat tape to the accepted joint source

This source-only mathematical checkpoint starts from accepted commit
`c1aaa0a00c0c943cec4b2753a937023e9884db04`, ordinary CI run 39507492456
attempt 1, and its independently accepted supplied-response ideal-law bridge.
It adds one staged Lean module and changes no accepted source, gate, workflow,
resource limit or evidence. Fast mode is off. No compiler, resolution, replay,
audit, admission attempt, push or CI launch is part of this checkpoint.

The new module defines a finite-vector tape `Fin N → Bool`, where
`N = l.length * card J * m * card (Sym2 (Fin n))`. Positions are mapped
bijectively to the exact accepted `samplingSchedule`: tail-first candidate
occurrence positions, then hosts, repetitions and original-edge identities.
The forward coordinate map is literally the schedule's `List.get`. Its inverse
is a mathematical equivalence, not a paid index lookup or enumerator.

The new claims are:

1. The finite-vector/occurrence tensor correspondence is a bijection, with each
   scheduled cell reading its exact flat position. Distinct candidate positions
   remain distinct even when their edge keys coincide.
2. An **independently defined literal product law** of biased Boolean cells on
   that vector pushes forward to the accepted `jointSourceLaw`. The proof
   reindexes the mass product and then the probability sum; it does not infer
   independence from marginal biases or from the supplied-response model.
3. Applying the accepted supplied-response interpretation to this reindexed
   **ideal** tape inherits the accepted assignment event probability law.

Empty dimensions need no special positivity assumption or division by tape
length. The coordinate/list bijection uses the already accepted nodup and
exhaustive schedule lemmas; finite products and sums include their empty cases.
The edge universe is unchanged, including diagonal identities and identities
outside the particular input graph. No candidate keys are deduplicated.

Status: ten theorem bodies, four noncomputable definitions and one type
abbreviation are new and **unelaborated**. The source argument and primary lemma
statements have been inspected by the author; parent sequential independent
mathematical/source review is next. Hash checks are source preservation evidence,
not kernel acceptance. The expected project import set has 81 existing modules,
82 including this target, derived from the accepted bridge closure. Official
resolution and object provenance are not established by that source count.

See `PROOF-ARGUMENT.md` for the derivation and `UNRESOLVED.md` for remaining
generation, probability-realization, representation and cost obligations.
`SOURCE-BINDINGS.json` binds all new checkpoint files except itself, the 81
accepted project source imports, the accepted bridge specification and pinned
primary theorem sources. It is a source-review inventory, never a runtime input
manifest or an execution plan.
