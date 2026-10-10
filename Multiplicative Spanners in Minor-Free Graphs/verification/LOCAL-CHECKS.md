# Local verification method

Each Lean invocation uses the pinned Lean 4.34.0 executable, `-j1`, and
`-DautoImplicit=false`. Compilation is bounded by a per-module timeout and
uses the shared nonblocking flock. No lock is held while doing source or
Site work. Root coordinates courtesy handoffs to prevent starvation.

The local search path includes the already-built LightSpanners and
VFTSpanners foundations. All12 transitive project-source imports were
checked byte-identical to this checkpoint; see imported-source-hashes.json.
Exact-commit CI rebuilds from the repository sources rather than trusting
these shared output files.

All eight initial modules and the library root were recompiled with these
flags at the aggregate local gate. The all-declaration audit passed 90
declarations; the only permitted logical axioms are propext,
Classical.choice and Quot.sound. All eight modules subsequently passed
independent kernel replay in two bounded groups on 10 October 2026,
completed at 16:51:36 UTC. The separate semantic report covers the exact
source hashes of that eight-module checkpoint.

The first kernel-runner attempt lacked Lean on PATH and was repaired before
any replay was claimed. The successful logs are retained separately.

Actual browser visual QA of the owner-private Site stopped at unanticipated
identity-sharing consent, which was left unaccepted. Static file/link tests
and the slider/reset functional checks passed; no visual pass is claimed.

## Second checkpoint: seven additional modules

All 15 proof modules and the aggregate root compile. The all-declaration
audit now covers 151 declarations. The seven additions and the unchanged
borrowed `LightSpanners.EdgeSubdivision` module passed independent kernel
replay, and both changed library indexes passed on 10 October 2026 at
17:21:39 UTC. See `new-component-gates.log` and the separate hash-pinned
`new-components-review.json` semantic PASS report. Exact-commit CI for the
new checkpoint is a separate subsequent gate.

The first aggregate attempt encountered a missing local output directory.
Adding that namespace directory exposed Lean's namespace-level search-path
selection, so the byte-matched imported LightSpanners artifacts were copied
into the local build directory before rerunning the successful gate. No
shared proof sources or build artifacts were modified. The borrowed module
was then locally recompiled and independently replayed; exact CI rebuilds
all repository sources from scratch.

## Third component batch: normalization, padding and cluster simplicity

All20 modules and the root compile; the all-declaration audit passes216
declarations. Both changed module indexes pass. The five new modules and
five unchanged borrowed normalization modules passed kernel replay in two
bounded windows, completed17:56 UTC on10 October2026. Logs and exact
source hashes are included. The original15 source files remain byte-identical
to8954f54, whose full exact-commit CI passed at17:45:58.

Early draft errors were multiplication-order rewriting, implicit theorem
arguments, a walk-map lemma name and reducibility/decidable-instance alignment
in finite edge counts. These were fixed before the successful frozen gate.
The next full exact-commit CI and a distinct component review are separate
from these local checks. No whole-paper completion is claimed.
