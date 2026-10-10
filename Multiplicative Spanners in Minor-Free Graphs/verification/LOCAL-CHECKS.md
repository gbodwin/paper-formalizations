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

Minor and Greedy were initially compiled before adding the explicit
-DautoImplicit=false flag. They must be rechecked with that flag in the
aggregate local gate before being recorded as fully locally passed.

Aggregate recheck completed 2026-10-10 16:40 UTC: all eight modules and root passed with -DautoImplicit=false; all90 declarations passed permitted-axiom audit.
