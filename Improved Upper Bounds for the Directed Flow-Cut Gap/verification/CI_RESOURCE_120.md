# Preventive resource-only CI allowance

This successor changes only the job allowance from90 to120 minutes and adds this
note. Every source, manifest, strict compilation, actual-machine fixture,
axiom/type-body audit, module-index check and complete sequential kernel replay
is preserved from exact Flow283 parent55176ce2fd82c0cbbc81e082e4f87eecac1717cb.
No proof gate or permission is removed or weakened.

The fully verified230 baseline a452bbdb ran its230-source final kernel replay
from18:13:34 to18:45:37UTC on12October2026, about8.36 seconds per source. The
current269 run38303677729 passed all69 pre-replay stages and entered its final
269-source replay at21:03:45UTC, after42m18s of earlier gates. The same-rate
estimate is roughly80 minutes total against its90-minute allowance. The283
successor adds further strict/audit/fixture/replay work, reducing that margin.
These are transparent projections from actual timestamps, not a measured final
269/283 duration and not a claim that either run timed out.

At this snapshot both exact269 and283 CIs were still running. Their existing
allowances cannot be changed in place and their original outcomes remain
separate. A fresh exact-commit CI is required for this resource successor.
Full-CI success is not inferred from local tests or partial running jobs.
Raw input preparation, complete normalization/controller composition and the
adaptive outer packing runtime remain open. The change adds time, not proof
coverage or a mathematical correction.
