# Qualification of the prior refusal report

The preserved refusal report at `checkpoints/light-eft-bounded-import-result-20261017/REPORT.md` says that inventory reads “increased file-cache accounting.” That causal wording was too strong: the prior refusal receipt did not include `memory.stat`. It recorded low headroom after hashing, but attributing the change specifically to file-cache growth was an **inference**, not a measured file-counter delta. The historical report and raw receipt remain unchanged; this note corrects their interpretation.

This new bounded advisory pass separately records parent/child `memory.stat` before and after, alongside usage, limits, OOM events, MemAvailable and process RSS. Its observed counter changes do not retroactively supply missing measurements for the prior attempt. A successful POSIX_FADV_DONTNEED return is not proof that any specified number of bytes was reclaimed.
