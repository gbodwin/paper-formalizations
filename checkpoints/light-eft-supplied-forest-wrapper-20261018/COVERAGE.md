# Positive and negative fixture boundaries

Run: python3 -B checkpoints/light-eft-supplied-forest-wrapper-20261018/test_wrapper.py.
Every run uses a new retained fixture directory. The fixed fixture_worker.py creates plaintext synthetic data and never invokes another tool or a Lean runtime. Private files named lock are fixture artifacts, never the universal lock. The production entry is not exercised.

| Boundary | Positive evidence | Negative evidence / tests |
| --- | --- | --- |
| Review and source authority | Real read-only 40029953 manifest, 10 supervisor hashes, 486 sources/pins, 196 objects; final implementation snapshots | input hash drift; symlink/hardlink rejection; manifest count/uniqueness/paths; 196 namespace counts; mutated commands; source/journal mismatch |
| Future production admission | Fresh-document pure fixture with matching owner/namespace/directory facts | missing production authority/fixture flag; wrong review reference, worker/reviewer/new-epoch declarations; stale owner/boot/namespace facts or time |
| Atomic new lease | Real O_EXCL/private-file flock; current FD/path matches | contention, existing lock, uncoordinated creator, symlink, racing competing file/symlink, path replacement; no adoption/truncation |
| Inherited description | Four-stage actual Python launcher FD and kernel-limit handshakes | each PID/PPID/SID/PGID/FD/device/inode/inheritability/start-time/limit mismatch |
| Whole-batch release | Same private inode across all stages; ECHILD release | live/unreaped kernel child delays release; sticky errors; unexpected descendant is killed/reaped; first failed compile fixture prevents later stages |
| Effective imports | Actual 196-object map and current search roots; synthetic exact map | missing/drifted dependencies, duplicate copies including nonproject modules, target sidecars and prefix siblings despite a singleton resolver count |
| Resolver/new object | New fixture object and exact official-schema target/object/search path | wrong count/target/path/root; changed object or resolution; missing source snapshot; tampered receipt environment and dependency set |
| Fresh capacity and limits | Same reviewed 3/4-GiB admission, resource limit readbacks and live sampling values | host/disk/visible headroom boundary, namespace/identity/limit/oom/pids changes, kernel readback mismatch, RSS/anonymous growth, partial telemetry, wall timestamps, decision-log cap |
| Scoped audit ownership | New-owner root plus imported project dependency in recursive closure | wrong owner/name/kind, omitted generated root, duplicate inventory, unsafe/partial/project axiom, strict findings |
| Exact imports and closure | New module + exact expected imports; reachable type/body/opaque chain | missing/extra/duplicate/aggregate import, dangling type/body link, orphan constant, truncated rows, missing inductive links |
| Dynamic audit counts | Counts and axioms recomputed from tables | changed roots/closure/opaque/axiom summary, duplicate summary, actual diagnostic warning; a hint merely containing “warning” is not double-counted |
| Audit write isolation | Audit exports under work/audit/ci-evidence; object/resolution protected independently | wrong export name, oversize file, live object/resolution mutation |
| Complete publication | All four tables + raw log and canonical input journal exported, chunks reconstruct byte-for-byte | missing/extra/altered/reordered/truncated/path-escaping chunks, wrong source/row contract |

Many rejection methods contain multiple named subcases; 114 is the number of recorded method/subcase results, not 114 independent compiler executions. No Lean compilation or kernel/audit execution has occurred. Test results establish only these Python wrapper/fixture behaviors.

The retained rejected-input fixtures deliberately include invalid symlinks, hardlinks, corrupted tables and synthetic .olean files. They are not accepted project objects. The publication manifest hashes symlink target text without following it; Git preserves these bytes/link texts, not historical fixture inode/link counts. Review these as test data rather than resolving their targets.
