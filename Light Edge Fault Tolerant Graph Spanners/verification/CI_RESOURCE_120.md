# Resource-only CI successor

Exact Light229 commit 3076daee4e7d73e4a7e8a02f0a80f3ed4c57092d ended cancelled in run38301896259 on2026-10-12 at21:05:25UTC. Its clean build, strict stored sample/vote checks, module indexes and declaration audit passed, including2788 Light declarations. Kernel replay emitted332 ordered start markers out of367 expected;331 are followed by the next replay, while the last started StoredRecordMachine was interrupted. No full-CI pass is claimed.

The exact workflow has a60-minute job allowance. The job began20:05:10UTC; the log records cancellation and termination of leanchecker at21:05:25UTC. These facts strongly support a resource-cap explanation, but the available job log does not explicitly name the timeout cause. No proof error was observed before cancellation; that is not successful complete verification.

This successor changes only the job allowance from60 to120 minutes and adds this note. Every proof, source manifest, build/index/safety/fixture stage, sequential kernel replay and permission is retained byte-for-byte from exact Light244 parent c2968852fd003113e0d912e614f6985f6c91e5f8. Its existing run38305477187 remains separately in progress and cannot have its allowance changed in place. The original cancelled229 outcome is retained. The new successor requires its own terminal exact-commit CI.

The allowance provides room for the remaining sequential replays without omitting any stage or changing mathematical scope. The unpublished247 probabilistic-output bridge is not part of this resource-only successor.

Preserved complete229 job-log SHA-256: 83769280a03d9490272c69b989cca1e2fe0195fd42d5b3407c9f8675209b327d
