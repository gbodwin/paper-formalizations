# Frozen contract review scope

This checklist records source-inspection obligations, not executed tests or
successful Lean elaboration. No workflow or existing specification is edited.
The current exact parent is c9a15c129d210bbbdf008ab1653f333fcd228d7b.

## Authority and inputs

- Follow `identity`, `controls` and `runtime` before either public entrypoint.
  The six new controls must be current-Git-exact and present in every old spec.
  On the current parent they are absent, so invocation refuses. An API call with
  supplied graph JSON is not an exporter entrypoint.
- Follow `strict_download.cjs` from actual role/source checks through the
  current-run SDK listing, exact ID/name/digest match, real download, positive
  digest result and transport-record write. No `findBy`, alternate run/token or
  externally supplied download receipt is accepted. The local SDK path/version,
  lock integrity and loaded source hashes must agree.
- Follow Python `transport` before manifest parsing. The fixed record is an
  owned 0600 single-link file in its fresh 0700 per-run/attempt/artifact domain.
  Manifest SHA, artifact digest and producer source/run/attempt come from future
  caller outputs, not payload claims. Exact caller wiring remains to be reviewed.

## Serialized closure and companion cases

- HeaderProbe uses pinned `findOLean`, `searchModuleNameOfFileName`,
  `findAllWithExt`, `findLean` and `readModuleDataParts`. It does not call
  `importModules`, initialize target extensions or replay declarations.
- Review base/server/private agreement, including the private-only orphan case.
  The import list preserves order and the public/meta/import-all flags. A ref
  retains compacted regions through output; no unsafe manual free is authored.
- Review module-system imports requiring three parts, target-only available
  companion prefixes, IR signature/IR pairing, and explicitly unused companions.
  `required_suffixes` derives the set from loader semantics and each selected
  batch's actual seed/import roles. Zero-byte source/SDK files are allowed;
  zero-byte compiled parts are rejected.
- Review missing dependency, duplicate node, cyclic import and hidden reachable
  node cases. All 567 original ordered invocation names and source OIDs remain
  bound. Per-batch closure derives from its fixed contiguous 189 names, never
  from an ad hoc user-selected subset or historical successful partial.
- Review same-prefix objects in multiple roots and nested target-prefix objects.
  Effective namespace selection and target expansion must match actual restored
  observations. A matching leaf in a later root is insufficient.

## Byte transport and restoration

- Derive `expected_file_set` independently from headers and the explicit five-
  companion availability map. File-list self-consistency alone is insufficient.
  Missing/extra companions, duplicate destinations and unknown stream fields fail.
- Every part name is deterministic, safe and unique. Chunks are at most 4 MiB,
  transferred via a 64-KiB buffer. Verify per-part and whole-object hashes before
  writes and reject all unlisted entries. Toolchain bytes are not copied.
- Verify fresh exact project/package/toolchain sources and pinned package heads.
  Consumer writes only its selected batch closure, uses exclusive regular-file
  creation, and never overwrites existing compiled files. Check actual installed
  toolchain companions in place against observed producer bytes.
- After restoration, compare actual namespace and source resolution, target
  prefix expansion, complete selected graph and import flags. Derive actual
  companion read sets again so fresh extra/missing parts cannot change semantics.

## Correlation, errors and boundaries

- Producer discovery, confirmed and sealed probes are actual serial calls, not
  fabricated receipts. Bracket them and copying with file identity/SHA snapshots,
  complete optional-part presence and namespace observations. Preserve snapshots
  in 64-record chunks. Confirm source/control/runtime identity again at the end.
- Consumer correlates the transport record, sources, parts and installed objects
  before writes; re-probes actual restored headers twice; checks all observed
  required bytes, presence and input snapshots afterward. No hostile-writer
  defense or absence of arbitrary processes is inferred from these correlations.
- Preserve partial files, metadata stdout/stderr, capture failures, progress and
  results. No success marker is emitted on timeout, missing source, digest error,
  changed input or partial restore. The only success status is metadata/object
  readiness, never replay/proof acceptance.
- All code, probe, compiler, Node/npm, transport and test execution remains
  unperformed. Limits in this format are proposed bounds, not measured fit.
  The retained mapped-region/graph footprint is explicitly unmeasured.
- Caller integration must retain original genuine admission/resource/CILease
  boundaries, one compiler and global serialization, all 1041 source bindings,
  the complete 567 fresh checker calls, fresh focused native producers and batch,
  and unchanged 120-minute execution/5-minute aggregate caps. Independent source
  review must precede that integration; no current native route is qualified.

## Upstream records

Lean 4.34 commit293d5d0c0c3f3dded4688b3ccd6a33939ac5102b supplied exact
LeanChecker/Environment/Path source. Download action commit
d3f86a106a0bac45b974a628896c90dbdf5c8093 supplied the exact package and lock
bytes and the SDK call/return shape; artifact2.3.2 integrity remains locked.
The copied package scripts have not run. Future runtime installation uses the
exact lock with scripts disabled, not an unpinned package download.

The independent parent-reported corollary audit passed its original native
checks, with 89.136620311s/90s and max wait4 RSS4772200KiB. It does not establish
robustness, memory recovery, all567 replay success or whole-paper acceptance.
