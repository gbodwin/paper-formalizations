# Same-run replay handoff: source contract only

This contract is an unexecuted source proposal based on exact parent
`c9a15c129d210bbbdf008ab1653f333fcd228d7b`, tree
`dc641dccdf3187e41af990894f92721952290967`. It does not change a workflow,
specification binding, theorem, resource profile, publication ref or admission.
Current specifications deliberately lack the six new controls, so both data
entrypoints refuse before any metadata probe or artifact request. Source review
of this unit precedes any caller/binding integration. No component has been
imported, elaborated, compiled, run or tested on this worker.

## Preserved semantics

The source target manifest contains all 567 original invocations, in the original
five-library and C-locale filename order. Three contiguous batches contain 189
invocations each. The complete ordered-name SHA256 is
`aacaaa23315dda4923b1407fc1336bffc7feb541c392e5eb1fbd1e6de6a1ccda`.
Every target source Git blob OID must still match the actual event checkout.

The pinned Lean v4.34.0 source commit is
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. `LeanChecker.lean` discovers
all `.olean` names in its search path and expands each requested module prefix.
`Lean/Util/Path.lean` selects the first root that claims a module's namespace,
even before checking the requested leaf. The new probe uses those same APIs;
the importer checks the actual restored results. Merely finding a matching
filename in some later root is insufficient.

`Lean/Environment.lean` stores the import header in ModuleData. Module-system
imports load base/server/private parts, and the default private import mode can
also read an existing IR-signature/IR pair. A target loads available server and
private parts in the checker's original order. Orphan private data without a
server part and IR without an IR signature are not silently promoted into read
inputs. The contract records all five companions' presence or absence, derives
the required set for each use, rejects missing required parts and disagreement
between available compiled headers, and never infers proof acceptance from them.

## Producer capture and immutable bundle

`export_handoff` requires actual full-role CI identity, exact event HEAD,
source-bound controls in all five existing specs, pinned Lean/checker binaries,
the actual Lake environment and all nine clean pinned package source checkouts.
No caller-supplied graph or synthetic producer receipt is accepted as its input.
This initial format admits only the observed ordered default project/package
build roots and toolchain root. An unknown or empty root is an explicit bounded
format refusal before discovery, not proof that the original launcher was
invalid or authority to alter its environment. Actual layout remains a future
qualification input; a necessary alternate layout requires a source correction,
not silently broadening a cache scan or dropping a search-root claim.

HeaderProbe is a metadata program, not a kernel replay. The Python caller invokes
the exact Git-bound program with the pinned Lean binary. It reads serialized
headers without importing target environments, initializing target extensions,
executing target code or replaying declarations. It retains mapped regions until
output completion; memory/virtual-memory/page-cache cost is unmeasured. It has not
been elaborated, and source inspection cannot establish successful compilation.

Discovery is followed by an exact input snapshot and a second actual capture.
Sealing copies only the complete workflow-wide module closure and required
non-toolchain companions. A third actual capture, full companion census and
second input snapshot must agree. Snapshot records include stable file identity
and SHA256 and are preserved in at most 64-record metadata chunks. These are
observational correlations at an externally maintained no-writer boundary;
they are not proof of hostile-writer absence or a new lease.

Compiled payload is streamed with a 64-KiB read buffer into parts of at most
4 MiB. Individual large objects are split, not omitted. The proposed total
transfer ceiling is 1 GiB and JSON ceiling 16 MiB; exceeding them is a precise
format/footprint refusal requiring bounded redesign, not a platform capacity
claim or permission to trim the closure. Actual cardinality, bytes, RSS, page
cache and time are unknown. No whole `.lake` directory or historical cache is
captured. Fresh installed toolchain objects are hash-verified in place instead
of bundled. Every closure source is bound to observed bytes; project/package
sources additionally match exact current Git blobs and package pins.

## Actual same-run transport

`strict_download.cjs` uses the public API and exact package/lock bytes from
`actions/download-artifact@d3f86a106a0bac45b974a628896c90dbdf5c8093`,
with artifact SDK 2.3.2 and its locked integrity. The original action warns on a
digest mismatch. This wrapper requires the SDK to report `digestMismatch ===
false`, and requires client-observed artifact ID, attempt-specific name and
digest to match the producer outputs. It uses the existing current-run runtime
client with no token/findBy/cross-run override or new REST permission. It records
the actual resolved local SDK entry and loaded-code hashes; their immutability
is checked during transport. The locked dependency install is an ordinary CI
setup input, not authenticated build or cache provenance.

The future caller must install the exact locked runtime dependencies with scripts
disabled, invoke this source directly, and bind producer outputs through `needs`.
No Node or npm operation has occurred here. No `dist/index.js` from the copied
package is invoked. The copied original package scripts are not an instruction
to run them. SDK safe extraction and the SDK's compressed-digest implementation
remain dependencies of the pinned supported client, not a new handwritten ZIP
decoder or alternate-host route. Artifact bytes are not used as code.

The Python importer accepts only the wrapper's fixed fresh runner-temp record
and data directory for the actual current run/attempt/artifact ID. It checks the
real transport result before reading the manifest. It then authenticates the
manifest against the independent producer output, rejects unknown files, unsafe
paths, duplicate destinations and incomplete chunks, and verifies both part and
whole-object hashes before materialization. No transport field grants CI
authority merely by appearing in payload JSON.

## Per-batch restoration

Each actual reusable replay job must select only batch 1, 2 or 3 from the source
manifest. The shared artifact is the required union for the complete workflow;
each consumer restores only its 189 target expansions and transitive import
closure. It never restores an unrelated cache or substitutes producer artifacts
for focused-job native children. It verifies the needed fresh toolchain objects
in place and refuses to overwrite existing compiled project/package objects.

After restoration, actual header probes check exact effective object and source
resolution, target-prefix expansion, import flags and transitive closure against
the producer. Actual companion read sets and before/after snapshots must agree.
Success returns only `BATCH_OBJECTS_AND_METADATA_ONLY_NOT_REPLAY_ACCEPTANCE`.
The data contract emits no kernel-completion or final validation marker.
Partial objects, capture logs, failures and progress records are preserved.

## Caller integration required after independent source review

This checkpoint does not implement the following caller changes:

1. Keep the producer body, all native guards and corollary/audit checks. Insert
   export only after successful producers; upload only the sealed `bundle`, and
   always preserve its separate capture/failure evidence. Bind actual upload ID
   and digest, manifest SHA and producer run/attempt/source outputs.
2. Introduce three explicitly chained reusable replay jobs with the genuine
   `global_replay` role and actual reusable workflow identity. Retain workflow-
   wide `paper-formalizations-single-compiler` concurrency and 120-minute caps.
   Each batch requires a fresh ordinary pinned toolchain/package-source setup,
   not another 100-minute producer run or restored build cache.
3. Retain the original fresh UID/Bash/source/tool/environment launcher-admission
   boundaries before protected work. Metadata compilation also needs a reviewed
   invocation profile before any execution authorization. This data draft does
   not self-authorize a compiler or claim a CILease/resource-supervised global
   replay; the accepted global boundary was launcher-only.
4. Invoke Python as the actual main source under `-I -B` and an explicit fresh
   absent `-X pycache_prefix`. Bind all transport variables from actual producer
   outputs, preserve the strict SDK result and call the importer. Only then run
   each original pinned checker invocation sequentially for its source-bound
   batch. Emit a batch marker only after every invocation returns success.
5. Require all three disjoint ordered batch coverages, successful producer and
   fresh focused output at the same exact candidate before the 5-minute
   aggregate. Keep the fresh focused paid9/decoder4/bridge4/batch12 route intact.
   No historical/full-role substitute may satisfy focused inputs.
6. Preserve every one of the original 1041 logical source bindings and refresh
   the exact five-spec acyclic identity cascade after source review: independent
   paid/decoder, then canonical, bridge, and fair-bit batch. Update exact caller
   controls and role policy together. No such edit is included in this unit.

The cancelled run 40249904316/1 remains rejected: 165 replay starts do not prove
567 completions. Independent parent-reported corollary inspection verified 1790
manifest entries and seven genuine children with released/ECHILD lease. Its final
audit took 89.136620311 seconds under the unchanged 90-second cap, max wait4 RSS
4772200 KiB. This narrow margin is recorded without a future-robustness or current
capacity claim. Per-job caps and every genuine native child gate stay unchanged.
