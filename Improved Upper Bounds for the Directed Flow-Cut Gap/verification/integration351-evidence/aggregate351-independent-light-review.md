# Flow351 independent integration-preservation review

2026-10-11 20:18 UTC. PASS for the exact frozen integration candidate.
Reviewer: concurrently active Light EFT owner. No child, Lean compiler, fixture
execution or kernel replay was used by this review. Fresh aggregate351 CI is
still required; this is not a full-paper semantic audit or runtime completion.

## Exact binding and independent checks

Packet SHA256 64b275e6021d2be5f549b6d958d7a5b8b13cbea3d1a8b01d28ff41f4bfb6a806.
Payload SHA256 4b7549e2a4ef2df213aa5b101b2559c933a1dfbab644611dc693cced3f1934f7.
Provenance SHA256 75286f070abb3ac126b5ec5d32d6a0e77a5767aacff19ed1aaf3db9de0301302.

I fetched the recursive remote Git trees for baseline322
9dc489c1dc68c02a49c52eab25060a921ae837bc and admitted111
b1894edaff36b5ec02c957d8fb049cc037f90e6c, both untruncated. I independently
computed Git blob IDs from each local byte sequence, rather than trusting only
the author's SHA256 manifest. All322 baseline proof files are exact; all111
admitted closure sources match the component's remote blobs. The82 shared sources
are identical and the29 genuinely new sources are byte-identical to the admitted
component. The351 root is precisely the sorted import list. All456 declared
file hashes, all351 module hashes and all95 payload contents match the stage.

564 present baseline blobs match their remote Git IDs. One historical metadata
file, integration284-provenance.json, is absent from the local staging copy; it
is not a payload path and remains in the verified baseline tree used as
base_tree_sha. No deletion is requested, so it is preserved remotely. This is
not a proof or publication blocker; final remote readback should preserve it.

I independently reran all six Python snapshot/source-closure checks. They pass.
The integration-preservation checker and its output are saved alongside this
report. No static check is being represented as a Lean build.

## Gate preservation

All129 previous strict targets remain among158. The official replay target list
contains every351 leaf and the exact root. The baseline KernelCheck.sh,
ExactFlowCutRootReplay.lean, StrictDirectedFlowCutGap.sh, AxiomAudit.lean,
CheckModuleIndex.sh and pathwise support-signature file are byte-identical.
The latter still checks all fifteen support helpers, full_support, pathwise_bound
and finite_source_support. The original graph bodies and all baseline regression
suites remain covered by the unchanged workflow segment and drivers.

The new workflow consists exactly of the old workflow, the29 admitted component
strict/safety/fixture stages and its source-closure checker, with the job timeout
increased from120 to180 minutes. Removing that insertion and restoring120 gives
the exact baseline workflow bytes. All copied machine gate/fixture files match
the full111 component's remote blobs, including the repaired prefix fixture
SHA256 93cb3fc1fd3cda7c261041212549c56210256fd1dfc199bb4eac280430fe43a6.
Only declared module-count/status literals change in the four snapshot scripts.
No assertion, source, replay or audit driver was removed or replaced by a cache.
The documented resource extension is reasonable and is not a weakening of checks.

I independently queried GitHub run38168074255 and job114554702137. They bind to
f7254ff6df6feb1a05284b39a2eb500a79cd0c06 and all50 job steps report success,
completed20:03:33. This admits the111 component only; it does not establish a
351-module clean build or full aggregate replay. The latter remains pending.

## Provenance and mathematical scope

All29 additions have source hashes appearing in retained independent semantic
review or exact production-binding records. Those records are byte-identical to
the supplied evidence. I read the critical multiplication, computed-budget-prefix
and selected-denominator source-review records and compared their explicit
contracts with the candidate README/provenance. No integration claim expands
those contracts.

The actual instruction primitives include arithmetic, encoded-source readers,
row/table/index construction, original-order output, computed-budget prefix
materialization and a selected-denominator zero flag. Valid encodings, in-range
indexes and sufficient source suffix are still explicit. The zero flag is not
a global graph-input rejection branch. The old abstract graph-read charge7 is
unchanged; these variable-cost readers do not silently discharge it. The candidate
retains graph parameter extraction, complete input validation, rational/graph
callback substitution, graph/controller/packing instruction composition, fuel,
selected-output joins and the full physical-runtime theorem as open.

Thus this packet may be published as an UNVERIFIED351 integration candidate and
run through its complete CI. It is not a verified aggregate until that terminal
run passes, and it carries no full-paper completion or research-website linking
claim. No required repair was found in the frozen95-file payload.
