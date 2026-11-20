# Storage and widths in the cached packed controller

`CachedHeapCopies.append_copies` follows the three array pushes in the cached heap append. In the persistent-copy model, an append to a heap of size H performs 12H+23 array copy instructions and allocates 3H+11 fresh cells. `CachedHeapBuild.original_build` applies the same model to the original conversion from the reference heap. The model charges a fresh destination even when a particular allocator can reuse storage.

`PaidTotalRawGraphExecution.storage_traffic` follows the actual cached steps until halt or the first unavailable request. It uses the completed raw trace from the original graph theorem to bound the length of that prefix. `PaidCacheTrace.Walk.next_operands` bounds the binary widths of the actual indexes, counters and append charges in a completed step, and proves that its reads use the indexed branch. The proof of termination and the modeled storage traces carry no runtime fuel calculation.

`PackedStoragePolynomial.polynomial` bounds the sum of cache construction and guarded-run allocations and copies by fixed polynomials in graph dimension plus the numerical trial count. `combined_layout` derives the address width from the initial cell extent and the fresh-cell count. The initial extent includes the stored inputs and fixed empty-cache arrays. A native fixture checks the initial cache, both retained counters, the indexed lookup and the modeled block placements.

The complete source-to-cut bit-time proof still needs to compose these storage bounds with scalar control in the cache and with structural allocation, metadata and control elsewhere in the solver.
