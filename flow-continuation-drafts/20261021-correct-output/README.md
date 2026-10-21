# Typed original-input output correctness — unverified source draft

This additive source-only patch composes the ordinary preserved store/dispatcher
draft at f853a31d941c5466647c14dca86e928164ca8c27 with the original solver
correctness theorem in baseline ea1dfba989c89eb8ceed693cdad42ba8d96584f5.
No Lean compilation, kernel replay, declaration audit, push or CI has run.

## Change

`OriginalStoreCorrectness.lean` defines `CorrectForInput` using the existing
`FractionalCoverRawGuesses.Correct`, without changing or weakening that predicate.
It proves, as a source draft, that this specification excludes `.invalid` and
joins the existing original-store run theorem to the existing semantic theorem.
The detailed theorem retains the exact same run witness, input representations,
ordered demand encoding, root identities, heap extension, terminal stop and
bound. The polynomial corollary likewise reuses one existing run witness.

The semantic covers clause includes the grid-list length, feasibility of every
returned state, and simultaneous factor-six cost/factor-twelve mass comparison
against every feasible real comparator. The mathematical correctness result is
inherited, not newly proved here. The advance is its explicit composition with
the physical output relation and typed-input construction.

`FinalDispatch.Output` encodes only the ordered state projection in the covers
branch. This suffices for the semantic specification, which ignores Result
operation counters. No executable output decoder or unique decoding theorem is
claimed. Preparation remains declared Boolean/list work, separate from the
physical dispatch run. Raw input parsing, a single finite-instruction preparation
trace, native execution time, rounding/weighted/edge outer composition and full
paper completion remain open.

## Provenance and preservation

All older sources, fixtures, evidence and workflows remain byte-for-byte intact.
The separately preserved f853a31 branch is not promoted to verified status.
Its notes report historical strict checks on dispatcher modules, but its store
modules remain unverified; absent historical local receipts are not recreated.
This patch changes no aggregate imports or accepted module index.

`SOURCE_BINDINGS.json` records all 696 transitively resolved Flow sources: 681
baseline, 14 preserved drafts, one new module. This is the new root's static
import closure, not a replacement for the accepted 722-source verification set.
Non-Flow dependencies remain pinned by the original Lean/mathlib manifests.
The Git bundle includes both the baseline-derived continuation branch and the
preserved f853a31 branch. For a future isolated build overlay, copy the 14 draft
module paths listed in the binding file and the one new module into the Flow
source directory; do not overwrite any baseline module or build over the
configured checkout. The binding records use repository-relative source paths.

## Proposed validation plan — pending parent approval

Do not execute this plan until the integration owner releases capacity and the
parent approves it. Maintain Standard usage/Fast off, one compiler process,
one Lean worker (`-j1`), and all inherited resource gates.

1. Freeze the exact prospective overlay and verify every source binding against
   its indicated Git commit. Preserve the existing 722-source acceptance set.
2. Strictly compile the 14 preserved drafts in dependency order, then the new
   module, with `-DautoImplicit=false -DwarningAsError=true`. Iterate only changed
   modules and affected dependencies; preserve every failure receipt.
3. Run the inherited dispatcher and original-store validation/fixtures without
   relabeling natural-reference checks as physical execution. Check zero,
   infeasible, positive covers and padded/duplicate-demand inputs. Test semantic
   specialization of both new theorems, including invalid exclusion and exact
   same-run/provenance fields.
4. Audit every owned declaration and its type/body dependency closure. Allow
   only propext, Classical.choice and Quot.sound; reject sorryAx/custom axioms.
   Replay the full relevant Lean kernel closure, including the new root and all
   preserved draft dependencies, while retaining the baseline's full gates.
5. Obtain sequential independent exact-source review after fixes and full local
   evidence. Only after parent integration coordination, push the reviewed exact
   candidate, run unchanged required CI (including the 240-minute cap), and
   preserve exact-commit results before any acceptance claim.

No companion site creation or publication is part of this checkpoint.
