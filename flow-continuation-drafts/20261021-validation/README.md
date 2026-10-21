# Explicit 737-module validation candidate — NOT EXECUTED

This additive gate addresses the independent review in Library
`libfile_04290cf9f4f88191921f619476c74a77` (6050 bytes). The old audit remains
unchanged: its ten new modules / 732 total do not validate the 15-new-module
candidate. The unchanged baseline workflow alone also cannot accept it.

## Exact selection and evidence

`MODULES.json` binds 722 baseline modules from ea1dfba, 14 preserved ordinary
drafts from f853a31, and OriginalStoreCorrectness from 21cc8d6: exactly 737
distinct modules. Git SHA-256 source bindings and actual set equality are
checked, along with every transitive Flow import. No copied baseline or draft
is edited. The 696-module import closure is not used as the replay selection.

`validate.py` defaults to source-only checks. It generates an isolated overlay
from the pinned Git blobs, strictly compiles all 737 in dependency order with
one compiler/worker, runs fresh baseline and full-union audits, and explicitly
replays all 737 modules through leanchecker. Each command has a separate log;
receipts preserve exact source/runtime/object hashes, declaration inventories,
root lists, explicit module selections, exit codes and failed attempts.

`AuditBody.lean` audits every constant by its defining module, including private
and generated declarations. It rejects unsafe owned declarations and permits
only propext, Classical.choice and Quot.sound. Every constant owned by each of
the 15 new modules roots the full type/body dependency traversal, which also
rejects unsafe dependencies and every other axiom. Actual imported module sets
must match exactly. All four OriginalStoreCorrectness declarations are required
roots. The parser compares the emitted root set to the complete new ownership
inventory; matching only a count is insufficient. Fresh baseline attribution
must contain exactly 26,090 declarations, with every name and owner preserved in
the union. Any mismatch fails rather than silently revising the expected set.

The inherited degenerate physical, numerical-envelope, positive natural, and
positive physical fixtures are pinned and executed separately. Natural output
is never counted as physical coverage. A positive physical cap must be supplied
explicitly by the parent; no speculative default is supplied. Timeout or an
unavailable/failed fixture prevents gate success. No new physical original-store
parser fixture or raw-input preparation theorem is claimed by this change.

## Resource and CI guards

The existing workflow, reference hash checker, reference kernel checker, audit,
Lake configuration and Lean/mathlib manifests must remain byte-identical to the
baseline. The new manually dispatched `flow-737-validation.yml` is additive and
has no push or pull-request trigger. Its 240-minute cap is unchanged in strength.
The validator has a stricter 200-minute execution budget to leave setup/artifact
time, with 180-second compile, 300-second replay, 600-second audit and 120-second
fixture caps. It never auto-retries or expands these budgets. The physical
degenerate fixture runs via `--run all` and must emit all four named PASS lines;
positive physical and natural diagnostics require distinct terminal markers.

Execution requires a clean exact full Git commit, a successful baseline workflow
at that same SHA, the original baseline job's successful status, and an explicit
positive attempt cap. CI additionally requires the dispatched workflow SHA to
equal the supplied SHA. It restores only that commit's baseline Lake cache with
no fallback or compiler bootstrap; missing cache fails closed. The validator
ignores cached project objects and compiles the full Flow union afresh. Installed
dependency revisions and compiler version are checked; runtime bytes are hashed
before execution and checked afterward. A nonblocking compiler lock and process
inventory reject an occupied environment; all compiler subprocesses run
sequentially with Lean worker count one. Runner failures, including preflight
and lock rejection, produce receipts once a fresh valid output path is reserved.
Existing/unsafe destinations are never overwritten. An independent workflow
setup receipt records checkout, setup, cache and validation step outcomes even
if the runner never starts; full setup logs remain in GitHub's workflow log.
Runner logs and both kinds of receipts are uploaded on success or failure.

Success is labelled `gates_passed_pending_independent_review`, never acceptance.
The exact new CI run, artifacts, inherited baseline CI logs, and complete source
must receive sequential independent post-execution review before acceptance.
Setup/download/tool failures remain failures; no green baseline substitutes for
the additive gate. Standard usage/Fast off remains a parent/runtime requirement,
not a property this script can establish.

## Current status / deferred execution

Only Python syntax, source bindings, generated-audit structure and synthetic
fail-closed parser tests have run. No Lean compiler, kernel, push or CI has run.
The Lean audit and runner remain unexecuted source candidates and may require
repairs after authorized validation. No baseline or preserved draft is promoted.
Light EFT continues to own integration until the parent releases it. Do not
dispatch the workflow or invoke `--execute` before that release and approval.

Source-only check:

```
python3 flow-continuation-drafts/20261021-validation/validate.py
```

After approval, a fresh isolated environment with the pinned dependency cache
can run the same validator with `--execute --expected-commit FULL_SHA
--baseline-run-id RUN_ID --positive-attempt-cap APPROVED_CAP --output FRESH_PATH`.
FRESH_PATH must be outside the checkout. Preserve every receipt after repairs
and bind revised code to a new reviewed commit before retrying acceptance gates.
