"""One finite sequential batch; final full verification gates all accepted results."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shutil
import signal
import traceback
import child_runner as child
from shared_preservation import Lease
from batch_context import Batch, B, R, PLAN, WORK, OUT


def save(data):
    temp = B / 'batch-result.tmp'
    with temp.open('w') as f:
        json.dump(data, f, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    temp.replace(B / 'batch-result.json')


def main():
    with (B / 'invocation-claimed.json').open('x') as f:
        json.dump({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'one_finite_batch_only': True}, f)
    state = {'source_commit': PLAN['source_commit'], 'base_evidence': PLAN['base_evidence'],
             'status': 'preparing', 'no_automatic_retry': True, 'provisional_modules': [],
             'accepted_modules': [], 'stages': [], 'final_full_verification_required': True}
    save(state)
    lease = Lease(B / 'batch-lock.json')
    ctx = None
    handlers = {}
    for sig in [signal.SIGTERM, signal.SIGINT, signal.SIGHUP]:
        handlers[sig] = signal.getsignal(sig)
        def interrupted(sig, frame):
            raise InterruptedError('Batch signal ' + str(sig))
        signal.signal(sig, interrupted)
    try:
        with lease as lock:
            try:
                ctx = Batch(lock, lease)
                observation = {}
                child.assert_idle('batch-before-full-verification', observation)
                state['initial_exclusion'] = observation
                state['status'] = 'full-initial-content-verification'
                save(state)
                print('Full initial content verification starting under shared lock', flush=True)
                ctx.initialize()
                state['canonical_inputs'] = ctx.input_ref
                print('Full initial content verification PASS: ' + str(ctx.input_ref['rows']) + ' bindings', flush=True)
                index = 0
                for row in PLAN['modules']:
                    module = row['module']
                    for stage in ['compile', 'resolve', 'replay']:
                        index += 1
                        state.update(status='running', current_module=module, current_stage=stage)
                        save(state)
                        if stage == 'compile':
                            ctx.object_path(module).parent.mkdir(parents=True, exist_ok=True)
                        folder = B / 'attempts' / ('%03d-%s-%s' % (index, module, stage))
                        plan = {'stage': stage, 'module': module, 'argv': ctx.argv(module, stage), 'env': ctx.environment(module, stage)}
                        try:
                            receipt = child.run_child(plan, WORK, folder, ctx)
                        except BaseException:
                            if (folder / 'receipt.json').exists():
                                failed = json.loads((folder / 'receipt.json').read_text())
                                state['stages'].append({'module': module, 'stage': stage, 'attempt_id': failed['attempt_id'],
                                                         'exit': failed.get('exit'), 'state': failed['state'], 'receipt': str((folder / 'receipt.json').relative_to(B))})
                            raise
                        raw = (folder / 'raw.log').read_text()
                        state['stages'].append({'module': module, 'stage': stage, 'attempt_id': receipt['attempt_id'],
                                                'exit': receipt['exit'], 'state': receipt['state'], 'receipt': str((folder / 'receipt.json').relative_to(B))})
                        if stage == 'compile':
                            parsed = re.findall(r"option 'arena_reserve': ([0-9]+) KiB", raw)
                            if parsed != ['131072']:
                                raise RuntimeError('Compiler allocator option confirmation missing')
                        elif stage == 'resolve':
                            ctx.verify_resolution(module)
                        elif raw.strip() != 'replaying ' + module:
                            raise RuntimeError('Unexpected singleton replay output')
                        print('%s %s PASS' % (module, stage), flush=True)
                        save(state)
                    state['provisional_modules'].append(module)
                    save(state)
                state['status'] = 'children-completed-awaiting-final-verification'
            except BaseException as exc:
                state.update(status='stopped-first-failure', failure=repr(exc))
                traceback.print_exc()
            finally:
                # No further child can start. Complete preservation under the
                # same lease even after a failed admission, child or signal.
                for sig in handlers:
                    signal.signal(sig, signal.SIG_IGN)
                print('Mandatory final full content verification starting; shared lock retained', flush=True)
                if ctx is not None and hasattr(ctx, 'frozen'):
                    try:
                        final = ctx.final_verify()
                        state['final_content_verification'] = final
                        if final['matching']:
                            state['accepted_modules'] = list(state['provisional_modules'])
                        else:
                            state.update(status='preservation-failed-no-results-accepted')
                    except BaseException as exc:
                        state.update(status='final-verification-failed-no-results-accepted', final_verification_failure=repr(exc))
                        traceback.print_exc()
                else:
                    state['final_verification_failure'] = 'No complete frozen input set initialized; no results accepted'
                if ctx is not None:
                    state['final_output_summary'] = ctx.output_summary()
                    state['partial_output_bindings'] = list(ctx.partial_outputs.values())
                save(state)
                print('Final full content verification ' + ('PASS' if state.get('final_content_verification', {}).get('matching') else 'FAILED'), flush=True)
        state['whole_batch_lock_released_after_verification'] = True
    finally:
        for sig, handler in handlers.items():
            signal.signal(sig, handler)
        state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        if len(state['accepted_modules']) == 20:
            state['status'] = 'twenty-module-batch-passed-final-preservation'
        state['skipped_modules'] = [x['module'] for x in PLAN['modules'] if x['module'] not in {s['module'] for s in state['stages']}]
        if OUT.exists():
            shutil.copytree(OUT, B / 'preserved-objects')
        if (WORK / 'resolutions').exists():
            shutil.copytree(WORK / 'resolutions', B / 'resolutions')
        save(state)
    return 0 if len(state['accepted_modules']) == 20 else 1


if __name__ == '__main__':
    raise SystemExit(main())
