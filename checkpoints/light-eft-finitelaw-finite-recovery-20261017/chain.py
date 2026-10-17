"""One finite recovery pass and conditional checker only; no compiler/resolver."""
from pathlib import Path
import datetime
import json
import shutil
import traceback
import pilot_runner as p
import pid_observations as observations

B = Path(__file__).resolve().parent


def save(data):
    temp = B / 'chain-result.tmp'
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(B / 'chain-result.json')


def main():
    with (B / 'invocation-claimed.json').open('x') as f:
        json.dump({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'one_checker_only_attempt': True, 'one_finite_recovery_pass': True}, f)
    state = {'source_commit': p.SOURCE, 'base_evidence': 'd5798e2b3d8119651e351359f42062cd826e05f5',
             'stages': [], 'status': 'preparing', 'no_retries': True, 'recompiled': False, 'resolver_rerun': False}
    save(state)
    try:
        if p.PILOT.exists() or p.EVIDENCE.exists():
            raise RuntimeError('Fresh path collision; do not retry')
        p.PILOT.mkdir()
        shutil.copy2(p.ACCEPTED_RESOLUTION, p.RESOLUTION)
        state['pinned_objects_before'] = p.verify_pinned_object()
        state['singleton_inventory_before'] = p.verify_target_inventory()
        state['accepted_resolution_reverified'] = p.verify_accepted_bindings()
        state['status'] = 'running-replay'
        save(state)
        observations.snapshot('replay-before.json', admit=True)
        plan = {'stage': 'replay', 'source': str(p.PROJECT_SOURCE), 'argv': p.stage_argv('replay'),
                'env': p.environment('replay'), 'cwd': str(p.PILOT), 'inputs': None,
                'object_bindings': p.verify_pinned_object()}
        try:
            receipt = p._run(plan, p.PILOT, p.EVIDENCE / 'replay')
        finally:
            observations.snapshot('replay-after.json')
        raw = (p.EVIDENCE / 'replay/raw.log').read_text()
        if raw.strip() != 'replaying ' + p.MODULE:
            raise RuntimeError('Unexpected singleton replay output')
        state['stages'].append({'stage': 'replay', 'attempt_id': receipt['attempt_id'], 'exit': receipt['exit']})
        state['status'] = 'pinned-singleton-checker-passed'
        print('replay PASS', flush=True)
    except BaseException as exc:
        state.update(status='stopped-first-failure', failure=repr(exc))
        traceback.print_exc()
    finally:
        try:
            state['pinned_objects_after'] = p.verify_pinned_object()
            shutil.copy2(p.RESOLUTION, B / 'accepted-resolution-copy.json')
        except BaseException as exc:
            state.update(status='stopped-first-failure', preservation_failure=repr(exc))
        state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save(state)
    return 0 if state['status'] == 'pinned-singleton-checker-passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
