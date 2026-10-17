"""One resolver then singleton checker chain against the pinned accepted object."""
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
                   'one_resolver_checker_chain': True, 'no_recompile': True}, f)
    state = {'source_commit': p.SOURCE, 'base_evidence': '5e10ed3e9cfaa2b10a4126a30d6b2ec643534a6a',
             'stages': [], 'status': 'preparing', 'no_retries': True, 'recompiled': False}
    save(state)
    try:
        if p.PILOT.exists() or p.EVIDENCE.exists():
            raise RuntimeError('Fresh work/evidence path collision; no retry')
        p.PILOT.mkdir()
        state['pinned_objects_before'] = p.verify_pinned_object()
        state['singleton_inventory_before'] = p.verify_target_inventory()
        save(state)
        for stage in ['resolve', 'replay']:
            state['status'] = 'running-' + stage
            save(state)
            observations.snapshot(stage + '-before.json', admit=True)
            source = p.RESOLVER if stage == 'resolve' else p.PROJECT_SOURCE
            plan = {'stage': stage, 'source': str(source), 'argv': p.stage_argv(stage),
                    'env': p.environment(stage), 'cwd': str(p.PILOT), 'inputs': None,
                    'object_bindings': p.verify_pinned_object()}
            try:
                receipt = p._run(plan, p.PILOT, p.EVIDENCE / stage)
            finally:
                observations.snapshot(stage + '-after.json')
            state['stages'].append({'stage': stage, 'attempt_id': receipt['attempt_id'],
                                     'exit': receipt['exit'], 'receipt': str((p.EVIDENCE / stage / 'receipt.json').relative_to(B))})
            if stage == 'resolve':
                state['official_resolution'] = p.verify_resolution()
            if stage == 'replay':
                raw = (p.EVIDENCE / stage / 'raw.log').read_text()
                if raw.strip() != 'replaying ' + p.MODULE:
                    raise RuntimeError('Unexpected singleton replay output')
            save(state)
            print(stage + ' PASS', flush=True)
        state['status'] = 'pinned-resolver-singleton-replay-passed'
    except BaseException as exc:
        state.update(status='stopped-first-failure', failure=repr(exc))
        traceback.print_exc()
    finally:
        state['pinned_objects_after'] = p.verify_pinned_object()
        if p.RESOLUTION.exists():
            shutil.copy2(p.RESOLUTION, B / 'official-resolution.json')
        state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save(state)
    return 0 if state['status'] == 'pinned-resolver-singleton-replay-passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
