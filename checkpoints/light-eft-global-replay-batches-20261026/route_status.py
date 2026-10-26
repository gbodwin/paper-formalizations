"""SOURCE ONLY: actual caller identities and serial coverage conjunction.

Not an invocation approval. All new controls must be Git-exact and bound in
every original specification before any operation. No resource/lease claim is
created by a status marker or by this source's environment observations.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import stat
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SPECS = ('light-eft-paid-focused-adapter-20261020',
         'light-eft-joint-flag-ci-extension-revision-20261019',
         'light-eft-canonical-output-adapter-20261020',
         'light-eft-paid-joint-bridge-ci-adapter-20261020',
         'light-eft-fair-bit-batch-ci-adapter-20261021')
NAMES = ('closure_contract.py', 'HeaderProbe.lean', 'targets.json',
         'strict_download.cjs', 'package.json', 'package-lock.json',
         'route_status.py', 'batch_runtime.py', 'runtime_sources.py',
         'batch_launcher.sh')
EXTRA = ('.github/workflows/lean.yml',
         '.github/workflows/light-eft-global-replay.yml',
         '.github/workflows/light-eft-fair-bit-focused.yml',
         'checkpoints/light-eft-sequential-validation-schedule-20261021/workflow_identity.py',
         'checkpoints/light-eft-sequential-validation-schedule-20261021/acceptance.py',
         'checkpoints/light-eft-canonical-output-adapter-20261020/ci_policy.py',
         'checkpoints/light-eft-replay-admission-plan-20261021/replay_preflight.py',
         'scripts/KernelCheck.sh', 'lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
LIMIT = 16 * 1024**2


def require(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key')
        result[key] = value
    return result


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def read(path):
    p = Path(path); s = p.lstat()
    require(stat.S_ISREG(s.st_mode) and s.st_size <= LIMIT, 'Unsafe/oversized record')
    return json.loads(p.read_bytes(), object_pairs_hook=unique)


def git(*args):
    return subprocess.run(['git', *args], cwd=ROOT, check=True,
                          capture_output=True, timeout=10).stdout


def source(rel):
    p = ROOT / rel
    require(not any(q.is_symlink() for q in [p, *p.parents]), 'Symlink source control')
    b = p.read_bytes()
    require(b == git('show', 'HEAD:' + rel), 'Source differs from actual HEAD: ' + rel)
    return dict(path=rel, bytes=len(b), sha256=hashlib.sha256(b).hexdigest())


def controls():
    paths = [p.relative_to(ROOT).as_posix() for p in [HERE / n for n in NAMES]] + list(EXTRA)
    rows = {rel: source(rel) for rel in paths}
    for name in SPECS:
        rel = 'checkpoints/' + name + '/ci-spec.json'
        source(rel)
        entries = read(ROOT / rel)['engine_files']
        require(len(entries) == len({r['path'] for r in entries}), 'Duplicate engine control')
        bound = {r['path']: r for r in entries}
        require(all(bound.get(k) == v for k, v in rows.items()),
                'Route controls not bound in every original specification')
    return rows


def identity(role):
    e = dict(os.environ); head = git('rev-parse', 'HEAD').decode().strip()
    require(e.get('GITHUB_ACTIONS') == 'true' and
            e.get('GITHUB_REPOSITORY') == 'gbodwin/paper-formalizations', 'Not project Actions')
    require(re.fullmatch('[0-9a-f]{40}', head) and
            e.get('GITHUB_SHA') == e.get('LIGHTEFT_EXPECTED_SOURCE', head) == head,
            'Actual checkout/event/source differs')
    require(all(re.fullmatch('[1-9][0-9]*', e.get(k, ''))
                for k in ['GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']), 'Invalid run/attempt')
    ref = e.get('GITHUB_REF', ''); repo = e['GITHUB_REPOSITORY']
    require(ref and ref != 'refs/heads/light-eft-spanners-checkpoints' and
            e.get('GITHUB_EVENT_NAME') in ['push', 'pull_request', 'workflow_dispatch'], 'Wrong trigger/ref')
    require(e.get('GITHUB_WORKFLOW') == 'Lean' and e.get('GITHUB_WORKFLOW_SHA') == head and
            e.get('GITHUB_WORKFLOW_REF') == repo + '/.github/workflows/lean.yml@' + ref,
            'Actual caller workflow differs')
    jobs = {'full': ('check', '.github/workflows/lean.yml'),
            'focused': ('check', '.github/workflows/light-eft-fair-bit-focused.yml'),
            'global_replay': ('check', '.github/workflows/light-eft-global-replay.yml'),
            'aggregate': ('acceptance', '.github/workflows/lean.yml')}
    require(role in jobs and e.get('GITHUB_JOB') == jobs[role][0], 'Wrong actual job')
    if role != 'aggregate':
        path = jobs[role][1]
        require(e.get('LEAN_NUM_THREADS') == '1' and e.get('LIGHTEFT_VALIDATION_ROLE') == role,
                'Wrong role/worker setting')
        require(e.get('LIGHTEFT_EXPECTED_SOURCE') == head and
                e.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY') == repo and
                e.get('LIGHTEFT_JOB_WORKFLOW_PATH') == path and
                e.get('LIGHTEFT_JOB_WORKFLOW_SHA') == head and
                e.get('LIGHTEFT_JOB_WORKFLOW_REF') in
                [repo + '/' + path + '@' + ref, repo + '/' + path + '@' + head],
                'Actual executing workflow differs')
    return dict(commit=head, repository=repo, ref=ref, run_id=e['GITHUB_RUN_ID'],
                run_attempt=e['GITHUB_RUN_ATTEMPT'], role=role, job=e['GITHUB_JOB'])


def contract():
    # Called only after controls(), including exact bytes of this dependency.
    spec = importlib.util.spec_from_file_location('_bound_replay_contract', HERE / 'closure_contract.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def handoff(ci):
    e = os.environ
    require(e.get('LIGHTEFT_HANDOFF_PRODUCER_SHA') == ci['commit'] and
            e.get('LIGHTEFT_HANDOFF_PRODUCER_RUN_ID') == ci['run_id'] and
            e.get('LIGHTEFT_HANDOFF_PRODUCER_RUN_ATTEMPT') == ci['run_attempt'],
            'Handoff is not this actual source/run/attempt')
    aid = e.get('LIGHTEFT_HANDOFF_ARTIFACT_ID', '')
    digest = e.get('LIGHTEFT_HANDOFF_ARTIFACT_DIGEST', '').removeprefix('sha256:')
    manifest = e.get('LIGHTEFT_HANDOFF_MANIFEST_SHA256', '')
    require(re.fullmatch('[1-9][0-9]*', aid) and re.fullmatch('[0-9a-f]{64}', digest) and
            re.fullmatch('[0-9a-f]{64}', manifest), 'Missing actual upload/manifest output')
    return dict(artifact_id=aid, artifact_digest=digest, manifest_sha256=manifest)


def validate_coverage(row, ci, number, binding, previous):
    require(isinstance(row, dict), 'Missing coverage marker')
    plan = read(HERE / 'targets.json')['batches'][number - 1]
    expected = dict(schema='LIGHT_COMPLETE_REPLAY_BATCH_V1', commit=ci['commit'],
                    repository=ci['repository'], run_id=ci['run_id'], run_attempt=ci['run_attempt'],
                    batch=number, offset=189 * (number - 1), count=189,
                    ordered_targets_sha256=plan['ordered_module_sha256'],
                    handoff=binding, previous_coverage_sha256=previous,
                    every_checker_exit_zero=True, fresh_process_count=189)
    require(set(row) == set(expected) | {'receipts_sha256', 'native_correlation_sha256'},
            'Unknown/incomplete coverage fields')
    require(all(row.get(k) == v for k, v in expected.items()) and
            all(re.fullmatch('[0-9a-f]{64}', row[k])
                for k in ['receipts_sha256', 'native_correlation_sha256']),
            'Coverage identity/order/results differ')
    return hashlib.sha256(encoded(row)).hexdigest()


def previous(ci, number, binding):
    raw = os.environ.get('LIGHTEFT_PREVIOUS_COVERAGE', '')
    sha = os.environ.get('LIGHTEFT_PREVIOUS_COVERAGE_SHA256', '')
    if number == 1:
        require(not raw and not sha, 'First batch cannot claim historical previous coverage')
        return ''
    row = json.loads(raw, object_pairs_hook=unique)
    # Earlier predecessor-chain completeness is also checked by final aggregate.
    prior = row.get('previous_coverage_sha256')
    require((number == 2 and prior == '') or
            (number == 3 and isinstance(prior, str) and re.fullmatch('[0-9a-f]{64}', prior)),
            'Previous chain field differs')
    actual = validate_coverage(row, ci, number - 1, binding, prior)
    require(actual == sha, 'Actual needs predecessor output hash differs')
    return sha


def output(values):
    with open(os.environ['GITHUB_OUTPUT'], 'a') as stream:
        for key, value in values.items():
            require('\n' not in str(value) and '\r' not in str(value), 'Unsafe output value')
            stream.write(key + '=' + str(value) + '\n')


def producer():
    controls(); ci = identity('full'); binding = handoff(ci)
    folder = Path(os.environ['RUNNER_TEMP']) / ('light-eft-replay-export-' + ci['run_id'] + '-' + ci['run_attempt'])
    summary = read(folder / 'export-summary.json'); result = read(folder / 'export-result.json')
    require(result['status'] == 'SEALED_OBJECT_HANDOFF_ONLY' and summary['target_count'] == 567 and
            summary['manifest_sha256'] == binding['manifest_sha256'] and
            hashlib.sha256((folder / 'bundle/manifest.json').read_bytes()).hexdigest() == binding['manifest_sha256'],
            'Export did not complete at this source')
    require(summary['producer'] == contract().identity('full'), 'Export identity differs')
    marker = dict(schema='LIGHT_PRODUCER_BODY_COMPLETE_NOT_FULL_ACCEPTANCE_V1', **ci, handoff=binding)
    output(dict(producer_commit=ci['commit'], producer_marker=encoded(marker).decode().strip()))


def aggregate():
    controls(); ci = identity('aggregate')
    folder = Path(os.environ['RUNNER_TEMP']) / ('light-eft-combined-acceptance-' + ci['run_id'] + '-' + ci['run_attempt'])
    folder.mkdir(mode=0o700, exist_ok=False)
    record = dict(accepted=False, CI_identity=ci)
    try:
        needs = json.loads(os.environ['LIGHTEFT_NEEDS_JSON'], object_pairs_hook=unique)
        record['needs'] = needs
        require(set(needs) == {'check', 'replay1', 'replay2', 'replay3', 'focused'}, 'All five mandatory jobs required')
        require(all(v['result'] == 'success' for v in needs.values()), 'Mandatory producer/replay/focused job failed')
        p = needs['check']['outputs']; marker = json.loads(p['producer_marker'], object_pairs_hook=unique)
        require(p['producer_commit'] == ci['commit'] and marker ==
                dict(schema='LIGHT_PRODUCER_BODY_COMPLETE_NOT_FULL_ACCEPTANCE_V1',
                     **{**ci, 'role': 'full', 'job': 'check'}, handoff=marker.get('handoff')),
                'Producer marker source/run/attempt differs')
        binding = marker['handoff']
        require(set(binding) == {'artifact_id', 'artifact_digest', 'manifest_sha256'} and
                re.fullmatch('[1-9][0-9]*', binding['artifact_id']) and
                all(re.fullmatch('[0-9a-f]{64}', binding[k]) for k in ['artifact_digest', 'manifest_sha256']),
                'Malformed producer artifact binding')
        last = ''
        for number in [1, 2, 3]:
            out = needs['replay' + str(number)]['outputs']
            require(out['validated_commit'] == ci['commit'], 'Replay source differs')
            row = json.loads(out['coverage'], object_pairs_hook=unique)
            last = validate_coverage(row, ci, number, binding, last)
            require(last == out['coverage_sha256'], 'Replay coverage hash differs')
        require(needs['focused']['outputs']['validated_commit'] == ci['commit'], 'Fresh focused source marker missing')
        record.update(accepted=True, all_567_ordered_checker_successes_required=True,
                      full_producer_and_fresh_focused_required=True,
                      qualification='Job-status/output conjunction; complete raw artifacts and independent review still required')
    except BaseException as error:
        record['failure'] = repr(error)
        raise
    finally:
        contract().create(folder / 'result.json', encoded(record))


def main():
    require(sys.flags.isolated and sys.dont_write_bytecode, 'Require Python -I -B')
    require(len(sys.argv) == 2, 'One finite status mode required')
    if sys.argv[1] == 'producer':
        producer()
    elif sys.argv[1] == 'aggregate':
        aggregate()
    elif sys.argv[1] == 'source':
        controls(); identity('global_replay')
        require(not os.path.lexists(ROOT / '.lake'), 'Replay requires a fresh absent .lake tree')
    else:
        raise ValueError('Unknown status mode')


if __name__ == '__main__':
    main()
