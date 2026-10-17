"""One offline reconciliation/export; never executes or retries Lean/checker."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import re
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    state = load(B / 'chain-result.json')
    assert state['status'] == 'stopped-first-failure' and state['no_retries'] and not state['recompiled']
    assert [x['stage'] for x in state['stages']] == ['resolve']
    assert state['pinned_objects_before'] == state['pinned_objects_after']
    obj = state['pinned_objects_after'][0]
    assert obj['sha256'] == '04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc'
    assert obj['bytes'] == 254600 and sha(Path(obj['path'])) == obj['sha256']
    expected = {x['path']: x for x in load(B / 'toolchain-object-advice.json')['files']}
    assert len(expected) == 12594 and sum(x['bytes'] for x in expected.values()) == 2212380925
    receipts = []
    stages = []
    streams = []
    for stage in ['resolve', 'replay']:
        E = B / 'evidence' / stage
        r = load(E / 'receipt.json')
        receipts.append(r)
        assert r['source_commit'] == '78cb40c7837db049d645d73696f2e0b724ce8a3b'
        assert r['all_descendants_gone'] and r['kernel_no_children_verified'] and r['direct_reaped']
        assert r['preserved_inputs_verified'] and not r['descendants_observed']
        assert r['object_bindings_before'] == r['output_inventory_after'] == [obj]
        assert (r['lock']['device'], r['lock']['inode']) == (33, 3849)
        assert r['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888],
                                           'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216],
                                           'RLIMIT_CORE': [0, 0]}
        assert r['memory_policy']['admission_visible_host_bytes'] == 3221225472
        assert r['memory_policy']['stop_visible_host_bytes'] == 1073741824
        assert r['memory_policy']['rss_observed_stop_bytes'] == 6442450944
        assert r['memory_policy']['per_cgroup_anon_growth_stop_bytes'] == 3221225472
        assert sha(E / 'submitted-source.txt') == r['submitted_source_sha256']
        assert (E / 'inputs-before.json').read_bytes() == (E / 'inputs-after.json').read_bytes()
        samples = [json.loads(x) for x in (E / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == r['latest_decision_sample']
        assert r['anonymous_preexec_baseline'] == {n['path']: n['memory_stat']['anon'] for n in r['preexec_admission']['nodes']}
        phases = {}
        for phase in ['before', 'after']:
            seen = set()
            with (E / ('hash-advice-' + phase + '.jsonl')).open() as f:
                for line in f:
                    x = json.loads(line)
                    assert not x.get('error') and not x.get('advice_error')
                    if x.get('advice_scope') == 'toolchain_immutable_object':
                        assert x['advised'] and x['path'] not in seen
                        seen.add(x['path'])
                        assert all(x[k] == expected[x['path']][k] for k in ['sha256', 'bytes', 'identity'])
            assert seen == set(expected)
            m = r['toolchain_verification_measurements'][phase]
            phases[phase] = {'files': len(seen), 'bytes': m['bytes'],
                              'visible_current_drop_bytes': m['visible_current_drop_bytes']}
        for name, item in r['completed_file_housekeeping'].items():
            file = Path(name)
            assert item['state'] == 'completed' and file.stat().st_size == item['bytes'] and sha(file) == item['sha256']
            assert item['identity'] == item['identity_after_advice']
        raw = (E / 'raw.log').read_text()
        warnings = len(re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M))
        assert warnings == 0
        post = [x for x in samples if x['sample_started_ns'] >= r['preexec_decision_sample']['sample_started_ns']]
        growth = {path: max(n['memory_stat']['anon'] - base for x in post for n in x['accounting']['nodes'] if n['path'] == path)
                  for path, base in r['anonymous_preexec_baseline'].items()}
        stages.append({'stage': stage, 'attempt_id': r['attempt_id'], 'created_utc': r['created_utc'],
                       'ended_utc': r['ended_utc'], 'child_pid': r['child_pid'], 'exit': r['exit'],
                       'supervised_state': r['state'], 'failure': r.get('failure'),
                       'argv': r['argv'], 'environment': r['environment'], 'handshake': r['handshake'],
                       'submitted_source_sha256': r['submitted_source_sha256'],
                       'admission_visible_bytes': r['admission']['headroom'],
                       'admission_host_bytes': r['admission']['system_available'],
                       'preexec_visible_bytes': r['preexec_admission']['headroom'],
                       'preexec_host_bytes': r['preexec_admission']['system_available'],
                       'sample_count': len(samples), 'first_sample_utc': samples[0]['sample_utc'],
                       'last_sample_utc': samples[-1]['sample_utc'],
                       'sampled_rss_peak_bytes': max(x['child'].get('rss') for x in samples if isinstance(x['child'].get('rss'), int)),
                       'wait4_maxrss_bytes': r['wait4_maxrss_kib'] * 1024,
                       'minimum_sampled_visible_headroom': min(x['accounting']['headroom'] for x in samples),
                       'maximum_sampled_anonymous_growth_by_group': growth,
                       'input_inventory_rows': len(load(E / 'inputs-before.json')),
                       'input_inventory_sha256': sha(E / 'inputs-before.json'),
                       'inventories_byte_identical': True, 'toolchain_advice': phases,
                       'terminal_confirmation': r.get('terminal_confirmation'),
                       'bounded_transition_used': r.get('exit_transition'), 'lean_warning_headers': warnings})
        streams += [(E / 'inputs-before.json', [E / 'inputs-before.json', E / 'inputs-after.json']),
                    (E / 'hash-advice-before.jsonl', [E / 'hash-advice-before.jsonl']),
                    (E / 'hash-advice-after.jsonl', [E / 'hash-advice-after.jsonl'])]
    resolver, checker = receipts
    assert resolver['state'] == 'finished' and resolver['exit'] == 0 and resolver['waitid_wait4_status_match']
    assert resolver['ended_ns'] < checker['lock']['acquired_ns']
    terminal = resolver['latest_decision_sample']
    assert terminal['exit_lifecycle']['terminal_confirmed'] and terminal['child']['rss'] is None and terminal['child']['vm'] is None
    assert terminal['exit_lifecycle']['confirmation'] == resolver['terminal_confirmation']
    (B / 'resolver-terminal-sample.json').write_text(json.dumps(terminal, indent=2) + '\n')
    assert checker['state'] == 'failed' and checker['exit'] == -9
    assert checker['stop_decision_errors'] == ["MemoryGuardError('Visible headroom below required floor')"]
    stop = checker['stop_decision_sample']
    assert stop == checker['latest_decision_sample'] and not stop['collection_errors']
    assert stop['accounting']['headroom'] == 1042374656 < 1073741824
    assert stop['child']['rss'] == 405020672 and stop['accounting']['system_available'] == 17625296896
    assert stop['sample_finished_ns'] <= checker['memory_stop_signal_started_ns'] <= checker['memory_stop_signal_finished_ns']
    assert checker['memory_stop_signal_sent'] and not stop['exit_lifecycle']['terminal_confirmed']
    (B / 'checker-stop-sample.json').write_text(json.dumps(stop, indent=2) + '\n')
    assert state['official_resolution'] == load(B / 'official-resolution.json')
    assert state['official_resolution']['resolved'] == [{'module': 'LightEFTSpanners.FiniteLaw', 'object': obj['path']}]
    assert state['official_resolution']['count'] == 1

    fixtures = load(B / 'focused-fixture-results-v2.json')['fixtures']
    assert len(fixtures) == 11 and all(x['fixture_passed'] for x in fixtures)
    fixture_receipts = []
    for entry in fixtures:
        file = B / entry['receipt']
        r = load(file)
        assert r['fixture_assertions_passed'] and r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
        assert r['exclusive_lock_verified'] and r['inherited_lock_verified']
        assert sha(file.parent / 'submitted-child.py') == r['submitted_source_sha256']
        for name, digest in r['submitted_sources'].items():
            assert sha(B / name) == digest
        if 'stop_decision_sample' in r:
            assert r['stop_decision_sample'] == json.loads((file.parent / 'samples.jsonl').read_text().splitlines()[-1])
        fixture_receipts.append(r)
    fixture_receipts.sort(key=lambda r: r['started_ns'])
    assert all(a['ended_ns'] < b['started_ns'] for a, b in zip(fixture_receipts, fixture_receipts[1:]))
    assert fixture_receipts[-1]['ended_ns'] < resolver['started_ns']
    old = list((B / 'focused-fixtures').glob('*/receipt.json'))
    assert len(old) == 1
    failed_fixture = load(old[0])
    assert failed_fixture['exit'] == 0 and failed_fixture['kernel_no_children_verified']
    for name, digest in failed_fixture['submitted_sources'].items():
        assert sha(B / 'fixture-development-failure-001' / name) == digest
    assert 'PermissionError' in (B / 'fixture-development-failure-001/focused-fixtures.log').read_text()

    chunks = B / 'chunks'
    chunks.mkdir(exist_ok=False)
    streams += [(B / 'toolchain-object-advice.json', [B / 'toolchain-object-advice.json'])]
    manifest = {'reconstruction': 'Concatenate listed part bytes without separators; each before/after input inventory pair is identical.', 'inventories': []}
    for file, targets in streams:
        folder = chunks / ('-'.join(file.relative_to(B).parts).replace('.', '-'))
        folder.mkdir()
        parts = []
        pending = bytearray()
        def flush():
            if pending:
                path = folder / ('part-%03d.txt' % len(parts))
                path.write_bytes(pending)
                parts.append({'path': str(path.relative_to(chunks)), 'bytes': len(pending), 'sha256': sha(path)})
                pending.clear()
        with file.open('rb') as f:
            for line in f:
                if len(pending) + len(line) > 200000:
                    flush()
                pending.extend(line)
        flush()
        digest = hashlib.sha256()
        for part in parts:
            digest.update((chunks / part['path']).read_bytes())
        assert digest.hexdigest() == sha(file)
        manifest['inventories'].append({'reconstructs': [str(x.relative_to(B)) for x in targets],
                                         'bytes': file.stat().st_size, 'sha256': sha(file), 'parts': parts})
    (chunks / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    active = [x for x in subprocess.check_output(['ps', '-eo', 'pid=,stat=,comm='], text=True).splitlines()
              if x.split()[-1] in ('lean', 'lake', 'leanchecker', 'strace', 'leantar') and not x.split()[1].startswith('Z')]
    assert not active
    with open('/tmp/distance-sparsification-single-compiler.lock') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'operation': 'offline evidence reconciliation only',
              'source_commit': state['source_commit'], 'recompiled': False, 'no_retries': True,
              'result': 'RESOLUTION_PASSED_CHECKER_STOPPED_BY_1GIB_VISIBLE_HEADROOM_GUARD',
              'stages': stages, 'pinned_objects': [obj], 'one_lock_inode': True, 'nonoverlap': True,
              'all_children_reaped': True, 'focused_fixtures_passed': 11, 'preserved_development_fixture_failures': 1,
              'kernel_replay_attempted': True, 'kernel_replay_passed': False, 'recursive_axiom_audits_this_attempt': 0,
              'checker_guard_shortfall_bytes': 1073741824 - stop['accounting']['headroom'],
              'actual_resolver_used_one_second_transition_wait': False,
              'actual_resolver_terminal_confirmation_before_missing_field_validation': True,
              'toolchain_advice_calls': 50376, 'new_history_passes': 0,
              'chunks': sum(len(x['parts']) for x in manifest['inventories']),
              'common_lock_free': True, 'active_compilers_tracers': active}
    (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('stages', 'pinned_objects')}, indent=2))


if __name__ == '__main__':
    main()
