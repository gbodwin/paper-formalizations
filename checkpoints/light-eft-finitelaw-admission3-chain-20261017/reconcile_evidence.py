"""Reconcile/export completed evidence only; no Lean, retry, or cache advice."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import re

B = Path(__file__).resolve().parent
R = B.parents[1]
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    state = load(B / 'chain-result.json')
    assert state['status'] == 'stopped-first-failure' and state['no_retries']
    assert [s['stage'] for s in state['stages']] == ['compile']
    assert not (B / 'evidence/replay').exists()
    expected = {x['path']: x for x in load(B / 'toolchain-object-advice.json')['files']}
    assert len(expected) == 12594 and sum(x['bytes'] for x in expected.values()) == 2212380925
    rows = []
    files_to_export = []
    receipts = []
    for stage in ['compile', 'resolve']:
        E = B / 'evidence' / stage
        r = load(E / 'receipt.json')
        receipts.append(r)
        assert r['source_commit'] == SOURCE and r['exit'] == 0
        assert r['kernel_no_children_verified'] and r['all_descendants_gone'] and r['direct_reaped']
        assert r['preserved_inputs_verified'] and not r['descendants_observed']
        assert r['memory_policy']['admission_visible_host_bytes'] == 3221225472
        assert r['memory_policy']['stop_visible_host_bytes'] == 1073741824
        assert r['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888],
                                           'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216],
                                           'RLIMIT_CORE': [0, 0]}
        assert (r['handshake']['lock_device'], r['handshake']['lock_inode']) == (33, 3849)
        assert r['handshake']['lock_inheritable'] and r['handshake']['pid'] == r['child_pid']
        assert sha(E / 'submitted-source.txt') == r['submitted_source_sha256']
        samples = [json.loads(x) for x in (E / 'samples.jsonl').read_text().splitlines()]
        assert r['latest_decision_sample'] == samples[-1]
        assert r['preexec_admission'] == r['preexec_decision_sample']['accounting']
        assert r['anonymous_preexec_baseline'] == {n['path']: n['memory_stat']['anon'] for n in r['preexec_admission']['nodes']}
        assert (E / 'inputs-before.json').read_bytes() == (E / 'inputs-after.json').read_bytes()
        for filename, item in r['completed_file_housekeeping'].items():
            path = Path(filename)
            assert item['state'] == 'completed' and path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
            assert item['identity'] == item['identity_after_advice']
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
            assert m['count'] == 12594 and m['bytes'] == 2212380925
            phases[phase] = {'verified_objects': len(seen), 'verified_bytes': m['bytes'],
                              'visible_current_drop_bytes': m['visible_current_drop_bytes'],
                              'visible_stat_deltas': {k: m['after']['nodes'][0]['memory_stat'][k] - m['before']['nodes'][0]['memory_stat'][k]
                                                      for k in ['anon', 'file', 'kernel']}}
        post = [s for s in samples if s['sample_started_ns'] >= r['preexec_decision_sample']['sample_started_ns']]
        anon_growth = {path: max(n['memory_stat']['anon'] - baseline for s in post for n in s['accounting']['nodes'] if n['path'] == path)
                       for path, baseline in r['anonymous_preexec_baseline'].items()}
        raw = (E / 'raw.log').read_text()
        warnings = re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.MULTILINE)
        assert not warnings
        rows.append({'stage': stage, 'attempt_id': r['attempt_id'], 'created_utc': r['created_utc'],
                     'ended_utc': r['ended_utc'], 'child_pid': r['child_pid'], 'child_exit': r['exit'],
                     'supervised_state': r['state'], 'failure': r.get('failure'),
                     'argv': r['argv'], 'environment': r['environment'],
                     'source_sha256': r['submitted_source_sha256'], 'source_bound': True,
                     'child_limit_and_lock_readbacks_verified': True,
                     'admission_visible_bytes': r['admission']['headroom'],
                     'admission_host_bytes': r['admission']['system_available'],
                     'preexec_visible_bytes': r['preexec_admission']['headroom'],
                     'preexec_host_bytes': r['preexec_admission']['system_available'],
                     'sample_count': len(samples), 'first_sample_utc': samples[0]['sample_utc'],
                     'last_sample_utc': samples[-1]['sample_utc'],
                     'sampled_rss_peak_bytes': max(s['child'].get('rss') or 0 for s in samples),
                     'wait4_maxrss_bytes': r['wait4_maxrss_kib'] * 1024,
                     'minimum_observed_visible_headroom': min(s['accounting']['headroom'] for s in samples),
                     'maximum_observed_anon_growth_per_visible_group': anon_growth,
                     'input_inventory_rows': len(load(E / 'inputs-before.json')),
                     'input_inventory_sha256': sha(E / 'inputs-before.json'),
                     'input_inventories_byte_identical': True, 'kernel_echild_verified': True,
                     'toolchain_advice': phases, 'lean_warning_headers': len(warnings)})
        files_to_export += [(E / 'inputs-before.json', [E / 'inputs-before.json', E / 'inputs-after.json']),
                            (E / 'hash-advice-before.jsonl', [E / 'hash-advice-before.jsonl']),
                            (E / 'hash-advice-after.jsonl', [E / 'hash-advice-after.jsonl'])]
    compile_r, resolve_r = receipts
    assert compile_r['state'] == 'finished' and 'failure' not in compile_r
    assert resolve_r['state'] == 'failed' and 'Missing required live value' in resolve_r['failure']
    assert compile_r['ended_ns'] < resolve_r['lock']['acquired_ns']
    assert len({r['attempt_id'] for r in receipts}) == 2
    assert all(r['attempt_id'] != '933e3496aaee49b38093699589d74c3b' for r in receipts)
    stop = resolve_r['stop_decision_sample']
    assert stop == resolve_r['latest_decision_sample']
    assert stop['child']['state'] == 'R' and stop['child']['rss'] is None and stop['child']['vm'] is None
    assert stop['child']['partial_stat'] and stop['child']['partial_status']
    assert resolve_r['memory_stop_signal_sent']
    assert stop['sample_finished_ns'] <= resolve_r['memory_stop_signal_started_ns'] <= resolve_r['memory_stop_signal_finished_ns']
    with (B / 'resolve-stop-sample.json').open('x') as f:
        json.dump(stop, f, indent=2)
        f.write('\n')
    obj = state['terminal_objects']
    assert len(obj) == 1 and obj == compile_r['output_inventory_after'] == resolve_r['object_bindings_before'] == resolve_r['output_inventory_after']
    assert obj[0]['sha256'] == '04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc'
    assert sha(Path(obj[0]['path'])) == obj[0]['sha256'] == sha(B / 'preserved-outputs/LightEFTSpanners/FiniteLaw.olean')
    resolution = load(B / 'official-resolution.json')
    assert resolution['target'] == 'LightEFTSpanners.FiniteLaw' and resolution['count'] == 1
    assert resolution['resolved'] == [{'module': 'LightEFTSpanners.FiniteLaw', 'object': obj[0]['path']}]
    assert not state.get('official_resolution')  # The supervised resolver stage never passed.
    history = [json.loads(x) for x in (B / 'history-advice.jsonl').read_text().splitlines()]
    expected_history = {x['path']: x for x in load(B / 'history-whitelist.json')['files']}
    assert len(history) == len({x['path'] for x in history}) == 407
    assert sum(x['bytes'] for x in history) == 183081165
    for row in history:
        assert row['verified_sha256'] == expected_history[row['path']]['sha256']
        assert row['identity'] == row['identity_after_advice']

    chunks = B / 'chunks'
    chunks.mkdir(exist_ok=False)
    manifest = {'reconstruction': 'Concatenate listed part bytes in order without separators; each before/after input inventory pair is identical.', 'inventories': []}
    files_to_export += [(B / 'history-advice.jsonl', [B / 'history-advice.jsonl']),
                       (B / 'toolchain-object-advice.json', [B / 'toolchain-object-advice.json'])]
    for file, targets in files_to_export:
        tag = '-'.join(file.relative_to(B).parts).replace('.', '-')
        folder = chunks / tag
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
        manifest['inventories'].append({'reconstructs': [str(p.relative_to(B)) for p in targets],
                                         'bytes': file.stat().st_size, 'sha256': sha(file), 'parts': parts})
    (chunks / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    active = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            name = (path / 'comm').read_text().strip()
            state_text = (path / 'stat').read_text().rsplit(')', 1)[1].split()[0]
            if name in {'lean', 'lake', 'leanchecker', 'leantar', 'strace'} and state_text != 'Z':
                active.append({'pid': path.name, 'comm': name})
        except OSError:
            pass
    assert not active
    with open('/tmp/distance-sparsification-single-compiler.lock') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'offline reconciliation only; no execution retry',
              'source_commit': SOURCE, 'result': 'COMPILE_PASSED_RESOLVER_TELEMETRY_FAILED_REPLAY_SKIPPED',
              'stages': rows, 'one_lock_inode': True, 'nonoverlap': True, 'all_children_reaped': True,
              'resolution_file_content_matches_fresh_singleton_offline': True, 'supervised_resolution_passed': False,
              'kernel_replay_invocations': 0, 'recursive_axiom_audits_this_attempt': 0,
              'stop_decision_sample_exactly_retained': True, 'signal_sent_before_stop_persistence_by_reviewed_runner': True,
              'signal_delivery_caused_exit': 'Not established; wait4 exit was 0, not a signal exit',
              'fresh_objects': obj, 'chunks': sum(len(x['parts']) for x in manifest['inventories']),
              'toolchain_advice_calls': 50376, 'history_files': 407, 'history_bytes': 183081165,
              'history_visible_current_drop_bytes': compile_r['history_pass']['visible_current_drop_bytes'],
              'common_lock_free': True, 'active_compilers_tracers': active,
              'remaining_blocker': 'Required memory fields missing from resolver status sample; no retry authorized'}
    (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ['stages', 'fresh_objects']}, indent=2))


if __name__ == '__main__':
    main()
