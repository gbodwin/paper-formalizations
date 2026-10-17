"""Offline evidence reconciliation and bounded chunk export; no execution/advice."""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]
E = B / 'evidence/replay'


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def identity(path):
    s = path.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def main():
    state = load(B / 'chain-result.json')
    r = load(E / 'receipt.json')
    q = r['finite_cache_recovery']
    assert state['status'] == 'pinned-singleton-checker-passed'
    assert not state['recompiled'] and not state['resolver_rerun'] and state['no_retries']
    assert len(state['stages']) == 1 and state['stages'][0]['stage'] == 'replay'
    assert r['state'] == 'finished' and r['exit'] == 0 and 'failure' not in r
    assert r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
    assert r['preserved_inputs_verified'] and r['waitid_wait4_status_match']
    assert r['terminal_confirmation']['status'] == 0 and r['terminal_confirmation']['code'] == os.CLD_EXITED
    assert (E / 'raw.log').read_text() == 'replaying LightEFTSpanners.FiniteLaw\n'
    assert not re.findall(r'^.*\.lean:\d+:\d+: warning:', (E / 'raw.log').read_text(), re.M)
    assert (E / 'inputs-before.json').read_bytes() == (E / 'inputs-after.json').read_bytes()
    inputs = load(E / 'inputs-before.json')
    bound = {x['path'] for x in inputs}
    for path, item in r['completed_file_housekeeping'].items():
        file = Path(path)
        assert sha(file) == item['sha256'] and file.stat().st_size == item['bytes']
        assert item['state'] == 'completed' and item['identity'] == item['identity_after_advice']
    assert state['pinned_objects_before'] == state['pinned_objects_after'] == r['object_bindings_before'] == r['output_inventory_after']
    obj = state['pinned_objects_after'][0]
    assert obj['bytes'] == 254600 and sha(Path(obj['path'])) == obj['sha256'] == '04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc'
    authority = load(B / 'recovery-plan.json')
    assert sha(B / 'recovery-plan.json') == 'a0c6b1c10e7ce61df406d68f1b84b6418b3f1acb4d925c5fb20f6ea76a42e335'
    expected = authority['entries']
    original = {}
    for m in authority['authority_manifests']:
        raw = subprocess.check_output(['git', 'show', authority['authority_commit'] + ':' + m['path']], cwd=R)
        assert hashlib.sha256(raw).hexdigest() == m['sha256'] and raw == (R / m['path']).read_bytes()
        parent = Path(m['path']).parent
        for x in json.loads(raw):
            original[str(parent / x['path'])] = x
    assert len(original) == len(expected) == 7313 and sum(x['bytes'] for x in expected) == 3104249317
    for x in expected:
        assert all(x[k] == original[x['path']][k] for k in ['bytes', 'sha256'])
    rows = [json.loads(x) for x in (B / 'finite-recovery.jsonl').read_text().splitlines()]
    assert len(rows) == 7313 and [x['path'] for x in rows] == [x['path'] for x in expected]
    counts = Counter()
    advised_bytes = excluded_bytes = 0
    for wanted, row in zip(expected, rows, strict=True):
        path = R / row['path']
        assert row['bytes'] == wanted['bytes']
        if row['status'] == 'advised':
            assert str(path) not in bound
            assert row['sha256'] == wanted['sha256']
            assert row['identity'] == row['identity_after_advice'] == wanted['identity'] == identity(path)
            assert path.suffix in {'.json', '.jsonl', '.txt', '.log', '.trace', '.maps'}
            assert not (path.suffix == '.txt' and 'source' in path.name.lower())
            assert not path.is_symlink() and not (path.stat().st_mode & 0o111)
            advised_bytes += row['bytes']
            counts['advised'] += 1
        else:
            counts[row['reason']] += 1
            excluded_bytes += row['bytes']
            if row['reason'] == 'current_bound_input':
                assert str(path) in bound
    assert counts == {'advised': 7129, 'code_object_or_nondata_extension': 162,
                       'source_text': 17, 'current_bound_input': 5}
    assert advised_bytes == q['advised_bytes'] == 3078727377 and excluded_bytes == q['excluded_bytes'] == 25521940
    assert q['state'] == 'completed' and q['advised_files'] == 7129 and q['excluded_files'] == 184
    assert sha(B / 'finite-recovery.jsonl') == q['log_finish']['sha256']
    assert q['log_finish']['flushed_fsynced'] and q['log_finish']['identity'] == q['log_finish']['identity_after_advice']
    assert q['log_finished_ns'] < q['after']['sample_started_ns'] < r['admission']['sample_started_ns']
    assert q['visible_current_drop_bytes'] == q['before']['nodes'][0]['current'] - q['after']['nodes'][0]['current'] == 1636978688
    assert r['admission']['headroom'] == 4443586560 >= 4294967296
    assert r['preexec_admission']['headroom'] == 4439322624 >= 4294967296
    assert r['admission']['system_available'] >= 3221225472 and r['preexec_admission']['system_available'] >= 3221225472
    samples = [json.loads(x) for x in (E / 'samples.jsonl').read_text().splitlines()]
    terminal = samples[-1]
    assert terminal == r['latest_decision_sample'] and terminal['exit_lifecycle']['terminal_confirmed']
    assert terminal['child']['rss'] is None and terminal['child']['vm'] is None
    assert r['anonymous_preexec_baseline'] == {n['path']: n['memory_stat']['anon'] for n in r['preexec_admission']['nodes']}
    required = ['anon', 'file', 'kernel', 'file_mapped', 'file_dirty', 'file_writeback',
                'active_file', 'inactive_file', 'slab_reclaimable', 'slab_unreclaimable']
    for s in [q['before'], q['after'], r['admission'], r['preexec_admission']] + [x['accounting'] for x in samples]:
        for node in s['nodes']:
            assert all(k in node['memory_stat'] for k in required)
            assert {k: int(v) for k, v in [x.split() for x in node['memory_stat_raw'].splitlines()]} == node['memory_stat']
    post = [x for x in samples if x['sample_started_ns'] >= r['preexec_decision_sample']['sample_started_ns']]
    growth = {path: max(n['memory_stat']['anon'] - base for s in post for n in s['accounting']['nodes'] if n['path'] == path)
              for path, base in r['anonymous_preexec_baseline'].items()}
    minimum = min(samples, key=lambda x: x['accounting']['headroom'])
    (B / 'checker-terminal-sample.json').write_text(json.dumps(terminal, indent=2) + '\n')
    (B / 'capacity-evidence.json').write_text(json.dumps({'recovery_before': q['before'], 'recovery_after': q['after'],
        'admission': r['admission'], 'preexec': r['preexec_admission'], 'minimum_runtime_sample': minimum}, indent=2) + '\n')
    tool = {x['path']: x for x in load(B / 'toolchain-object-advice.json')['files']}
    for phase in ['before', 'after']:
        seen = set()
        with (E / ('hash-advice-' + phase + '.jsonl')).open() as f:
            for line in f:
                x = json.loads(line)
                assert not x.get('error')
                if x.get('advice_scope') == 'toolchain_immutable_object':
                    assert x['advised'] and x['path'] not in seen
                    seen.add(x['path'])
                    assert all(x[k] == tool[x['path']][k] for k in ['sha256', 'bytes', 'identity'])
        assert seen == set(tool) and len(seen) == 12594

    folder = B / 'chunks'
    folder.mkdir(exist_ok=False)
    streams = [(E / 'inputs-before.json', [E / 'inputs-before.json', E / 'inputs-after.json']),
               (E / 'hash-advice-before.jsonl', [E / 'hash-advice-before.jsonl']),
               (E / 'hash-advice-after.jsonl', [E / 'hash-advice-after.jsonl']),
               (B / 'finite-recovery.jsonl', [B / 'finite-recovery.jsonl']),
               (B / 'recovery-plan.json', [B / 'recovery-plan.json']),
               (B / 'toolchain-object-advice.json', [B / 'toolchain-object-advice.json']),
               (E / 'samples.jsonl', [E / 'samples.jsonl'])]
    manifest = {'reconstruction': 'Concatenate listed part bytes without separators. Byte chunks may split JSON tokens or rows.', 'inventories': []}
    for file, targets in streams:
        partdir = folder / ('-'.join(file.relative_to(B).parts).replace('.', '-'))
        partdir.mkdir()
        parts = []
        digest = hashlib.sha256()
        with file.open('rb') as f:
            for data in iter(lambda: f.read(200000), b''):
                part = partdir / ('part-%03d.txt' % len(parts))
                part.write_bytes(data)
                digest.update(data)
                parts.append({'path': str(part.relative_to(folder)), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
        assert digest.hexdigest() == sha(file)
        manifest['inventories'].append({'reconstructs': [str(p.relative_to(B)) for p in targets],
                                         'bytes': file.stat().st_size, 'sha256': sha(file), 'parts': parts})
    (folder / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    active = [x for x in subprocess.check_output(['ps', '-eo', 'pid=,stat=,comm='], text=True).splitlines()
              if x.split()[-1] in ('lean', 'lake', 'leanchecker', 'leantar', 'strace') and not x.split()[1].startswith('Z')]
    assert not active
    with open('/tmp/distance-sparsification-single-compiler.lock') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline reconciliation only; no execution or cache advice',
              'source_commit': state['source_commit'], 'result': 'PINNED_SINGLETON_CHECKER_PASSED_AFTER_ONE_FINITE_RECOVERY',
              'attempt_id': r['attempt_id'], 'created_utc': r['created_utc'], 'ended_utc': r['ended_utc'], 'child_pid': r['child_pid'],
              'child_exit': 0, 'recompiled': False, 'resolver_rerun': False, 'no_retries': True,
              'argv': r['argv'], 'environment': r['environment'], 'pinned_object': obj,
              'recovery_authority_files': 7313, 'recovery_authority_bytes': 3104249317,
              'recovery_advised_files': 7129, 'recovery_advised_bytes': advised_bytes,
              'recovery_excluded_counts': dict(counts), 'measured_visible_current_drop_bytes': 1636978688,
              'log_finished_before_measurement': True, 'admission_visible_bytes': r['admission']['headroom'],
              'preexec_visible_bytes': r['preexec_admission']['headroom'], 'input_inventory_rows': len(inputs),
              'input_inventories_byte_identical': True, 'input_inventory_sha256': sha(E / 'inputs-before.json'),
              'runtime_sample_count': len(samples), 'minimum_runtime_visible_bytes': minimum['accounting']['headroom'],
              'sampled_rss_peak_bytes': r['sampled_rss_peak_bytes'], 'wait4_rss_bytes': r['wait4_maxrss_kib'] * 1024,
              'maximum_anonymous_growth_per_group': growth, 'full_memory_stat_retained': True,
              'child_limit_and_lock_readbacks_verified': True, 'waitid_wait4_status_match': True,
              'all_children_reaped': True, 'chunks': sum(len(x['parts']) for x in manifest['inventories']),
              'new_recursive_axiom_audits': 0, 'new_compiler_invocations': 0, 'new_resolver_invocations': 0,
              'new_checker_invocations': 1, 'ci_or_full_clean': False, 'common_lock_free': True, 'active_compilers_tracers': active}
    (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('argv', 'environment', 'pinned_object')}, indent=2))


if __name__ == '__main__':
    main()
