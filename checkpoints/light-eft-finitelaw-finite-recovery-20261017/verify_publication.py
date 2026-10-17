"""Read-only verification; never imports/runs the attempt or performs advice."""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]
E = B / 'evidence/replay'
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    state = load(B / 'chain-result.json')
    result = load(B / 'result-reconciliation.json')
    r = load(E / 'receipt.json')
    q = r['finite_cache_recovery']
    assert state['source_commit'] == result['source_commit'] == r['source_commit'] == SOURCE
    assert state['status'] == 'pinned-singleton-checker-passed'
    assert not state['recompiled'] and not state['resolver_rerun'] and state['no_retries']
    assert r['state'] == 'finished' and r['exit'] == 0 and 'failure' not in r
    assert r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
    assert r['waitid_wait4_status_match'] and r['preserved_inputs_verified']
    assert r['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888],
        'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
    assert (r['lock']['device'], r['lock']['inode']) == (33, 3849)
    assert r['argv'] == ['/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker', '-v', 'LightEFTSpanners.FiniteLaw']
    assert (E / 'raw.log').read_text() == 'replaying LightEFTSpanners.FiniteLaw\n'
    assert (E / 'inputs-before.json').read_bytes() == (E / 'inputs-after.json').read_bytes()
    inputs = load(E / 'inputs-before.json')
    assert len(inputs) == 67011
    bound = {x['path'] for x in inputs}
    obj = state['pinned_objects_before']
    assert obj == state['pinned_objects_after'] == r['object_bindings_before'] == r['output_inventory_after']
    assert obj[0]['bytes'] == 254600 and sha(Path(obj[0]['path'])) == obj[0]['sha256'] == '04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc'
    for x in load(B / 'source-toolchain-object-hashes.json')['files']:
        assert sha(Path(x['path'])) == x['sha256']
    source = R / 'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean'
    assert source.read_bytes() == subprocess.check_output(['git', 'show', SOURCE + ':' + str(source.relative_to(R))], cwd=R)
    for name in ['lake-manifest.json', 'lean-toolchain']:
        assert (R / name).read_bytes() == subprocess.check_output(['git', 'show', SOURCE + ':' + name], cwd=R)
    plan = load(B / 'recovery-plan.json')
    assert sha(B / 'recovery-plan.json') == 'a0c6b1c10e7ce61df406d68f1b84b6418b3f1acb4d925c5fb20f6ea76a42e335'
    assert len(plan['roots']) == 15 and len(plan['entries']) == 7313
    assert sum(x['bytes'] for x in plan['entries']) == 3104249317
    for m in plan['authority_manifests']:
        assert sha(R / m['path']) == m['sha256']
    rows = [json.loads(x) for x in (B / 'finite-recovery.jsonl').read_text().splitlines()]
    assert [x['path'] for x in rows] == [x['path'] for x in plan['entries']]
    counts = Counter()
    total = 0
    for expected, row in zip(plan['entries'], rows, strict=True):
        file = R / row['path']
        if row['status'] == 'advised':
            counts['advised'] += 1
            total += row['bytes']
            assert str(file) not in bound and row['sha256'] == expected['sha256']
            assert row['identity'] == row['identity_after_advice'] == expected['identity']
            s = file.stat()
            assert [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns] == row['identity']
        else:
            counts[row['reason']] += 1
            if row['reason'] == 'current_bound_input':
                assert str(file) in bound
    assert counts == {'advised': 7129, 'code_object_or_nondata_extension': 162, 'source_text': 17, 'current_bound_input': 5}
    assert total == q['advised_bytes'] == 3078727377
    assert q['state'] == 'completed' and q['advised_files'] == 7129 and q['excluded_files'] == 184
    assert sha(B / 'finite-recovery.jsonl') == q['log_finish']['sha256']
    assert q['log_finish']['flushed_fsynced'] and q['log_finish']['identity'] == q['log_finish']['identity_after_advice']
    assert q['log_finished_ns'] < q['after']['sample_started_ns'] < r['admission']['sample_started_ns']
    assert r['admission']['headroom'] == 4443586560 >= 4294967296
    assert r['preexec_admission']['headroom'] == 4439322624 >= 4294967296
    assert r['admission']['system_available'] >= 3221225472 and r['preexec_admission']['system_available'] >= 3221225472
    assert r['memory_policy']['stop_visible_host_bytes'] == 1073741824
    samples = [json.loads(x) for x in (E / 'samples.jsonl').read_text().splitlines()]
    assert len(samples) == 71 and samples[-1] == r['latest_decision_sample'] == load(B / 'checker-terminal-sample.json')
    assert samples[-1]['exit_lifecycle']['terminal_confirmed'] and samples[-1]['child']['rss'] is None
    assert min(s['accounting']['headroom'] for s in samples) == 1980600320
    for account in [q['before'], q['after'], r['admission'], r['preexec_admission']] + [s['accounting'] for s in samples]:
        for node in account['nodes']:
            assert {k: int(v) for k, v in [x.split() for x in node['memory_stat_raw'].splitlines()]} == node['memory_stat']
            assert all(k in node['memory_stat'] for k in ['file_mapped', 'file_dirty', 'file_writeback',
                                                         'active_file', 'inactive_file', 'slab_reclaimable', 'slab_unreclaimable'])
    assert all(load(B / 'boundary-checks.json')['checks'].values())
    count = 0
    for stream in load(B / 'chunks/manifest.json')['inventories']:
        digest = hashlib.sha256()
        size = 0
        for part in stream['parts']:
            file = B / 'chunks' / part['path']
            assert sha(file) == part['sha256'] and file.stat().st_size == part['bytes']
            digest.update(file.read_bytes())
            size += part['bytes']
            count += 1
        assert size == stream['bytes'] and digest.hexdigest() == stream['sha256']
        for target in stream['reconstructs']:
            assert sha(B / target) == stream['sha256'] and (B / target).stat().st_size == size
    assert count == 487
    manifest = B / 'evidence-sha256.json'
    entries = None
    if manifest.exists():
        entries = load(manifest)
        expected = {str(p.relative_to(B)) for p in B.rglob('*') if p.is_file()
                    and '__pycache__' not in p.parts and p.name != manifest.name}
        assert {x['path'] for x in entries} == expected
        for row in entries:
            assert sha(B / row['path']) == row['sha256'] and (B / row['path']).stat().st_size == row['bytes']
    publication = B / 'PUBLICATION.json'
    if publication.exists():
        meta = load(publication)
        paths = subprocess.check_output(['git', 'diff', '--name-only', meta['base_evidence_commit'], 'HEAD'], cwd=R, text=True).splitlines()
        assert paths and all(x.startswith(str(B.relative_to(R)) + '/') for x in paths)
    active = [x for x in subprocess.check_output(['ps', '-eo', 'pid=,stat=,comm='], text=True).splitlines()
              if x.split()[-1] in ('lean', 'lake', 'leanchecker', 'leantar', 'strace') and not x.split()[1].startswith('Z')]
    assert not active
    with open('/tmp/distance-sparsification-single-compiler.lock') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    print(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      'scope': 'Offline verification only; no tool execution, advice, recovery pass, or retry',
                      'source_commit': SOURCE, 'attempt_id': r['attempt_id'], 'checker_exit': 0,
                      'result': result['result'], 'recovery_advised_files': 7129,
                      'recovery_advised_bytes': total, 'current_bound_inputs_excluded': 5,
                      'chunks_verified': count, 'manifest_entries_verified': len(entries) if entries else None,
                      'active_compilers_tracers': active, 'common_lock_free': True}, indent=2))


if __name__ == '__main__':
    main()
