"""Offline receipt/inventory verification; no Lean, advice or third full input pass."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    s = load(B / 'batch-result.json')
    final = load(B / 'final-content-verification.json')
    lease = load(B / 'batch-lock.json')
    result = load(B / 'result-reconciliation.json')
    assert s['source_commit'] == result['source_commit'] == '78cb40c7837db049d645d73696f2e0b724ce8a3b'
    assert s['status'] == 'stopped-first-failure' and s['accepted_modules'] == s['provisional_modules'] == []
    assert len(s['stages']) == 2 and result['skipped_stages'] == 58
    assert final['matching'] and final['all_paths_attempted'] and final['paths_checked'] == 74609
    assert final['before_sha256'] == final['after_stream_sha256'] == sha(B / 'inputs.jsonl')
    assert final['before_sha256'] == '50a2e51d63e167bbf4410dbb84b59b3724071be2daff59ea7ea577fd3611ac2d'
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns']
    rs = []
    for st in s['stages']:
        p = B / st['receipt']
        r = load(p)
        assert r['kernel_no_children_verified'] and r['all_descendants_gone'] and r['direct_reaped']
        assert r['between_child_preservation_passed'] and r['lock']['outer_acquired_ns'] == lease['acquired_ns']
        assert (r['lock']['device'], r['lock']['inode']) == (33, 3849)
        assert r['canonical_input_inventory']['sha256'] == final['before_sha256']
        assert sha(B / r['source_snapshot']) == r['submitted_source_sha256']
        samples = [json.loads(x) for x in (p.parent / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == r['latest_decision_sample']
        rs.append(r)
    assert rs[0]['state'] == 'finished' and rs[0]['exit'] == 0
    assert rs[0]['ended_ns'] < rs[1]['lock']['child_entry_ns']
    assert rs[1]['state'] == 'failed' and rs[1]['exit'] == 0
    stop = load(B / 'resolver-stop-sample.json')
    assert stop == rs[1]['stop_decision_sample'] == rs[1]['latest_decision_sample']
    assert stop['child']['state'] == 'Z' and stop['child']['stat_threads'] == stop['child']['status_threads'] == 2
    assert stop['child']['rss'] is None and stop['child']['vm'] is None
    assert len(stop['exit_lifecycle']['probes']) == 3 and all(not p['terminal'] for p in stop['exit_lifecycle']['probes'])
    assert not stop['exit_lifecycle']['allow_missing_memory'] and rs[1]['memory_stop_signal_sent']
    assert max([stop['sample_finished_ns']] + [p['finished_ns'] for p in stop['exit_lifecycle']['probes']]) <= rs[1]['memory_stop_signal_started_ns']
    statuses = load(B / 'module-status.json')
    assert len(statuses) == 20 and not any(x['accepted'] for x in statuses)
    assert all(x['replay'] == 'skipped_after_first_failure' for x in statuses)
    outputs = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])['objects']
    assert len(outputs) == 2
    for obj in outputs:
        p = Path(obj['path'])
        copy = B / 'preserved-objects' / p.relative_to(p.parents[1])
        assert sha(p) == sha(copy) == obj['sha256']
    cases = load(B / 'shared-fixture-results.json')['cases']
    assert len(cases) == 3 and all(x['passed'] for x in cases)
    for case in cases:
        assert load(B / case['folder'] / 'lease.json')['kernel_echild_at_release']
        for path in case['receipts']:
            r = load(B / path)
            assert r['fixture_only'] and r['kernel_no_children_verified']
            for name, value in r['harness_hashes'].items():
                assert sha(B / name) == value
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
                      'scope': 'Offline verification; no Lean/advice/retry or third full frozen-input pass',
                      'source_commit': s['source_commit'], 'new_completed_modules': 0,
                      'successful_compiles': 1, 'failed_supervised_resolutions': 1, 'checker_invocations': 0,
                      'final_full_content_verified': True, 'canonical_input_rows': 74609,
                      'focused_fixture_cases': 3, 'manifest_entries_verified': len(entries) if entries else None,
                      'active_compilers_tracers': active, 'common_lock_free': True}, indent=2))


if __name__ == '__main__':
    main()
