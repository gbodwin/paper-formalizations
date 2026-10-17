"""Read-only evidence verification; no attempt imports, Lean, fixtures or advice."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import subprocess

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
    result = load(B / 'result-reconciliation.json')
    assert state['source_commit'] == result['source_commit'] == SOURCE
    assert state['status'] == 'stopped-first-failure' and not state['recompiled'] and state['no_retries']
    assert [x['stage'] for x in state['stages']] == ['resolve']
    assert result['result'] == 'RESOLUTION_PASSED_CHECKER_STOPPED_BY_1GIB_VISIBLE_HEADROOM_GUARD'
    obj = state['pinned_objects_before']
    assert obj == state['pinned_objects_after'] and len(obj) == 1
    assert sha(Path(obj[0]['path'])) == obj[0]['sha256'] == '04730e8d2e2cd8b517825d4e91505c9eb60e27ca616d1654d574a3dbea00d1cc'
    assert obj[0]['bytes'] == 254600
    receipts = [load(B / 'evidence' / stage / 'receipt.json') for stage in ['resolve', 'replay']]
    assert receipts[0]['state'] == 'finished' and receipts[0]['exit'] == 0 and receipts[0]['waitid_wait4_status_match']
    assert receipts[1]['state'] == 'failed' and receipts[1]['exit'] == -9
    assert receipts[0]['ended_ns'] < receipts[1]['lock']['acquired_ns']
    for r in receipts:
        E = B / 'evidence' / r['stage']
        assert r['source_commit'] == SOURCE and r['direct_reaped'] and r['kernel_no_children_verified']
        assert r['all_descendants_gone'] and r['preserved_inputs_verified']
        assert r['object_bindings_before'] == r['output_inventory_after'] == obj
        assert (r['lock']['device'], r['lock']['inode']) == (33, 3849)
        assert r['handshake']['limits']['RLIMIT_AS'] == [12884901888, 12884901888]
        assert sha(E / 'submitted-source.txt') == r['submitted_source_sha256']
        assert (E / 'inputs-before.json').read_bytes() == (E / 'inputs-after.json').read_bytes()
        samples = [json.loads(x) for x in (E / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == r['latest_decision_sample']
    terminal = load(B / 'resolver-terminal-sample.json')
    assert terminal == receipts[0]['latest_decision_sample']
    assert terminal['child']['rss'] is None and terminal['child']['vm'] is None
    assert terminal['exit_lifecycle']['terminal_confirmed']
    assert terminal['exit_lifecycle']['confirmation'] == receipts[0]['terminal_confirmation']
    assert receipts[0].get('exit_transition') is None
    stop = load(B / 'checker-stop-sample.json')
    checker = receipts[1]
    assert stop == checker['stop_decision_sample'] == checker['latest_decision_sample']
    assert not stop['collection_errors'] and not stop['exit_lifecycle']['terminal_confirmed']
    assert stop['accounting']['headroom'] == 1042374656 < 1073741824
    assert stop['sample_finished_ns'] <= checker['memory_stop_signal_started_ns'] <= checker['memory_stop_signal_finished_ns']
    assert checker['memory_stop_signal_sent']
    assert (B / 'evidence/replay/raw.log').read_bytes() == b''
    resolution = load(B / 'official-resolution.json')
    assert state['official_resolution'] == resolution and resolution['count'] == 1
    assert resolution['resolved'] == [{'module': 'LightEFTSpanners.FiniteLaw', 'object': obj[0]['path']}]
    for item in load(B / 'source-toolchain-object-hashes.json')['files']:
        assert sha(Path(item['path'])) == item['sha256']
    source = R / 'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/FiniteLaw.lean'
    assert source.read_bytes() == subprocess.check_output(['git', 'show', SOURCE + ':' + str(source.relative_to(R))], cwd=R)
    for name in ['lake-manifest.json', 'lean-toolchain']:
        assert (R / name).read_bytes() == subprocess.check_output(['git', 'show', SOURCE + ':' + name], cwd=R)
    fixtures = load(B / 'focused-fixture-results-v2.json')['fixtures']
    assert len(fixtures) == 11 and all(x['fixture_passed'] for x in fixtures)
    fixture_rows = []
    for item in fixtures:
        file = B / item['receipt']
        r = load(file)
        assert r['fixture_assertions_passed'] and r['kernel_no_children_verified'] and r['direct_reaped']
        assert r['exclusive_lock_verified'] and r['inherited_lock_verified']
        assert sha(file.parent / 'submitted-child.py') == r['submitted_source_sha256']
        for name, digest in r['submitted_sources'].items():
            assert sha(B / name) == digest
        fixture_rows.append(r)
    fixture_rows.sort(key=lambda r: r['started_ns'])
    assert all(a['ended_ns'] < b['started_ns'] for a, b in zip(fixture_rows, fixture_rows[1:]))
    assert fixture_rows[-1]['ended_ns'] < receipts[0]['started_ns']
    failed = list((B / 'focused-fixtures').glob('*/receipt.json'))
    assert len(failed) == 1
    old = load(failed[0])
    assert old['exit'] == 0 and old['kernel_no_children_verified']
    for name, digest in old['submitted_sources'].items():
        assert sha(B / 'fixture-development-failure-001' / name) == digest
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
            file = B / target
            assert sha(file) == stream['sha256'] and file.stat().st_size == size
    assert count == 891
    manifest = B / 'evidence-sha256.json'
    entries = None
    if manifest.exists():
        entries = load(manifest)
        expected = {str(p.relative_to(B)) for p in B.rglob('*') if p.is_file()
                    and '__pycache__' not in p.parts and p.name != manifest.name}
        assert {x['path'] for x in entries} == expected
        for item in entries:
            path = B / item['path']
            assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes']
    publication = B / 'PUBLICATION.json'
    if publication.exists():
        meta = load(publication)
        paths = subprocess.check_output(['git', 'diff', '--name-only', meta['base_evidence_commit'], 'HEAD'], cwd=R, text=True).splitlines()
        assert paths and all(x.startswith(str(B.relative_to(R)) + '/') for x in paths)
    active = [x for x in subprocess.check_output(['ps', '-eo', 'pid=,stat=,comm='], text=True).splitlines()
              if x.split()[-1] in ('lean', 'lake', 'leanchecker', 'strace', 'leantar') and not x.split()[1].startswith('Z')]
    assert not active
    with open('/tmp/distance-sparsification-single-compiler.lock') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    print(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      'operation': 'Offline verification only; no Lean/checker, fixtures, advice or retry',
                      'source_commit': SOURCE, 'result': result['result'], 'receipts': 2,
                      'focused_fixtures_passed': 11, 'preserved_development_fixture_failures': 1,
                      'chunks_verified': count, 'manifest_entries_verified': len(entries) if entries else None,
                      'active_compilers_tracers': active, 'common_lock_free': True}, indent=2))


if __name__ == '__main__':
    main()
