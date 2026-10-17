"""Read-only evidence reconciliation. Does not import or execute the attempt runner."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]
E = B / 'evidence/compile'
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'
ATTEMPT = '933e3496aaee49b38093699589d74c3b'
SOURCE_HASH = '7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def published_files():
    return sorted(p for p in B.rglob('*') if p.is_file()
                  and '__pycache__' not in p.parts and p.name != 'evidence-sha256.json')


def main():
    r = read_json(E / 'receipt.json')
    state = read_json(B / 'chain-result.json')
    assert r['attempt_id'] == ATTEMPT and r['source_commit'] == SOURCE
    assert r['state'] == 'failed' and r.get('child_pid') is None
    assert r['failure'] == "MemoryGuardError('Visible headroom below required floor')"
    assert r['admission']['headroom'] == 3733762048
    assert r['memory_policy']['admission_visible_host_bytes'] == 3758096384
    assert r['kernel_no_children_verified'] and r['preserved_inputs_verified']
    assert not r['output_inventory_after']
    assert state['status'] == 'stopped-first-failure' and not state['stages']
    assert not state['terminal_objects'] and state['no_retries']
    assert not (E / 'raw.log').exists() and not (E / 'samples.jsonl').exists()
    assert not (B / 'evidence/resolve').exists() and not (B / 'evidence/replay').exists()
    object_path = Path(r['argv'][r['argv'].index('-o') + 1])
    assert not list(object_path.parents[1].rglob('*.*'))
    source_path = Path(r['argv'][-1])
    assert digest(source_path.read_bytes()) == SOURCE_HASH == r['submitted_source_sha256']
    assert digest((E / 'submitted-source.txt').read_bytes()) == SOURCE_HASH
    frozen = subprocess.check_output(['git', 'show', SOURCE + ':' + str(source_path.relative_to(R))], cwd=R)
    assert frozen == source_path.read_bytes()
    for name in ['lake-manifest.json', 'lean-toolchain']:
        assert subprocess.check_output(['git', 'show', SOURCE + ':' + name], cwd=R) == (R / name).read_bytes()

    before = (E / 'inputs-before.json').read_bytes()
    assert before == (E / 'inputs-after.json').read_bytes()
    assert digest(before) == 'e59838ddb9d9f126857d2f8892c8f359ea157d6bd589b6727abedcb6664d4cae'
    assert len(json.loads(before)) == 66985
    whitelist = B / 'toolchain-object-advice.json'
    assert digest(whitelist.read_bytes()) == 'ac8ff793992fec47cbac50629be8e3835b6f81328804b4662a4d6a94e60b65af'
    expected = {x['path']: x for x in read_json(whitelist)['files']}
    assert len(expected) == 12594 and sum(x['bytes'] for x in expected.values()) == 2212380925
    advice = read_json(B / 'toolchain-advice-reconciliation.json')
    for phase, drop in [('before', -15200256), ('after', -13053952)]:
        seen = set()
        with (E / ('hash-advice-' + phase + '.jsonl')).open() as f:
            for line in f:
                row = json.loads(line)
                assert not row.get('error') and not row.get('advice_error')
                if row.get('advice_scope') == 'toolchain_immutable_object':
                    assert row['advised'] and row['path'] not in seen
                    seen.add(row['path'])
                    wanted = expected[row['path']]
                    assert all(row[k] == wanted[k] for k in ['sha256', 'bytes', 'identity'])
        assert seen == set(expected)
        m = r['toolchain_verification_measurements'][phase]
        assert m == advice['phases'][phase]['measurement']
        assert m['visible_current_drop_bytes'] == drop
        assert m['before']['nodes'][0]['current'] - m['after']['nodes'][0]['current'] == drop

    history_expected = {x['path']: x for x in read_json(B / 'history-whitelist.json')['files']}
    history = [json.loads(x) for x in (B / 'history-advice.jsonl').read_text().splitlines()]
    assert len(history) == len({x['path'] for x in history}) == 407
    assert sum(x['bytes'] for x in history) == 183081165
    for row in history:
        assert row['verified_sha256'] == history_expected[row['path']]['sha256']
        assert row['identity'] == row['identity_after_advice']
    assert r['history_pass']['visible_current_drop_bytes'] == 81920
    assert len(r['completed_file_housekeeping']) == 5
    for name, row in r['completed_file_housekeeping'].items():
        data = Path(name).read_bytes()
        assert row['state'] == 'completed' and digest(data) == row['sha256'] and len(data) == row['bytes']
        assert row['identity'] == row['identity_after_advice']

    tests = read_json(B / 'harmless-tests.json')
    assert all(tests['checks'].values()) and len(tests['fixtures']) == 7
    for fixture in tests['fixtures']:
        path = B / fixture['receipt']
        q = read_json(path)
        assert q['stop_decision_sample'] == read_json(path.parent / 'samples.jsonl')
        assert q['exact_sample_retained'] and q['child_reaped']
        assert q['collection_before_kill_before_persist']

    chunks = read_json(B / 'chunks/manifest.json')
    chunk_count = 0
    for item in chunks['inventories']:
        whole = hashlib.sha256()
        size = 0
        for part in item['parts']:
            data = (B / 'chunks' / part['path']).read_bytes()
            assert len(data) == part['bytes'] and digest(data) == part['sha256']
            whole.update(data)
            size += len(data)
            chunk_count += 1
        assert size == item['bytes'] and whole.hexdigest() == item['sha256']
        for target in item['reconstructs']:
            data = (B / 'chunks' / target).read_bytes()
            assert len(data) == size and digest(data) == whole.hexdigest()
    assert chunk_count == 459

    manifest_path = B / 'evidence-sha256.json'
    manifest_count = None
    if manifest_path.exists():
        entries = read_json(manifest_path)
        assert {x['path'] for x in entries} == {str(p.relative_to(B)) for p in published_files()}
        for row in entries:
            data = (B / row['path']).read_bytes()
            assert len(data) == row['bytes'] and digest(data) == row['sha256']
        manifest_count = len(entries)
    publication_path = B / 'PUBLICATION.json'
    if publication_path.exists():
        p = read_json(publication_path)
        assert p['source_commit'] == SOURCE and p['attempt_id'] == ATTEMPT
        assert p['compiler_children'] == p['resolver_children'] == p['checker_children'] == 0
        paths = subprocess.check_output(['git', 'diff', '--name-only', p['base_evidence_commit'], 'HEAD'], cwd=R, text=True).splitlines()
        assert paths and all(x.startswith(str(B.relative_to(R)) + '/') for x in paths)

    active = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            comm = (path / 'comm').read_text().strip()
            state = (path / 'stat').read_text().rsplit(')', 1)[1].split()[0]
            if comm in {'lean', 'leanchecker', 'lake', 'leanc', 'leantar', 'strace'} and state != 'Z':
                active.append({'pid': path.name, 'comm': comm, 'state': state})
        except (OSError, IndexError):
            pass
    assert not active, active
    with open('/tmp/distance-sparsification-single-compiler.lock', 'r') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    print(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      'operation': 'offline evidence verification only; no Lean or retry',
                      'attempt_id': ATTEMPT, 'result': 'admission refused before child spawn',
                      'compiler_children': 0, 'resolver_children': 0, 'checker_children': 0,
                      'verified_input_rows': 66985, 'verified_chunk_count': chunk_count,
                      'verified_manifest_entries': manifest_count, 'active_compilers_tracers': active,
                      'common_lock_free': True}, indent=2))


if __name__ == '__main__':
    main()
