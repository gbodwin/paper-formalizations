"""Read-only reconciliation of the published failed chain; never executes Lean."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'
PREVIOUS = R / 'checkpoints/light-eft-finitelaw-accounted-chain-20261017'


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    result = load(B / 'result-reconciliation.json')
    state = load(B / 'chain-result.json')
    assert result['source_commit'] == SOURCE == state['frozen_production']
    assert result['result'] == 'COMPILE_PASSED_RESOLVER_TELEMETRY_FAILED_REPLAY_SKIPPED'
    assert result['kernel_replay_invocations'] == result['recursive_axiom_audits_this_attempt'] == 0
    assert state['status'] == 'stopped-first-failure' and state['no_retries']
    assert len(state['stages']) == 1 and state['stages'][0]['stage'] == 'compile'
    assert not (B / 'evidence/replay').exists()
    receipts = [load(B / 'evidence' / stage / 'receipt.json') for stage in ['compile', 'resolve']]
    assert receipts[0]['state'] == 'finished' and 'failure' not in receipts[0]
    assert receipts[1]['state'] == 'failed' and 'Missing required live value' in receipts[1]['failure']
    assert receipts[0]['ended_ns'] < receipts[1]['lock']['acquired_ns']
    assert len({r['attempt_id'] for r in receipts}) == 2
    for r in receipts:
        assert r['exit'] == 0 and r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
        assert r['preserved_inputs_verified'] and r['memory_policy']['admission_visible_host_bytes'] == 3221225472
        assert r['handshake']['limits']['RLIMIT_AS'] == [12884901888, 12884901888]
        assert (r['lock']['device'], r['lock']['inode']) == (33, 3849)
        assert (r['handshake']['lock_device'], r['handshake']['lock_inode']) == (33, 3849)
        E = B / 'evidence' / r['stage']
        assert sha(E / 'submitted-source.txt') == r['submitted_source_sha256']
        assert (E / 'inputs-before.json').read_bytes() == (E / 'inputs-after.json').read_bytes()
        samples = [json.loads(x) for x in (E / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == r['latest_decision_sample']
        assert r['anonymous_preexec_baseline'] == {n['path']: n['memory_stat']['anon'] for n in r['preexec_admission']['nodes']}
    stop = receipts[1]['stop_decision_sample']
    assert stop == load(B / 'resolve-stop-sample.json') == receipts[1]['latest_decision_sample']
    assert stop['child']['rss'] is None and stop['child']['vm'] is None and stop['child']['state'] == 'R'
    assert stop['sample_finished_ns'] <= receipts[1]['memory_stop_signal_started_ns'] <= receipts[1]['memory_stop_signal_finished_ns']
    assert receipts[1]['memory_stop_signal_sent']
    resolution = load(B / 'official-resolution.json')
    obj = state['terminal_objects'][0]
    assert resolution['resolved'] == [{'object': obj['path'], 'module': 'LightEFTSpanners.FiniteLaw'}]
    assert resolution['count'] == 1 and 'official_resolution' not in state
    assert sha(Path(obj['path'])) == obj['sha256'] == sha(B / 'preserved-outputs/LightEFTSpanners/FiniteLaw.olean')
    for row in load(B / 'source-toolchain-object-hashes.json')['files']:
        assert sha(Path(row['path'])) == row['sha256']
    source_path = Path(receipts[0]['argv'][-1])
    assert subprocess.check_output(['git', 'show', SOURCE + ':' + str(source_path.relative_to(R))], cwd=R) == source_path.read_bytes()
    expected_runner = (PREVIOUS / 'pilot_runner.py').read_bytes().replace(b'ADMISSION_HEADROOM=3758096384', b'ADMISSION_HEADROOM=3221225472').replace(b'ec7ed3c19a7e4d64ad9aa59666882e61', b'f23bcfb0a9df41ef888a8b33de4130f3')
    assert (B / 'pilot_runner.py').read_bytes() == expected_runner
    for name in ['pilot_child.py', 'pilot_accounting.py', 'pilot_cache_advice.py', 'decision_telemetry.py',
                 'integrated_housekeeping.py', 'pid_observations.py', 'chain.py',
                 'history-whitelist.json', 'toolchain-object-advice.json']:
        assert (B / name).read_bytes() == (PREVIOUS / name).read_bytes()
    assert all(load(B / 'admission-boundary-checks.json')['checks'].values())
    chunks = load(B / 'chunks/manifest.json')
    count = 0
    for item in chunks['inventories']:
        digest = hashlib.sha256()
        size = 0
        for part in item['parts']:
            path = B / 'chunks' / part['path']
            assert path.stat().st_size == part['bytes'] and sha(path) == part['sha256']
            with path.open('rb') as f:
                digest.update(f.read())
            size += part['bytes']
            count += 1
        assert size == item['bytes'] and digest.hexdigest() == item['sha256']
        for target in item['reconstructs']:
            path = B / target
            assert path.stat().st_size == size and sha(path) == item['sha256']
    assert count == 893
    manifest = B / 'evidence-sha256.json'
    entries = None
    if manifest.exists():
        entries = load(manifest)
        expected_paths = {str(p.relative_to(B)) for p in B.rglob('*') if p.is_file()
                          and '__pycache__' not in p.parts and p.name != manifest.name}
        assert {x['path'] for x in entries} == expected_paths
        for row in entries:
            path = B / row['path']
            assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256']
    publication = B / 'PUBLICATION.json'
    if publication.exists():
        meta = load(publication)
        paths = subprocess.check_output(['git', 'diff', '--name-only', meta['base_evidence_commit'], 'HEAD'], cwd=R, text=True).splitlines()
        assert paths and all(p.startswith(str(B.relative_to(R)) + '/') for p in paths)
    active = []
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            comm = (p / 'comm').read_text().strip()
            status = (p / 'stat').read_text().rsplit(')', 1)[1].split()[0]
            if comm in {'lean', 'lake', 'leanchecker', 'leantar', 'strace'} and status != 'Z':
                active.append({'pid': p.name, 'comm': comm})
        except OSError:
            pass
    assert not active
    with open('/tmp/distance-sparsification-single-compiler.lock') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert Path(lock.name).stat().st_ino == 3849
    print(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      'scope': 'Offline publication verification; no Lean, checker, retry, or cache advice',
                      'source_commit': SOURCE, 'result': result['result'], 'receipts': 2,
                      'chunks_verified': count, 'manifest_entries_verified': len(entries) if entries else None,
                      'active_compilers_tracers': active, 'common_lock_free': True}, indent=2))


if __name__ == '__main__':
    main()
