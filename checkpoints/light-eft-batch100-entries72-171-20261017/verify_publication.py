"""Post-stop offline reconciliation only; no Lean, advice, fixtures or retries."""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys

B = Path(__file__).resolve().parent
R = B.parents[1]
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def main():
    state = load(B / 'batch-result.json')
    plan = load(B / 'PLAN.json')
    final = load(B / 'final-content-verification.json')
    lease = load(B / 'batch-lock.json')
    graph = load(R / plan['source_graph_path'])
    assert state['source_commit'] == plan['source_commit'] == SOURCE
    assert state['status'] == 'stopped-first-failure'
    assert not state['accepted_modules'] and not state['provisional_modules']
    assert len(plan['modules']) == plan['module_count'] == 100
    assert plan['stage_count'] == 300 and plan['stages_per_module'] == ['compile', 'resolve', 'replay']
    assert [{key: row[key] for key in graph[0]} for row in plan['modules']] == graph[71:171]
    assert sha(R / plan['source_graph_path']) == plan['source_graph_sha256']
    assert {row['module'] for row in plan['accepted_seeds']} == {row['module'] for row in graph[:71]}
    for name, digest in load(B / 'preparation-checks.json')['supervisor_byte_identity'].items():
        assert sha(B / name) == digest
        assert (B / name).read_bytes() == (R / 'checkpoints/light-eft-batch50-entries22-71-20261017' / name).read_bytes()
    expected = [(row['module'], phase) for row in plan['modules'] for phase in plan['stages_per_module']]
    assert len(expected) == 300
    assert [(row['module'], row['stage']) for row in state['stages']] == expected[:3]
    assert final['paths_checked'] == state['canonical_inputs']['rows'] == 74688
    assert final['matching'] and final['all_paths_attempted'] and not final['changes']
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256']
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    small = []
    scope = Counter()
    scope_bytes = 0
    scope_hash = hashlib.sha256()
    rows = 0
    # Reads the canonical inventory FILE, not each frozen dependency path.
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        rows += 1
        path = Path(row['path'])
        if path.parent == B and path.suffix == '.py' or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256']
            small.append(row)
        if row['advice_scope']:
            scope[row['advice_scope']] += 1
            scope_bytes += row['bytes']
            scope_hash.update((json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode())
    assert rows == 74688
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    assert scope == {'previously_accepted_evidence_data': 7129, 'reviewed_dependency_or_tool_object': 66961}
    assert scope_bytes == 11790867848
    advice = [load(B / 'bootstrap-recovery.json')] + [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    assert len(advice) == 3
    for row in advice:
        assert row['state'] == 'completed' and row['counts'] == dict(scope)
        assert row['scope_identity_sha256'] == scope_hash.hexdigest()
    receipts = []
    records = []
    for index, item in enumerate(state['stages']):
        path = B / item['receipt']
        receipt = load(path)
        receipts.append(receipt)
        assert receipt['attempt_id'] == item['attempt_id'] and receipt['source_commit'] == SOURCE
        assert receipt['harness_sha256'] == harness and receipt['canonical_input_inventory']['sha256'] == final['before_sha256']
        assert receipt['lock']['outer_acquired_ns'] == lease['acquired_ns']
        assert (receipt['lock']['device'], receipt['lock']['inode']) == (33, 3849)
        assert sha(B / receipt['source_snapshot']) == receipt['submitted_source_sha256']
        assert receipt['between_child_preservation_passed'] and receipt['kernel_no_children_verified']
        assert receipt['module'] not in {row['module'] for row in plan['accepted_seeds']}
        record = {key: receipt.get(key) for key in ['module', 'stage', 'attempt_id', 'created_utc', 'ended_utc', 'child_pid', 'exit', 'state', 'failure', 'argv', 'environment', 'submitted_source_sha256', 'memory_policy']}
        record['receipt'] = item['receipt']
        record['admission_visible_bytes'] = receipt['admission']['headroom']
        record['admission_host_MemAvailable_bytes'] = receipt['admission']['system_available']
        if index < 2:
            assert receipt['state'] == 'finished' and receipt['exit'] == 0 and 'failure' not in receipt
            assert receipt['direct_reaped'] and receipt['all_descendants_gone']
            assert receipt['waitid_wait4_status_match'] and receipt['terminal_confirmation']['terminal'] and receipt['terminal_confirmation']['status'] == 0
            assert receipt['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888], 'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
            raw = (path.parent / 'raw.log').read_text()
            warnings = len(re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M))
            assert warnings == 0
            if index == 0:
                assert re.findall(r"option 'arena_reserve': ([0-9]+) KiB", raw) == ['131072']
            else:
                assert raw == 'PASS: official checker resolution is exactly [LightSpanners.RetainedGraph]\n'
            samples = [json.loads(line) for line in (path.parent / 'samples.jsonl').read_text().splitlines()]
            assert samples[-1] == receipt['latest_decision_sample']
            assert receipt['sampled_rss_peak_bytes'] < 6442450944
            assert all(row['accounting']['headroom'] >= 1073741824 for row in samples)
            record.update(lean_warning_headers=warnings, sample_count=len(samples), sampled_rss_peak_bytes=receipt['sampled_rss_peak_bytes'], wait4_rss_bytes=receipt['wait4_maxrss_kib'] * 1024,
                minimum_runtime_visible_bytes=min(row['accounting']['headroom'] for row in samples), preexec_visible_bytes=receipt['preexec_admission']['headroom'])
        else:
            assert receipt['state'] == 'failed' and receipt['stage'] == 'replay'
            assert receipt['failure'] == "MemoryGuardError('Visible headroom below required floor')"
            assert 'child_pid' not in receipt and 'handshake' not in receipt and 'preexec_admission' not in receipt
            assert 'exit' not in receipt
            assert not (path.parent / 'raw.log').exists() and not (path.parent / 'samples.jsonl').exists()
            assert receipt['admission']['headroom'] == 4255289344 < receipt['memory_policy']['admission_visible_bytes'] == 4294967296
            assert receipt['admission']['system_available'] == 17676820480
            record.update(child_spawned=False, raw_log_absence='No child or log created: measured admission refused before spawn', shortfall_bytes=4294967296 - 4255289344)
        records.append(record)
    assert len(receipts) == len({row['attempt_id'] for row in receipts}) == 3
    assert len({row['child_pid'] for row in receipts if 'child_pid' in row}) == 2
    assert all(a['ended_ns'] < b['lock']['child_entry_ns'] for a, b in zip(receipts, receipts[1:]))
    assert receipts[-1]['ended_ns'] < final['started_ns']
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    assert len(ledger['objects']) == 72
    for row in ledger['objects']:
        original = Path(row['path'])
        preserved = B / 'preserved-objects' / original.relative_to(original.parents[1])
        assert sha(preserved) == sha(original) == row['sha256']
    for row in plan['accepted_seeds'] + plan['accepted_seed_evidence']:
        assert sha(R / row['path']) == row['sha256']
    for row in plan['modules']:
        raw = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=R)
        assert hashlib.sha256(raw).hexdigest() == sha(R / row['path']) == row['sha256']
    with open('/tmp/distance-sparsification-single-compiler.lock', 'r') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        stat = os.fstat(handle.fileno())
        assert (stat.st_dev, stat.st_ino) == (33, 3849)
        fcntl.flock(handle, fcntl.LOCK_UN)
    active = []
    for path in Path('/proc').iterdir():
        if path.name.isdigit():
            try:
                if (path / 'comm').read_text().strip() in ['lean', 'leanchecker', 'lake', 'strace', 'ltrace']:
                    active.append(path.name)
            except OSError:
                pass
    assert not active, active
    manifest = B / 'evidence-sha256.json'
    manifest_entries = None
    if manifest.exists():
        entries = load(manifest)
        files = {str(path.relative_to(B)) for path in B.rglob('*') if path.is_file() and '__pycache__' not in path.parts and path != manifest}
        assert files == {row['path'] for row in entries}
        tracked = set(subprocess.check_output(['git', 'ls-files', '-z', str(B.relative_to(R))], cwd=R).decode().split('\0'))
        for row in entries:
            path = B / row['path']
            assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256']
            assert str(path.relative_to(R)) in tracked
        manifest_entries = len(entries)
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline post-stop reconciliation; no third full frozen-input content pass, Lean, fixture, cache advice or retry',
        'source_commit': SOURCE, 'base_evidence': plan['base_evidence'], 'result': 'RETAINEDGRAPH_COMPILE_AND_EXACT_RESOLUTION_PASSED_REPLAY_ADMISSION_REFUSED_NO_CHILD',
        'graph_entries_inclusive': [72, 171], 'planned_new_modules': 100, 'planned_stages': 300, 'attempted_stage_receipts': 3, 'executed_tool_children': 2, 'passed_stages': 2,
        'failed_admission_stages': 1, 'skipped_stages': 297, 'completed_new_module_chains': 0, 'compiler_children': 1, 'resolver_children': 1, 'checker_children': 0,
        'accepted_seed_objects': 71, 'accepted_seed_recompilations': 0, 'accepted_seed_replays': 0, 'new_lifecycle_fixture_runs': 0, 'reviewed_supervisor_byte_identical': True,
        'canonical_inventory': state['canonical_inputs'], 'saved_final_full_content_match': True, 'full_input_content_pass_count': 2,
        'one_shared_lock_through_final_verification': True, 'unique_attempt_uuids': True, 'nonoverlap': True, 'all_spawned_children_reaped': True,
        'anchored_lean_warning_headers': 0, 'advice_scope_counts': dict(scope), 'advice_bytes_per_pass': scope_bytes, 'pre_initial_idle_passes': 1, 'between_child_idle_passes': 2,
        'replay_admission': {'measured_visible_bytes': 4255289344, 'required_visible_bytes': 4294967296, 'shortfall_bytes': 39677952, 'host_MemAvailable_bytes': 17676820480, 'checker_spawned': False},
        'preserved_project_objects': 72, 'new_recursive_axiom_audits': 0, 'new_ci_runs': 0, 'manifest_entries_verified': manifest_entries,
        'active_compilers_checkers_tracers': active, 'common_lock_free': True, 'stages': records}
    if '--write' in sys.argv:
        assert not manifest.exists(), 'Do not mutate manifest-bound evidence'
        (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'stages'}, indent=2))


if __name__ == '__main__':
    main()
