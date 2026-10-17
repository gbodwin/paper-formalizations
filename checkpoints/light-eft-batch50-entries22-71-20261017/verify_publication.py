"""Post-execution offline reconciliation; never executes Lean or cache advice."""
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
    assert state['source_commit'] == plan['source_commit'] == SOURCE
    assert state['status'] == 'fifty-module-batch-passed-final-preservation'
    assert final['matching'] and final['all_paths_attempted'] and not final['changes']
    assert final['paths_checked'] == state['canonical_inputs']['rows'] == 74638
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256']
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    small = []
    scope = Counter()
    scope_bytes = 0
    scope_hash = hashlib.sha256()
    row_count = 0
    # Only the inventory FILE is read in full; dependency input contents are
    # not opened again. Small execution bindings are independently reconciled.
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        row_count += 1
        path = Path(row['path'])
        if path.parent == B and path.suffix == '.py' or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256']
            small.append(row)
        if row['advice_scope']:
            scope[row['advice_scope']] += 1
            scope_bytes += row['bytes']
            scope_hash.update((json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode())
    assert row_count == 74638
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    assert scope == {'previously_accepted_evidence_data': 7129, 'reviewed_dependency_or_tool_object': 66961}
    assert scope_bytes == 11790867848
    advice = [load(B / 'bootstrap-recovery.json')] + [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    for row in advice:
        assert row['state'] == 'completed' and row['counts'] == dict(scope)
        assert row['scope_identity_sha256'] == scope_hash.hexdigest()
    expected = [(row['module'], phase) for row in plan['modules'] for phase in plan['stages_per_module']]
    assert len(plan['modules']) == plan['module_count'] == 50
    assert plan['stage_count'] == 150
    graph = load(R / plan['source_graph_path'])
    assert [{key: row[key] for key in graph[0]} for row in plan['modules']] == graph[21:71]
    assert sha(R / plan['source_graph_path']) == plan['source_graph_sha256']
    assert {row['module'] for row in plan['accepted_seeds']} == {row['module'] for row in graph[:21]}
    for name in load(B / 'preparation-checks.json')['supervisor_byte_identity']:
        assert (B / name).read_bytes() == (R / 'checkpoints/light-eft-batch18-effective-reread-20261017' / name).read_bytes()
    assert len(expected) == plan['stage_count']
    assert [(row['module'], row['stage']) for row in state['stages']] == expected
    records = []
    receipts = []
    for item in state['stages']:
        path = B / item['receipt']
        receipt = load(path)
        receipts.append(receipt)
        assert receipt['attempt_id'] == item['attempt_id']
        assert receipt['source_commit'] == SOURCE and receipt['harness_sha256'] == harness
        assert receipt['state'] == item['state'] == 'finished' and receipt['exit'] == item['exit'] == 0
        assert 'failure' not in receipt
        assert receipt['direct_reaped'] and receipt['all_descendants_gone'] and receipt['kernel_no_children_verified']
        assert receipt['waitid_wait4_status_match'] and receipt['terminal_confirmation']['terminal'] and receipt['terminal_confirmation']['status'] == 0
        assert receipt['between_child_preservation_passed'] and receipt['canonical_input_inventory']['sha256'] == final['before_sha256']
        assert receipt['lock']['outer_acquired_ns'] == lease['acquired_ns']
        assert (receipt['lock']['device'], receipt['lock']['inode']) == (lease['device'], lease['inode']) == (33, 3849)
        assert sha(B / receipt['source_snapshot']) == receipt['submitted_source_sha256']
        assert receipt['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888], 'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
        raw = (path.parent / 'raw.log').read_text()
        warnings = len(re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M))
        assert warnings == 0
        if receipt['stage'] == 'compile':
            assert re.findall(r"option 'arena_reserve': ([0-9]+) KiB", raw) == ['131072']
        if receipt['stage'] == 'replay':
            assert raw == 'replaying ' + receipt['module'] + '\n'
        if receipt['stage'] == 'resolve':
            assert raw == 'PASS: official checker resolution is exactly [' + receipt['module'] + ']\n'
        samples = [json.loads(line) for line in (path.parent / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == receipt['latest_decision_sample']
        rereads = 0
        no_mm_rereads = 0
        for sample in samples:
            memory = sample.get('observed_process_memory', {})
            if memory.get('rss') is not None:
                assert memory['rss'] <= receipt['sampled_rss_peak_bytes'] < 6442450944
            life = sample['exit_lifecycle']
            assert sample['accounting']['headroom'] >= 1073741824
            for row in life['threads']:
                if 'fd_transition_reread' not in row:
                    continue
                rereads += 1
                fresh = row['fd_transition_reread']
                effective = life['effective_classifications'].get(str(row['pid']))
                if fresh.get('known_tid_positively_gone'):
                    assert effective is None
                else:
                    assert effective is not None
                    assert effective['state'] == fresh['state'] and effective['rss'] == fresh['rss'] and effective['vm'] == fresh['vm']
                    assert effective['start_ticks'] == fresh['start_ticks']
                    if effective['no_mm']:
                        no_mm_rereads += 1
                if isinstance(row.get('rss'), int):
                    assert sample['observed_process_memory']['rss'] >= row['rss']
            selected = sample.get('process_memory', {})
            if selected.get('source_tid') is not None:
                assert selected['tgid'] == receipt['child_pid']
                assert selected['start_ticks'] == receipt['tid_catalog'][str(selected['source_tid'])]['start_ticks']
                assert life['live_lock_verification']['tid'] == selected['source_tid']
                assert selected['aggregation'].endswith('never summed')
        if receipt.get('process_teardown'):
            assert receipt['process_teardown']['confirmed_ns'] <= receipt['process_teardown']['deadline_ns']
        records.append({'module': receipt['module'], 'stage': receipt['stage'], 'attempt_id': receipt['attempt_id'], 'receipt': item['receipt'],
            'submitted_source_sha256': receipt['submitted_source_sha256'], 'child_pid': receipt['child_pid'], 'created_utc': receipt['created_utc'], 'ended_utc': receipt['ended_utc'],
            'argv': receipt['argv'], 'environment': receipt['environment'], 'exit': 0, 'state': 'finished', 'lean_warning_headers': warnings,
            'sample_count': len(samples), 'sampled_rss_peak_bytes': receipt['sampled_rss_peak_bytes'], 'wait4_rss_bytes': receipt['wait4_maxrss_kib'] * 1024,
            'admission_visible_bytes': receipt['admission']['headroom'], 'preexec_visible_bytes': receipt['preexec_admission']['headroom'],
            'minimum_runtime_visible_bytes': min(row['accounting']['headroom'] for row in samples), 'fd_transition_rereads': rereads, 'effective_no_mm_rereads': no_mm_rereads})
    assert len(receipts) == len({row['attempt_id'] for row in receipts}) == len({row['child_pid'] for row in receipts}) == plan['stage_count']
    assert Counter(row['stage'] for row in receipts) == {'compile': 50, 'resolve': 50, 'replay': 50}
    assert all(a['ended_ns'] < b['lock']['child_entry_ns'] for a, b in zip(receipts, receipts[1:]))
    assert receipts[-1]['ended_ns'] < final['started_ns']
    assert all(row['module'] not in {seed['module'] for seed in plan['accepted_seeds']} for row in receipts )
    assert state['accepted_modules'] == state['provisional_modules'] == [row['module'] for row in plan['modules']]
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    assert len(ledger['objects']) == len(plan['accepted_seeds']) + plan['module_count'] == 71
    for row in ledger['objects']:
        original = Path(row['path'])
        preserved = B / 'preserved-objects' / original.relative_to(original.parents[1])
        assert sha(preserved) == sha(original) == row['sha256']
    for row in plan['accepted_seeds']:
        assert sha(R / row['path']) == row['sha256']
    for row in plan['accepted_seed_evidence']:
        assert sha(R / row['path']) == row['sha256']
    for row in plan['modules']:
        raw = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=R)
        assert hashlib.sha256(raw).hexdigest() == sha(R / row['path']) == row['sha256']
    assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=R)
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
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'source_commit': SOURCE, 'base_evidence': plan['base_evidence'],
        'scope': 'Post-execution offline reconciliation; no additional full frozen-input content pass, Lean, fixture or cache-advice invocation',
        'result': 'ALL_150_STAGES_AND_FINAL_FULL_PRESERVATION_PASSED', 'qualified_module_chains': state['accepted_modules'],
        'planned_stages': plan['stage_count'], 'attempted_stages': len(receipts), 'skipped_stages': 0, 'compiler_invocations': 50, 'resolver_invocations': 50, 'singleton_kernel_replays': 50,
        'accepted_seed_recompilations': 0, 'accepted_seed_replays': 0, 'new_lifecycle_fixture_runs': 0, 'reviewed_supervisor_byte_identical': True,
        'canonical_inventory': state['canonical_inputs'], 'saved_final_full_content_match': True, 'full_input_content_pass_count': 2,
        'one_shared_lock_through_final_verification': True, 'unique_uuids_and_child_pids': True, 'nonoverlap': True, 'all_children_reaped': True,
        'anchored_lean_warning_headers': 0, 'advice_scope_counts': dict(scope), 'advice_bytes_per_pass': scope_bytes, 'pre_initial_idle_passes': 1, 'between_child_idle_passes': len(advice) - 1,
        'fd_transition_rereads': sum(row['fd_transition_rereads'] for row in records), 'effective_no_mm_rereads': sum(row['effective_no_mm_rereads'] for row in records),
        'new_recursive_axiom_audits': 0, 'new_ci_runs': 0, 'preserved_project_objects': 71, 'manifest_entries_verified': manifest_entries,
        'active_compilers_checkers_tracers': active, 'common_lock_free': True, 'stages': records}
    if '--write' in sys.argv:
        assert not manifest.exists(), 'Do not mutate manifest-bound evidence'
        (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'stages'}, indent=2))


if __name__ == '__main__':
    main()
