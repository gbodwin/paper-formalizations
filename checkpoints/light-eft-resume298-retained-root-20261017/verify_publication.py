"""Offline post-stop reconciliation; never launches Lean or cache advice."""
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
    assert plan['chosen_resume_plan'].startswith('Retain exact output/search root')
    assert plan['stage_count'] == 298 and plan['resume_first_module_phases'] == ['replay']
    assert len(plan['modules']) == 100 and len(plan['accepted_seeds']) == 72
    assert [{key: row[key] for key in graph[0]} for row in plan['modules']] == graph[71:171]
    assert sha(R / plan['source_graph_path']) == plan['source_graph_sha256']
    assert {row['module'] for row in plan['accepted_seeds']} == {row['module'] for row in graph[:72]}
    expected = [(row['module'], phase) for index, row in enumerate(plan['modules']) for phase in (plan['resume_first_module_phases'] if index == 0 else plan['stages_per_module'])]
    assert len(expected) == 298 and [(row['module'], row['stage']) for row in state['stages']] == expected[:68]
    assert state['accepted_modules'] == state['provisional_modules'] == [row['module'] for row in plan['modules'][:23]]
    assert state['current_module'] == graph[94]['module'] == 'LightEFTSpanners.BernoulliFlagEncoding'
    for name, digest in load(B / 'preparation-checks.json')['supervisor_byte_identity'].items():
        assert sha(B / name) == digest
        assert (B / name).read_bytes() == (R / 'checkpoints/light-eft-batch100-entries72-171-20261017' / name).read_bytes()
    assert final['matching'] and final['all_paths_attempted'] and not final['changes']
    assert final['paths_checked'] == state['canonical_inputs']['rows'] == 75320
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256']
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    # Only the canonical inventory FILE and small control inputs are read;
    # this is not another full frozen-input/dependency-content pass.
    scopes = Counter()
    scope_bytes = 0
    scope_digest = hashlib.sha256()
    expanded = {}
    small = []
    count = 0
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        count += 1
        path = Path(row['path'])
        if path.parent == B and path.suffix == '.py' or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256']
            small.append(row)
        if row['advice_scope']:
            scopes[row['advice_scope']] += 1
            scope_bytes += row['bytes']
            scope_digest.update((json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode())
        if row['advice_scope'] == 'reviewed_finalized_batch_data':
            expanded[row['path']] = row
    assert count == 75320
    assert scopes == {'previously_accepted_evidence_data': 7129, 'reviewed_dependency_or_tool_object': 66961, 'reviewed_finalized_batch_data': 623}
    assert scope_bytes == 12024908981
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    selected = {}
    top = {'inputs.jsonl', 'output-records.jsonl', 'cache-advice.jsonl', 'result-reconciliation.json', 'module-status.json', 'source-toolchain-object-hashes.json', 'publication-checks.json'}
    for authority in plan['expanded_advice_manifests']:
        manifest = R / authority['path']
        assert sha(manifest) == authority['sha256']
        assert subprocess.check_output(['git', 'show', authority['accepted_commit'] + ':' + authority['path']], cwd=R) == manifest.read_bytes()
        for row in load(manifest):
            parts = Path(row['path']).parts
            if row['path'] in top or len(parts) == 3 and parts[0] == 'attempts' and parts[2] in {'receipt.json', 'samples.jsonl', 'raw.log'}:
                selected[str(manifest.parent / row['path'])] = row
    assert set(selected) == set(expanded) and len(selected) == 623
    assert sum(row['bytes'] for row in selected.values()) == 234041133
    for path, row in expanded.items():
        assert row['sha256'] == selected[path]['sha256'] and row['bytes'] == selected[path]['bytes']
    verified = [json.loads(line) for line in (B / 'expanded-scope-verified.jsonl').read_text().splitlines()]
    assert {row['path']: row for row in verified} == expanded
    initial_scope = load(B / 'expanded-scope-initial.json')
    assert initial_scope['state'] == 'completed' and initial_scope['counts'] == {'reviewed_finalized_batch_data': 623}
    assert initial_scope['bytes'] == 234041133
    advice = [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    for row in advice:
        assert row['state'] == 'completed' and row['counts'] == dict(scopes)
        assert row['bytes'] == scope_bytes and row['scope_identity_sha256'] == scope_digest.hexdigest()
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
        assert receipt['direct_reaped'] and receipt['all_descendants_gone']
        assert receipt['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888], 'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
        raw = (path.parent / 'raw.log').read_text()
        warnings = len(re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M))
        assert warnings == 0
        samples = [json.loads(line) for line in (path.parent / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == receipt['latest_decision_sample']
        if index < 67:
            assert receipt['state'] == 'finished' and receipt['exit'] == 0 and 'failure' not in receipt
            assert receipt['waitid_wait4_status_match'] and receipt['terminal_confirmation']['terminal'] and receipt['terminal_confirmation']['status'] == 0
            assert all(row['accounting']['headroom'] >= 1073741824 for row in samples)
            if receipt['stage'] == 'replay':
                assert raw == 'replaying ' + receipt['module'] + '\n'
            if receipt['stage'] == 'resolve':
                assert raw == 'PASS: official checker resolution is exactly [' + receipt['module'] + ']\n'
        else:
            assert receipt['state'] == 'failed' and receipt['exit'] == -9
        if receipt['stage'] == 'compile':
            assert re.findall(r"option 'arena_reserve': ([0-9]+) KiB", raw) == ['131072']
        records.append({**{key: receipt.get(key) for key in ['module', 'stage', 'attempt_id', 'child_pid', 'created_utc', 'ended_utc', 'state', 'exit', 'failure', 'argv', 'environment', 'submitted_source_sha256']},
            'receipt': item['receipt'], 'lean_warning_headers': warnings, 'sample_count': len(samples), 'sampled_rss_peak_bytes': receipt['sampled_rss_peak_bytes'],
            'wait4_rss_bytes': receipt['wait4_maxrss_kib'] * 1024, 'admission_visible_bytes': receipt['admission']['headroom'], 'preexec_visible_bytes': receipt['preexec_admission']['headroom'],
            'minimum_runtime_visible_bytes': min(row['accounting']['headroom'] for row in samples)})
    assert len(receipts) == len({row['attempt_id'] for row in receipts}) == len({row['child_pid'] for row in receipts}) == 68
    assert Counter(row['stage'] for row in receipts) == {'compile': 23, 'resolve': 22, 'replay': 23}
    assert all(a['ended_ns'] < b['lock']['child_entry_ns'] for a, b in zip(receipts, receipts[1:]))
    assert receipts[-1]['ended_ns'] < final['started_ns']
    assert receipts[0]['module'] == 'LightSpanners.RetainedGraph' and receipts[0]['stage'] == 'replay'
    assert not any(row['module'] in {seed['module'] for seed in plan['accepted_seeds']} for row in receipts[1:])
    assert receipts[0]['admission']['headroom'] == 4444446720 >= 4294967296
    assert receipts[0]['preexec_admission']['headroom'] == 4439908352 >= 4294967296
    failed = receipts[-1]
    stop = failed['stop_decision_sample']
    assert stop == failed['latest_decision_sample']
    assert failed['stop_decision_errors'] == ["MemoryGuardError('Visible headroom below required floor')"]
    assert stop['accounting']['headroom'] == 1073291264 < 1073741824
    assert stop['accounting']['system_available'] == 17029275648
    assert stop['observed_process_memory']['rss'] == 3407331328 < 6442450944
    assert failed['memory_stop_signal_sent']
    assert stop['sample_finished_ns'] <= failed['memory_stop_signal_started_ns'] <= failed['memory_stop_signal_finished_ns']
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    assert len(ledger['objects']) == 94 and not state['partial_output_bindings']
    for row in ledger['objects']:
        original = Path(row['path'])
        preserved = B / 'preserved-objects' / original.relative_to(original.parents[1])
        assert sha(preserved) == sha(original) == row['sha256']
    initial = load(B / 'retained-root-binding.json')
    assert len(initial['objects']) == 72 and initial['exact_initial_membership']
    current = {row['path']: row for row in ledger['objects']}
    assert all(current[row['path']] == row for row in initial['objects'])
    assert sha(Path(initial['resolution']['path'])) == initial['resolution']['sha256']
    resolution_paths = {initial['resolution']['path']} | {receipt['resolution_binding']['path'] for receipt in receipts if receipt['stage'] == 'resolve'}
    assert {str(path) for path in (R / plan['retained_work_root']).rglob('*') if path.is_file()} == set(current) | resolution_paths
    for row in plan['accepted_seed_evidence']:
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
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline post-stop reconciliation; no extra full input-content pass, Lean, fixture, advice or retry',
        'source_commit': SOURCE, 'base_evidence': plan['base_evidence'], 'chosen_plan': 'Retained output/search root and RetainedGraph resolution; exactly 298 stages',
        'result': '67_STAGES_PASSED_23_CHAINS_FINAL_PRESERVATION_PASSED_BERNOULLI_COMPILE_RUNTIME_HEADROOM_STOP',
        'planned_stages': 298, 'attempted_stages': 68, 'passed_stages': 67, 'failed_runtime_stages': 1, 'skipped_stages': 230,
        'completed_new_module_chains': state['accepted_modules'], 'compiler_children': 23, 'successful_compilations': 22, 'resolver_children': 22, 'checker_children': 23, 'successful_kernel_replays': 23,
        'qualified_seed_chains': 71, 'retainedgraph_recompilations': 0, 'retainedgraph_resolutions': 0, 'qualified_seed_replays': 0,
        'retainedgraph_replay_admission_bytes': 4444446720, 'retainedgraph_replay_preexec_bytes': 4439908352,
        'expanded_scope_files': 623, 'expanded_scope_bytes': 234041133, 'expanded_scope_ceiling_not_exceeded': True,
        'combined_advice_scope_counts': dict(scopes), 'combined_advice_bytes_per_pass': scope_bytes, 'ordinary_combined_idle_passes': len(advice),
        'new_lifecycle_fixture_runs': 0, 'reviewed_supervisor_byte_identical': True, 'canonical_inventory': state['canonical_inputs'],
        'saved_final_full_content_match': True, 'full_input_content_pass_count': 2, 'one_shared_lock_through_final_verification': True,
        'unique_uuids_and_child_pids': True, 'nonoverlap': True, 'all_children_reaped': True, 'anchored_lean_warning_headers': 0,
        'runtime_stop': {'module': failed['module'], 'stage': failed['stage'], 'attempt_id': failed['attempt_id'], 'utc': stop['sample_utc'], 'visible_headroom_bytes': 1073291264,
            'running_floor_bytes': 1073741824, 'shortfall_bytes': 450560, 'observed_rss_bytes': 3407331328, 'host_MemAvailable_bytes': 17029275648, 'SIGKILL_sent': True, 'exit': -9},
        'preserved_project_objects': 94, 'original_root_objects_unchanged': 72, 'original_resolution_unchanged': True,
        'new_recursive_axiom_audits': 0, 'new_ci_runs': 0, 'manifest_entries_verified': manifest_entries,
        'active_compilers_checkers_tracers': active, 'common_lock_free': True, 'stages': records}
    if '--write' in sys.argv:
        assert not manifest.exists()
        (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
        (B / 'runtime-stop-sample.json').write_text(json.dumps(stop, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'stages'}, indent=2))


if __name__ == '__main__':
    main()
