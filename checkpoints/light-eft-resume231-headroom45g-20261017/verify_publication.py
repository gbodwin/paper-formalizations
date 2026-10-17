"""Offline reconciliation only; no Lean, advice, extraction or fixture rerun."""
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
NEW = {'approved_archive_extension', 'approved_finalized_extension'}


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
    old = R / 'checkpoints/light-eft-resume231-headroom5g-20261017'
    old_plan = load(old / 'PLAN.json')
    assert state['source_commit'] == plan['source_commit'] == SOURCE
    assert state['status'] == 'retained-root-77-module-batch-passed-final-preservation'
    assert len(plan['modules']) == plan['module_count'] == 77 and plan['stage_count'] == 231
    assert [{key: row[key] for key in graph[0]} for row in plan['modules']] == graph[94:171]
    assert plan['first_compile_visible_gate'] == 4831838208
    assert plan['new_archive_authorities'] == old_plan['new_archive_authorities']
    assert plan['new_data_manifests'] == old_plan['new_data_manifests']
    assert plan['expanded_advice_manifests'] == old_plan['expanded_advice_manifests']
    assert (B / 'run_batch.py').read_text().replace('4831838208', '5368709120') == (old / 'run_batch.py').read_text()
    for name in ['batch_context.py', 'one_time_extension.py', 'finalized_scope.py', 'child_runner.py', 'decision_telemetry.py', 'exit_transition.py', 'shared_preservation.py', 'pilot_child.py', 'pilot_accounting.py', 'pilot_cache_advice.py']:
        assert (B / name).read_bytes() == (old / name).read_bytes()
    boundary = load(B / 'gate-boundary.json')
    assert boundary['passed'] and boundary['gate_bytes'] == 4831838208
    assert [(row['visible_bytes'], row['actual_accepted']) for row in boundary['cases']] == [(4831838208, True), (4831838207, False)]
    for name, digest in boundary['hashes'].items():
        assert sha(B / name) == digest
    expected = [(row['module'], phase) for row in plan['modules'] for phase in plan['stages_per_module']]
    assert len(expected) == 231 and [(row['module'], row['stage']) for row in state['stages']] == expected
    assert state['accepted_modules'] == state['provisional_modules'] == [row['module'] for row in plan['modules']]
    assert {row['module'] for row in plan['accepted_seeds']} == {row['module'] for row in graph[:94]}
    assert final['matching'] and final['all_paths_attempted'] and not final['changes']
    assert final['paths_checked'] == state['canonical_inputs']['rows'] == 79882
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256']
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    # Stream inventory records, not the dependency/archive contents again.
    small = []
    counts = Counter()
    sizes = Counter()
    digests = {'all': hashlib.sha256(), 'legacy': hashlib.sha256()}
    new_rows = {}
    count = 0
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        count += 1
        path = Path(row['path'])
        if path.parent == B and path.suffix == '.py' or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256']
            small.append(row)
        if row['advice_scope']:
            scope = row['advice_scope']
            counts[scope] += 1
            sizes[scope] += row['bytes']
            data = (json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode()
            digests['all'].update(data)
            if scope not in NEW:
                digests['legacy'].update(data)
            else:
                new_rows[row['path']] = row
    assert count == 79882
    assert counts == {'reviewed_dependency_or_tool_object': 66961, 'previously_accepted_evidence_data': 7129, 'reviewed_finalized_batch_data': 623,
                      'approved_archive_extension': 3809, 'approved_finalized_extension': 708}
    assert sizes['approved_archive_extension'] == 818684031 and sizes['approved_finalized_extension'] == 385582329
    # Metadata-only rederivation by the unchanged, reviewed finite selector.
    # It performs known-path metadata checks; no archive body hash/advice here.
    from one_time_extension import selected
    selected_rows = selected(R, plan)
    selected_new = {name: row for name, row in selected_rows.items() if row['scope'] in NEW}
    assert set(selected_new) == set(new_rows) and len(new_rows) == 4517
    assert sum(row['bytes'] for row in selected_new.values()) == 1204266360
    for name, row in new_rows.items():
        assert row['sha256'] == selected_new[name]['sha256'] and row['bytes'] == selected_new[name]['bytes']
    for authority in plan['new_archive_authorities'] + plan['new_data_manifests'] + plan['expanded_advice_manifests']:
        assert sha(R / authority['path']) == authority['sha256']
        assert subprocess.check_output(['git', 'show', authority['accepted_commit'] + ':' + authority['path']], cwd=R) == (R / authority['path']).read_bytes()
    verified = [json.loads(line) for line in (B / 'one-time-extension-verified.jsonl').read_text().splitlines()]
    assert {row['path']: row for row in verified} == new_rows
    advice = [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    finite = [row for row in advice if row['mode'] == 'one-time-extension']
    assert len(finite) == 1 and finite[0] == load(B / 'one-time-cache-advice.json')
    assert finite[0]['after']['headroom'] == 4875730944
    for row in advice:
        assert row['state'] == 'completed'
        if row['mode'] == 'one-time-extension':
            assert row['counts'] == dict(counts) and row['bytes'] == 13229175341
            assert row['scope_identity_sha256'] == digests['all'].hexdigest()
        else:
            assert row['mode'] == 'ordinary-legacy-only' and not set(row['counts']) & NEW
            assert row['counts'] == {key: value for key, value in counts.items() if key not in NEW}
            assert row['bytes'] == 12024908981 and row['scope_identity_sha256'] == digests['legacy'].hexdigest()
    assert load(B / 'extension-pass-claimed.json')['one_pass_only']
    assert load(B / 'expanded-scope-initial.json')['counts'] == {'reviewed_finalized_batch_data': 623}
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    receipts = []
    records = []
    for index, item in enumerate(state['stages']):
        path = B / item['receipt']
        receipt = load(path)
        receipts.append(receipt)
        assert receipt['attempt_id'] == item['attempt_id'] and receipt['source_commit'] == SOURCE
        assert receipt['state'] == item['state'] == 'finished' and receipt['exit'] == item['exit'] == 0 and 'failure' not in receipt
        assert receipt['harness_sha256'] == harness and receipt['canonical_input_inventory']['sha256'] == final['before_sha256']
        assert receipt['lock']['outer_acquired_ns'] == lease['acquired_ns'] and (receipt['lock']['device'], receipt['lock']['inode']) == (33, 3849)
        assert sha(B / receipt['source_snapshot']) == receipt['submitted_source_sha256']
        assert receipt['between_child_preservation_passed'] and receipt['direct_reaped'] and receipt['all_descendants_gone'] and receipt['kernel_no_children_verified']
        assert receipt['waitid_wait4_status_match'] and receipt['terminal_confirmation']['terminal'] and receipt['terminal_confirmation']['status'] == 0
        assert receipt['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888], 'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
        gate = 4831838208 if index == 0 else 4294967296 if receipt['stage'] == 'replay' else 3221225472
        assert receipt['memory_policy']['admission_visible_bytes'] == gate
        assert receipt['admission']['headroom'] >= gate and receipt['preexec_admission']['headroom'] >= gate
        assert receipt['admission']['system_available'] >= 3221225472 and receipt['preexec_admission']['system_available'] >= 3221225472
        assert receipt['memory_policy']['stop_visible_host_bytes'] == 1073741824
        assert receipt['memory_policy']['rss_observed_stop_bytes'] == 6442450944
        assert receipt['memory_policy']['per_cgroup_anon_growth_stop_bytes'] == 3221225472
        raw = (path.parent / 'raw.log').read_text()
        assert not re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M)
        if receipt['stage'] == 'compile':
            assert re.findall(r"option 'arena_reserve': ([0-9]+) KiB", raw) == ['131072']
        elif receipt['stage'] == 'resolve':
            assert raw == 'PASS: official checker resolution is exactly [' + receipt['module'] + ']\n'
        else:
            assert raw == 'replaying ' + receipt['module'] + '\n'
        samples = [json.loads(line) for line in (path.parent / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == receipt['latest_decision_sample']
        assert receipt['sampled_rss_peak_bytes'] < 6442450944
        assert all(row['accounting']['headroom'] >= 1073741824 and row['accounting']['system_available'] >= 1073741824 for row in samples)
        if receipt.get('process_teardown'):
            assert receipt['process_teardown']['confirmed_ns'] <= receipt['process_teardown']['deadline_ns']
        records.append({**{key: receipt.get(key) for key in ['module', 'stage', 'attempt_id', 'child_pid', 'created_utc', 'ended_utc', 'argv', 'environment', 'submitted_source_sha256']},
            'receipt': item['receipt'], 'state': 'finished', 'exit': 0, 'lean_warning_headers': 0, 'sample_count': len(samples),
            'sampled_rss_peak_bytes': receipt['sampled_rss_peak_bytes'], 'wait4_rss_bytes': receipt['wait4_maxrss_kib'] * 1024,
            'admission_visible_bytes': receipt['admission']['headroom'], 'preexec_visible_bytes': receipt['preexec_admission']['headroom'],
            'admission_host_bytes': receipt['admission']['system_available'], 'preexec_host_bytes': receipt['preexec_admission']['system_available'],
            'minimum_runtime_visible_bytes': min(row['accounting']['headroom'] for row in samples)})
    assert len(receipts) == len({row['attempt_id'] for row in receipts}) == len({row['child_pid'] for row in receipts}) == 231
    assert Counter(row['stage'] for row in receipts) == {'compile': 77, 'resolve': 77, 'replay': 77}
    assert all(a['ended_ns'] < b['lock']['child_entry_ns'] for a, b in zip(receipts, receipts[1:]))
    assert receipts[-1]['ended_ns'] < final['started_ns']
    assert not {row['module'] for row in receipts} & {row['module'] for row in plan['accepted_seeds']}
    assert receipts[0]['admission']['headroom'] == 4875730944 and receipts[0]['preexec_admission']['headroom'] == 4873035776
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    original = load(B / 'retained-root-binding.json')
    current = {row['path']: row for row in ledger['objects']}
    assert len(current) == 171 and len(original['objects']) == 94 and len(original['resolutions']) == 23
    assert all(current[row['path']] == row for row in original['objects'])
    for row in ledger['objects']:
        path = Path(row['path'])
        copy = B / 'preserved-objects' / path.relative_to(path.parents[1])
        assert sha(path) == sha(copy) == row['sha256']
    resolutions = {row['path'] for row in original['resolutions']} | {row['resolution_binding']['path'] for row in receipts if row['stage'] == 'resolve'}
    assert len(resolutions) == 100
    assert {str(path) for path in (R / plan['retained_work_root']).rglob('*') if path.is_file()} == set(current) | resolutions
    for row in original['resolutions']:
        assert sha(Path(row['path'])) == row['sha256']
    for row in plan['accepted_seed_evidence']:
        assert sha(R / row['path']) == row['sha256']
    for row in plan['modules']:
        raw = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=R)
        assert hashlib.sha256(raw).hexdigest() == sha(R / row['path']) == row['sha256']
    with open('/tmp/distance-sparsification-single-compiler.lock', 'r') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        info = os.fstat(handle.fileno())
        assert (info.st_dev, info.st_ino) == (33, 3849)
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
    manifest_entries = None
    manifest = B / 'evidence-sha256.json'
    if manifest.exists():
        entries = load(manifest)
        files = {str(path.relative_to(B)) for path in B.rglob('*') if path.is_file() and '__pycache__' not in path.parts and path != manifest}
        assert files == {row['path'] for row in entries}
        tracked = set(subprocess.check_output(['git', 'ls-files', '-z', str(B.relative_to(R))], cwd=R).decode().split('\0'))
        for row in entries:
            path = B / row['path']
            assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
            assert str(path.relative_to(R)) in tracked
        manifest_entries = len(entries)
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline reconciliation; no Lean, extraction, advice, fixture rerun or extra full input-content pass',
        'source_commit': SOURCE, 'base_evidence': plan['base_evidence'], 'result': 'ALL_231_STAGES_77_CHAINS_AND_FINAL_FULL_PRESERVATION_PASSED',
        'graph_entries_inclusive': [95, 171], 'planned_stages': 231, 'attempted_stages': 231, 'passed_stages': 231, 'failed_stages': 0, 'skipped_stages': 0,
        'completed_new_module_chains': state['accepted_modules'], 'successful_compilations': 77, 'exact_resolutions': 77, 'singleton_kernel_replays': 77,
        'accepted_seed_chains': 94, 'accepted_stage_reruns': 0, 'first_compile_gate_bytes': 4831838208, 'boundary_equality_accepted': True, 'boundary_one_byte_below_refused': True,
        'first_compile_admission_visible_bytes': 4875730944, 'first_compile_preexec_visible_bytes': 4873035776,
        'first_compile_admission_host_bytes': 17698488320, 'first_compile_preexec_host_bytes': 17694093312,
        'runtime_limits_unchanged': True, 'new_scope_A_files': 3809, 'new_scope_A_bytes': 818684031, 'new_scope_B_files': 708, 'new_scope_B_bytes': 385582329,
        'new_combined_scope_files': 4517, 'new_combined_scope_bytes': 1204266360, 'renewed_new_scope_hash_advice_passes': 1,
        'ordinary_legacy_only_advice_passes': len(advice) - 1, 'new_scope_repeated_in_ordinary_advice': False, 'archive_extractions': 0, 'stronger_provenance_claim': False,
        'canonical_inventory': state['canonical_inputs'], 'saved_final_full_preservation_match': True, 'full_input_content_pass_count': 2,
        'one_continuous_universal_lock': True, 'unique_uuids_and_pids': True, 'nonoverlap': True, 'all_children_reaped': True, 'anchored_lean_warning_headers': 0,
        'original_root_objects_unchanged': 94, 'original_resolutions_unchanged': 23, 'preserved_project_objects': 171, 'retained_resolution_files': 100,
        'new_lifecycle_fixture_runs': 0, 'new_exhaustive_audits': 0, 'new_ci_runs': 0, 'manifest_entries_verified': manifest_entries,
        'active_compilers_checkers_tracers': active, 'common_lock_free': True, 'stages': records}
    if '--write' in sys.argv:
        assert not manifest.exists()
        (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'stages'}, indent=2))


if __name__ == '__main__':
    main()
