"""Offline evidence reconciliation; no compiler, advice, fixture or input-body pass."""
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

B = Path('/workspace/light-eft-verification/checkpoints/light-eft-batch100-entries272-371-20261017')
R = B.parents[1]
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'
BASE = '7c5688da20649e4825015886b6b75536fe2b83e4'
NEW = {'approved_archive_extension', 'approved_finalized_extension'}


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def main():
    plan = load(B / 'PLAN.json')
    state = load(B / 'batch-result.json')
    final = load(B / 'final-content-verification.json')
    lease = load(B / 'batch-lock.json')
    old = R / 'checkpoints/light-eft-batch100-entries172-271-20261017'
    prior = load(old / 'PLAN.json')
    graph = load(R / plan['source_graph_path'])
    assert plan['source_commit'] == state['source_commit'] == SOURCE
    assert plan['base_evidence'] == BASE
    assert plan['graph_entries_inclusive'] == [272, 371]
    assert [{k: row[k] for k in graph[0]} for row in plan['modules']] == graph[271:371]
    assert len(plan['modules']) == 100 and plan['stage_count'] == 300
    assert plan['modules'][0]['module'] == 'LightEFTSpanners.SeededSubtreePacking'
    assert plan['modules'][-1]['module'] == 'LightEFTSpanners.StoredCandidateDrawLookup'
    assert graph[371]['module'] == 'LightEFTSpanners.StoredOriginalCandidateRecords'
    available = {row['module'] for row in graph[:271]}
    edge_count = 0
    for row in plan['modules']:
        assert set(row['project_imports']) <= available
        edge_count += len(row['project_imports'])
        available.add(row['module'])
        raw = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=R)
        assert hashlib.sha256(raw).hexdigest() == row['sha256'] == sha(R / row['path'])
    assert edge_count == 130
    assert {x['module'] for x in plan['accepted_seeds']} == {x['module'] for x in graph[:271]}
    for key in ['resource_controls', 'new_archive_authorities', 'new_data_manifests', 'expanded_advice_manifests', 'retained_work_root']:
        assert plan[key] == prior[key]
    unchanged = ['bootstrap_recovery.py', 'one_time_extension.py', 'finalized_scope.py', 'child_runner.py', 'decision_telemetry.py', 'exit_transition.py', 'shared_preservation.py', 'pilot_child.py', 'pilot_accounting.py', 'pilot_cache_advice.py', 'toolchain-object-advice.json']
    for name in unchanged:
        assert (B / name).read_bytes() == (old / name).read_bytes()
    assert 'return PLAN[\'first_compile_visible_gate\']' not in (B / 'batch_context.py').read_text()
    assert plan['first_compile_visible_gate'] == 3221225472
    assert final['matching'] and not final['changes'] and final['all_paths_attempted']
    assert final['paths_checked'] == state['canonical_inputs']['rows']
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256']
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    counts = Counter()
    sizes = Counter()
    new_rows = {}
    small = []
    advice_digests = {'all': hashlib.sha256(), 'legacy': hashlib.sha256()}
    line_count = 0
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        line_count += 1
        path = Path(row['path'])
        if (path.parent == B and path.suffix == '.py') or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256']
            small.append(row)
        scope = row['advice_scope']
        if scope:
            counts[scope] += 1
            sizes[scope] += row['bytes']
            data = (json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode()
            advice_digests['all'].update(data)
            if scope not in NEW:
                advice_digests['legacy'].update(data)
            else:
                new_rows[row['path']] = row
    assert line_count == final['paths_checked'] == 80255
    assert counts == {'reviewed_dependency_or_tool_object': 66961, 'previously_accepted_evidence_data': 7129, 'reviewed_finalized_batch_data': 623, 'approved_archive_extension': 3809, 'approved_finalized_extension': 708}
    assert sizes['approved_archive_extension'] == 818684031 and sizes['approved_finalized_extension'] == 385582329
    sys.path.insert(0, str(B))
    from one_time_extension import selected
    selected_rows = selected(R, plan)  # Known-path metadata only; no advice/body hashing.
    selected_new = {name: row for name, row in selected_rows.items() if row['scope'] in NEW}
    assert set(selected_new) == set(new_rows) and len(new_rows) == 4517
    for name, row in new_rows.items():
        assert row['sha256'] == selected_new[name]['sha256'] and row['bytes'] == selected_new[name]['bytes']
    verified_new = [json.loads(line) for line in (B / 'one-time-extension-verified.jsonl').read_text().splitlines()]
    assert {row['path']: row for row in verified_new} == new_rows
    for authority in plan['new_archive_authorities'] + plan['new_data_manifests'] + plan['expanded_advice_manifests']:
        assert sha(R / authority['path']) == authority['sha256']
        assert subprocess.check_output(['git', 'show', authority['accepted_commit'] + ':' + authority['path']], cwd=R) == (R / authority['path']).read_bytes()
    advice = [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    finite = [row for row in advice if row['mode'] == 'one-time-extension']
    assert len(finite) == 1 and finite[0] == load(B / 'one-time-cache-advice.json')
    for row in advice:
        assert row['state'] == 'completed'
        if row['mode'] == 'one-time-extension':
            assert row['counts'] == dict(counts) and row['bytes'] == 13229175341
            assert row['scope_identity_sha256'] == advice_digests['all'].hexdigest()
        else:
            assert row['mode'] == 'ordinary-legacy-only' and not set(row['counts']) & NEW
            assert row['counts'] == {k: v for k, v in counts.items() if k not in NEW}
            assert row['bytes'] == 12024908981 and row['scope_identity_sha256'] == advice_digests['legacy'].hexdigest()
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    expected = [(row['module'], phase) for row in plan['modules'] for phase in plan['stages_per_module']]
    assert [(row['module'], row['stage']) for row in state['stages']] == expected[:len(state['stages'])]
    receipts = []
    records = []
    for item in state['stages']:
        path = B / item['receipt']
        receipt = load(path)
        receipts.append(receipt)
        assert receipt['source_commit'] == SOURCE and receipt['attempt_id'] == item['attempt_id']
        assert receipt['harness_sha256'] == harness and receipt['canonical_input_inventory']['sha256'] == final['before_sha256']
        assert receipt['lock']['outer_acquired_ns'] == lease['acquired_ns'] and [receipt['lock']['device'], receipt['lock']['inode']] == [33, 3849]
        assert sha(B / receipt['source_snapshot']) == receipt['submitted_source_sha256']
        gate = 4294967296 if receipt['stage'] == 'replay' else 3221225472
        assert receipt['memory_policy']['admission_visible_bytes'] == gate
        assert receipt['memory_policy']['stop_visible_host_bytes'] == 1073741824
        assert receipt['memory_policy']['rss_observed_stop_bytes'] == 6442450944
        assert receipt['memory_policy']['per_cgroup_anon_growth_stop_bytes'] == 3221225472
        successful = receipt['state'] == 'finished' and receipt.get('exit') == 0 and 'failure' not in receipt
        if not successful and not receipt.get('child_pid'):
            assert receipt['kernel_no_children_verified']
            assert receipt['stage'] == 'replay' and receipt['admission']['headroom'] == 3980185600 < gate == 4294967296
            assert receipt.get('preexec_admission') is None
        if receipt.get('child_pid'):
            assert receipt['direct_reaped'] and receipt['all_descendants_gone'] and receipt['kernel_no_children_verified']
            assert receipt['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888], 'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
        for name, binding in receipt.get('completed_logs', {}).items():
            file = path.parent / name
            assert sha(file) == binding['sha256'] and file.stat().st_size == binding['bytes']
        raw = (path.parent / 'raw.log').read_text() if (path.parent / 'raw.log').exists() else ''
        warnings = re.findall(r'^.*\.lean:\d+:\d+: warning:.*$', raw, re.M)
        samples = [json.loads(line) for line in (path.parent / 'samples.jsonl').read_text().splitlines()] if (path.parent / 'samples.jsonl').exists() else []
        if successful:
            assert receipt['between_child_preservation_passed'] and receipt['waitid_wait4_status_match']
            assert receipt['terminal_confirmation']['terminal'] and receipt['terminal_confirmation']['status'] == 0
            assert receipt['admission']['headroom'] >= gate and receipt['preexec_admission']['headroom'] >= gate
            assert receipt['admission']['system_available'] >= 3221225472 and receipt['preexec_admission']['system_available'] >= 3221225472
            assert samples and samples[-1] == receipt['latest_decision_sample']
            assert not warnings and receipt['sampled_rss_peak_bytes'] < 6442450944
            assert all(row['accounting']['headroom'] >= 1073741824 and row['accounting']['system_available'] >= 1073741824 for row in samples)
            if receipt.get('process_teardown'):
                assert receipt['process_teardown']['confirmed_ns'] <= receipt['process_teardown']['deadline_ns']
            if receipt['stage'] == 'compile':
                assert re.findall(r"option 'arena_reserve': ([0-9]+) KiB", raw) == ['131072']
            elif receipt['stage'] == 'resolve':
                assert raw == 'PASS: official checker resolution is exactly [' + receipt['module'] + ']\n'
            else:
                assert raw == 'replaying ' + receipt['module'] + '\n'
        records.append({**{key: receipt.get(key) for key in ['module', 'stage', 'attempt_id', 'child_pid', 'created_utc', 'ended_utc', 'argv', 'environment', 'submitted_source_sha256', 'failure', 'memory_stop_reason']}, 'receipt': item['receipt'], 'state': receipt['state'], 'exit': receipt.get('exit'), 'successful': successful, 'warning_headers': warnings, 'samples': len(samples), 'sampled_rss_peak_bytes': receipt.get('sampled_rss_peak_bytes'), 'admission_visible_bytes': receipt.get('admission', {}).get('headroom'), 'preexec_visible_bytes': receipt.get('preexec_admission', {}).get('headroom')})
    assert len(receipts) == len({row['attempt_id'] for row in receipts})
    pids = [row['child_pid'] for row in receipts if row.get('child_pid')]
    assert len(pids) == len(set(pids))
    assert len(receipts) == 3 and len(pids) == 2
    assert Counter(row['stage'] for row in receipts if row.get('child_pid')) == {'compile': 1, 'resolve': 1}
    assert Counter(row['stage'] for row in receipts if row.get('child_pid') and row['stage'] == 'replay') == {}
    assert all(a['ended_ns'] < b['lock']['child_entry_ns'] for a, b in zip(receipts, receipts[1:]))
    assert not receipts or receipts[-1]['ended_ns'] < final['started_ns']
    assert not {row['module'] for row in receipts} & {row['module'] for row in plan['accepted_seeds']}
    success = [row for row in records if row['successful']]
    complete = [row['module'] for row in plan['modules'] if all(any(x['module'] == row['module'] and x['stage'] == phase for x in success) for phase in plan['stages_per_module'])]
    assert state['accepted_modules'] == state['provisional_modules'] == complete
    if len(receipts) == 300 and len(success) == 300:
        assert len(complete) == 100 and state['status'] == 'retained-root-100-module-batch-passed-final-preservation'
    else:
        assert len(records) - len(success) == 1 and state['status'] == 'stopped-first-failure'
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    original = load(B / 'retained-root-binding.json')
    current = {row['path']: row for row in ledger['objects']}
    assert len(original['objects']) == 271 and len(original['resolutions']) == 200
    assert all(current[row['path']] == row for row in original['objects'])
    for row in ledger['objects']:
        path = Path(row['path'])
        copy = B / 'preserved-objects' / path.relative_to(path.parents[1])
        assert sha(path) == sha(copy) == row['sha256']
    resolutions = {row['path'] for row in original['resolutions']} | {row['resolution_binding']['path'] for row in receipts if 'resolution_binding' in row}
    for row in original['resolutions']:
        assert sha(Path(row['path'])) == row['sha256']
    partial = {row['path'] for row in state.get('partial_output_bindings', [])}
    partial |= {row['failed_resolution_binding']['path'] for row in receipts if 'failed_resolution_binding' in row}
    assert {str(path) for path in (R / plan['retained_work_root']).rglob('*') if path.is_file()} == set(current) | resolutions | partial
    for row in plan['accepted_seed_evidence']:
        assert sha(R / row['path']) == row['sha256']
    with open('/tmp/distance-sparsification-single-compiler.lock') as handle:
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
    assert not active
    manifest = B / 'evidence-sha256.json'
    manifest_count = None
    if manifest.exists():
        entries = load(manifest)
        files = {str(path.relative_to(B)) for path in B.rglob('*') if path.is_file() and '__pycache__' not in path.parts and path != manifest}
        assert files == {row['path'] for row in entries}
        tracked = set(subprocess.check_output(['git', 'ls-files', '-z', str(B.relative_to(R))], cwd=R).decode().split('\0'))
        for row in entries:
            path = B / row['path']
            assert sha(path) == row['sha256'] and path.stat().st_size == row['bytes'] and str(path.relative_to(R)) in tracked
        manifest_count = len(entries)
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline reconciliation only; no Lean/advice/fixtures or extra full input-body pass', 'source_commit': SOURCE, 'base_evidence': BASE, 'batch_status': state['status'], 'graph_entries_inclusive': [272, 371], 'excluded_entry_372': graph[371]['module'], 'project_import_edges': edge_count, 'planned_stages': 300, 'attempted_stages': len(records), 'passed_stages': len(success), 'failed_stages': len(records) - len(success), 'unattempted_stages': 300 - len(records), 'successful_by_stage': dict(Counter(row['stage'] for row in success)), 'completed_new_module_chains': complete, 'independent_acceptance': 'pending', 'executed_Lean_children': 2, 'executed_kernel_replays': 0, 'refused_replay_admissions_without_child': 1, 'accepted_seeds': 271, 'accepted_seed_reruns': 0, 'gate_exception': False, 'compile_resolve_gate_bytes': 3221225472, 'replay_gate_bytes': 4294967296, 'runtime_limits_unchanged': True, 'renewed_new_scope_passes': 1, 'new_scope_files': 4517, 'new_scope_bytes': 1204266360, 'ordinary_legacy_only_passes': len(advice) - 1, 'new_scope_repeated': False, 'canonical_inventory': state['canonical_inputs'], 'saved_final_full_preservation_match': True, 'full_input_content_passes': 2, 'one_continuous_lock': True, 'all_children_reaped': True, 'nonoverlap': True, 'unique_uuids_and_pids': True, 'original_objects_unchanged': 271, 'original_resolutions_unchanged': 200, 'retained_objects': len(current), 'retained_resolutions': len(resolutions), 'partial_paths_preserved': sorted(partial), 'warning_headers': sum(len(row['warning_headers']) for row in records), 'maximum_sampled_rss_bytes': max([row.get('sampled_rss_peak_bytes') or 0 for row in records], default=0), 'new_lifecycle_fixtures': 0, 'new_exhaustive_audits': 0, 'new_ci': 0, 'manifest_entries_verified': manifest_count, 'active_compilers_checkers_tracers': active, 'common_lock_free': True, 'stages': records}
    if '--write' in sys.argv:
        assert not manifest.exists()
        (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key not in ['stages', 'completed_new_module_chains']}, indent=2))


if __name__ == '__main__':
    main()
