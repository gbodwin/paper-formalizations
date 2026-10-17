"""Offline evidence reconciliation; never launches Lean, fixtures, or cache advice.

Added for publication after execution. Hashes the canonical inventory FILE,
small execution inputs and preserved evidence/objects, never all frozen paths.
"""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import os
import re
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'
INVENTORY = 'c6ef74001a7bcbf35624556862f87e173ff939863d85631e253686815ad450cd'


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
    summary = load(B / 'result-reconciliation.json')
    assert state['source_commit'] == plan['source_commit'] == SOURCE
    assert state['status'] == 'stopped-first-failure'
    assert state['planned_remaining_stages'] == 59
    assert summary['attempted_stages'] == 7 and summary['skipped_stages'] == 52
    assert final['paths_checked'] == 74615 and final['all_paths_attempted']
    assert final['matching'] and not final['changes']
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256'] == INVENTORY
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    # Reconstruct the original small-harness digest from the canonical records.
    # The post-execution publication helper is deliberately not a tested input.
    small = []
    row_count = 0
    scope = Counter()
    scope_hash = hashlib.sha256()
    scope_bytes = 0
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        row_count += 1
        path = Path(row['path'])
        if path.parent == B and path.suffix == '.py' or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256'], str(path)
            small.append(row)
        if row['advice_scope']:
            scope[row['advice_scope']] += 1
            scope_bytes += row['bytes']
            scope_hash.update((json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode())
    assert row_count == 74615
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    assert scope == {'previously_accepted_evidence_data': 7129, 'reviewed_dependency_or_tool_object': 66961}
    assert scope_bytes == 11790867848
    advice = [load(B / 'bootstrap-recovery.json')] + [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    assert len(advice) == 6
    for row in advice:
        assert row['state'] == 'completed' and row['counts'] == dict(scope)
        assert row['scope_identity_sha256'] == scope_hash.hexdigest()
    receipts = []
    warning_count = 0
    for item in state['stages']:
        path = B / item['receipt']
        receipt = load(path)
        receipts.append(receipt)
        assert receipt['source_commit'] == SOURCE
        assert receipt['attempt_id'] == item['attempt_id']
        assert receipt['state'] == item['state'] and receipt['exit'] == item['exit'] == 0
        assert receipt['direct_reaped'] and receipt['all_descendants_gone'] and receipt['kernel_no_children_verified']
        assert receipt['between_child_preservation_passed']
        assert receipt['harness_sha256'] == harness
        assert receipt['canonical_input_inventory']['sha256'] == INVENTORY
        assert receipt['lock']['outer_acquired_ns'] == lease['acquired_ns']
        assert (receipt['lock']['device'], receipt['lock']['inode']) == (lease['device'], lease['inode']) == (33, 3849)
        assert sha(B / receipt['source_snapshot']) == receipt['submitted_source_sha256']
        assert receipt['handshake']['limits'] == {'RLIMIT_AS': [12884901888, 12884901888], 'RLIMIT_CPU': [60, 60], 'RLIMIT_FSIZE': [16777216, 16777216], 'RLIMIT_CORE': [0, 0]}
        raw = (path.parent / 'raw.log').read_text()
        warning_count += len(re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M))
        samples = [json.loads(line) for line in (path.parent / 'samples.jsonl').read_text().splitlines()]
        assert samples[-1] == receipt['latest_decision_sample']
        if receipt['state'] == 'finished':
            assert receipt['waitid_wait4_status_match'] and receipt['terminal_confirmation']['terminal']
            assert receipt['terminal_confirmation']['status'] == 0
            if receipt['stage'] == 'replay':
                assert raw == 'replaying ' + receipt['module'] + '\n'
            if receipt['stage'] == 'resolve':
                assert raw == 'PASS: official checker resolution is exactly [' + receipt['module'] + ']\n'
        for sample in samples:
            memory = sample.get('process_memory', {})
            if memory.get('source_tid') is not None:
                assert memory['tgid'] == receipt['child_pid']
                assert memory['start_ticks'] == receipt['tid_catalog'][str(memory['source_tid'])]['start_ticks']
                assert memory['aggregation'].endswith('never summed')
    assert len(receipts) == len({row['attempt_id'] for row in receipts}) == 7
    assert Counter(row['stage'] for row in receipts) == {'compile': 2, 'resolve': 3, 'replay': 2}
    assert all(a['ended_ns'] < b['lock']['child_entry_ns'] for a, b in zip(receipts, receipts[1:]))
    assert lease['acquired_ns'] < receipts[0]['started_ns'] < receipts[-1]['ended_ns'] < final['started_ns']
    assert all(row['module'] not in {seed['module'] for seed in plan['accepted_seeds']} for row in receipts if row['stage'] == 'compile')
    assert warning_count == 0
    failed = receipts[-1]
    assert [row['state'] for row in receipts] == ['finished'] * 6 + ['failed']
    stop = failed['stop_decision_sample']
    assert stop == load(B / 'product-resolver-stop-sample.json') == failed['latest_decision_sample']
    fresh = stop['child']['fd_transition_reread']
    assert stop['child']['state'] == 'S' and stop['child']['rss'] is not None
    assert fresh['rss'] is None and fresh['vm'] is None and fresh['stat_flags'] & 4
    assert fresh['stat_vsize_bytes'] == fresh['stat_rss_pages'] == 0
    assert fresh['tgid'] == failed['child_pid'] and fresh['start_ticks'] == stop['child']['start_ticks']
    assert not stop['exit_lifecycle']['terminal_confirmed']
    assert stop['process_memory']['rss'] is None and failed['memory_stop_signal_sent']
    assert max(stop['sample_finished_ns'], fresh['tid_read_finished_ns']) <= failed['memory_stop_signal_started_ns'] < failed['process_teardown']['deadline_ns']
    assert failed['stop_decision_errors'] == ["{'operation': 'whole-process supervision', 'error': 'No identity-checked live shared-mm telemetry or bounded exiting-only group'}"]
    fixtures = load(B / 'whole-process-fixture-results.json')['cases']
    assert len(fixtures) == 14 and all(row['passed'] for row in fixtures)
    for case in fixtures:
        receipt = load(B / case['receipt'])
        fixture_lease = load(B / case['folder'] / 'lease.json')
        assert receipt['fixture_only'] and not receipt['compiler_or_checker']
        assert receipt['direct_reaped'] and receipt['all_descendants_gone'] and receipt['kernel_no_children_verified']
        assert fixture_lease['state'] == 'released' and fixture_lease['kernel_echild_at_release']
        for name, digest in receipt['harness_hashes'].items():
            assert sha(B / name) == digest
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    assert len(ledger['objects']) == 4
    for row in ledger['objects']:
        original = Path(row['path'])
        preserved = B / 'preserved-objects' / original.relative_to(original.parents[1])
        assert sha(preserved) == row['sha256']
    statuses = load(B / 'module-status.json')
    assert len(statuses) == 20
    assert [row['module'] for row in statuses if row['accepted']] == ['LightEFTSpanners.AdaptiveFiniteLaw', 'LightEFTSpanners.FiniteHoeffding']
    assert state['accepted_modules'] == state['provisional_modules'] == [row['module'] for row in statuses if row['accepted']]
    for row in plan['modules']:
        source = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=R)
        assert hashlib.sha256(source).hexdigest() == row['sha256']
    manifest_path = B / 'evidence-sha256.json'
    manifest_entries = None
    if manifest_path.exists():
        manifest = load(manifest_path)
        expected_paths = {str(path.relative_to(B)) for path in B.rglob('*') if path.is_file() and '__pycache__' not in path.parts and path != manifest_path}
        assert {row['path'] for row in manifest} == expected_paths
        tracked = set(subprocess.check_output(['git', 'ls-files', '-z', str(B.relative_to(R))], cwd=R).decode().split('\0'))
        for row in manifest:
            path = B / row['path']
            assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256']
            assert str(path.relative_to(R)) in tracked
        manifest_entries = len(manifest)
    with open('/tmp/distance-sparsification-single-compiler.lock', 'r') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        stat = os.fstat(handle.fileno())
        assert (stat.st_dev, stat.st_ino) == (33, 3849)
        fcntl.flock(handle, fcntl.LOCK_UN)
    active = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            if (path / 'comm').read_text().strip() in ('lean', 'leanchecker', 'lake', 'strace', 'ltrace'):
                active.append(path.name)
        except OSError:
            pass
    assert not active, active
    print(json.dumps({'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline publication reconciliation only; no Lean, fixtures, advice or additional full-input content pass', 'source_commit': SOURCE, 'qualified_chains': state['accepted_modules'], 'attempted_stages': 7, 'skipped_stages': 52, 'focused_fixtures_passed': 14, 'inventory_sha256': INVENTORY, 'saved_final_full_content_match': True, 'nonoverlap': True, 'all_children_reaped': True, 'anchored_lean_warning_headers': warning_count, 'failed_resolver_remains_failed': True, 'manifest_entries_verified': manifest_entries, 'active_compilers_checkers_tracers': active, 'lock_free': True}, indent=2))


if __name__ == '__main__':
    main()
