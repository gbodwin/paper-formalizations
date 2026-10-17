"""Offline evidence checks; never executes Lean, extraction, advice or retries."""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import os
import stat
import subprocess
import sys

B = Path(__file__).resolve().parent
R = B.parents[1]
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'
TOP = {'inputs.jsonl', 'output-records.jsonl', 'cache-advice.jsonl', 'result-reconciliation.json', 'module-status.json', 'source-toolchain-object-hashes.json', 'publication-checks.json'}
REPLAY = {'hash-advice-before.jsonl', 'hash-advice-after.jsonl', 'inputs-before.json', 'inputs-after.json', 'receipt.json', 'samples.jsonl', 'raw.log'}
CHUNKS = {'evidence-replay-hash-advice-before-jsonl', 'evidence-replay-hash-advice-after-jsonl', 'evidence-replay-inputs-before-json'}
NEW = {'approved_archive_extension', 'approved_finalized_extension'}


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def signature(info):
    return [info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns]


def pinned(root, binding):
    path = root / binding['path']
    assert sha(path) == binding['sha256'] and path.stat().st_size == binding['bytes']
    assert subprocess.check_output(['git', 'show', binding['accepted_commit'] + ':' + binding['path']], cwd=R) == path.read_bytes()
    return load(path)


def main():
    state = load(B / 'batch-result.json')
    plan = load(B / 'PLAN.json')
    final = load(B / 'final-content-verification.json')
    lease = load(B / 'batch-lock.json')
    graph = load(R / plan['source_graph_path'])
    assert state['source_commit'] == plan['source_commit'] == SOURCE
    assert state['status'] == 'stopped-first-failure' and not state['accepted_modules'] and not state['provisional_modules']
    assert plan['module_count'] == len(plan['modules']) == 77 and plan['stage_count'] == 231
    assert plan['stages_per_module'] == ['compile', 'resolve', 'replay']
    assert [{key: row[key] for key in graph[0]} for row in plan['modules']] == graph[94:171]
    assert {row['module'] for row in plan['accepted_seeds']} == {row['module'] for row in graph[:94]}
    assert plan['first_compile_visible_gate'] == 5368709120
    assert len(state['stages']) == 1
    attempt = state['stages'][0]
    receipt_path = B / attempt['receipt']
    receipt = load(receipt_path)
    assert receipt['module'] == graph[94]['module'] == 'LightEFTSpanners.BernoulliFlagEncoding'
    assert receipt['stage'] == 'compile' and receipt['state'] == 'failed'
    assert receipt['failure'] == "MemoryGuardError('Visible headroom below required floor')"
    assert 'child_pid' not in receipt and 'exit' not in receipt and 'handshake' not in receipt and 'preexec_admission' not in receipt
    assert not (receipt_path.parent / 'raw.log').exists() and not (receipt_path.parent / 'samples.jsonl').exists()
    assert receipt['kernel_no_children_verified'] and receipt['between_child_preservation_passed']
    assert receipt['admission']['headroom'] == 4955549696 < receipt['memory_policy']['admission_visible_bytes'] == 5368709120
    assert receipt['admission']['system_available'] == 17715765248
    assert receipt['memory_policy']['as_bytes'] == 12884901888
    assert receipt['memory_policy']['stop_visible_host_bytes'] == 1073741824
    assert receipt['memory_policy']['rss_observed_stop_bytes'] == 6442450944
    assert receipt['memory_policy']['per_cgroup_anon_growth_stop_bytes'] == 3221225472
    assert final['matching'] and final['all_paths_attempted'] and not final['changes']
    assert final['paths_checked'] == state['canonical_inputs']['rows'] == 79881
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256']
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < receipt['started_ns'] < receipt['ended_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns'] < lease['released_ns']
    assert receipt['lock']['outer_acquired_ns'] == lease['acquired_ns']
    assert (receipt['lock']['device'], receipt['lock']['inode']) == (33, 3849)
    assert sha(B / receipt['source_snapshot']) == receipt['submitted_source_sha256']
    small = []
    counts = Counter()
    sizes = Counter()
    scope_digest = hashlib.sha256()
    new_rows = {}
    row_count = 0
    for line in (B / 'inputs.jsonl').open():
        row = json.loads(line)
        row_count += 1
        path = Path(row['path'])
        if path.parent == B and path.suffix == '.py' or path in [B / 'PLAN.json', R / 'scripts/LightEFTResolveCheckerTarget.lean', R / 'scripts/LightEFTProcessLifecycle.py']:
            assert sha(path) == row['sha256']
            small.append(row)
        if row['advice_scope']:
            counts[row['advice_scope']] += 1
            sizes[row['advice_scope']] += row['bytes']
            scope_digest.update((json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode())
        if row['advice_scope'] in NEW:
            new_rows[row['path']] = row
    assert row_count == 79881
    harness = hashlib.sha256(b''.join((json.dumps(row, separators=(',', ':')) + '\n').encode() for row in sorted(small, key=lambda row: row['path']))).hexdigest()
    assert harness == receipt['harness_sha256']
    assert counts == {'reviewed_dependency_or_tool_object': 66961, 'previously_accepted_evidence_data': 7129, 'reviewed_finalized_batch_data': 623,
                      'approved_archive_extension': 3809, 'approved_finalized_extension': 708}
    assert sizes['approved_archive_extension'] == 818684031 and sizes['approved_finalized_extension'] == 385582329
    expected = {}
    archives = pinned(R, plan['new_archive_authorities'][0])['archives']
    assert len(archives) == 3808
    for row in archives:
        path = Path(row['local_archive'])
        assert path.parent == Path('/workspace/cache/mathlib') and path.name == row['cache_key'] + '.ltar'
        expected[str(path)] = row
    tool = pinned(R, plan['new_archive_authorities'][1])['official_archive']
    assert tool['path'] == '/workspace/toolchains/lean.tar.zst'
    expected[tool['path']] = tool
    assert len(expected) == 3809 and sum(row['bytes'] for row in expected.values()) == 818684031
    checkpoint_counts = {}
    for binding in plan['new_data_manifests']:
        manifest = R / binding['path']
        added = 0
        for row in pinned(R, binding):
            parts = Path(row['path']).parts
            allowed = row['path'] in TOP
            if manifest.parent.name == 'light-eft-finitelaw-finite-recovery-20261017':
                allowed |= len(parts) == 3 and parts[:2] == ('evidence', 'replay') and parts[-1] in REPLAY
                allowed |= len(parts) == 3 and parts[0] == 'chunks' and parts[1] in CHUNKS and parts[-1].startswith('part-') and parts[-1].endswith('.txt')
            else:
                allowed |= len(parts) == 3 and parts[0] == 'attempts' and parts[-1] in {'receipt.json', 'samples.jsonl', 'raw.log'}
            if allowed:
                path = str(manifest.parent / row['path'])
                assert path not in expected
                expected[path] = row
                added += 1
        assert added == binding['selected_file_count']
        checkpoint_counts[manifest.parent.name] = added
    assert list(checkpoint_counts.values()) == [12, 27, 14, 211, 444]
    assert len(expected) == len(new_rows) == 4517
    assert sum(row['bytes'] for row in expected.values()) == 1204266360
    assert set(new_rows) == set(expected)
    for name, row in new_rows.items():
        assert row['sha256'] == expected[name]['sha256'] and row['bytes'] == expected[name]['bytes']
        info = os.lstat(name)
        assert stat.S_ISREG(info.st_mode) and not info.st_mode & 0o111 and signature(info) == row['identity']
    verified = [json.loads(line) for line in (B / 'one-time-extension-verified.jsonl').read_text().splitlines()]
    assert {row['path']: row for row in verified} == new_rows
    advice = [json.loads(line) for line in (B / 'cache-advice.jsonl').read_text().splitlines()]
    assert len(advice) == 1
    finite = advice[0]
    assert finite == load(B / 'one-time-cache-advice.json')
    assert finite['state'] == 'completed' and finite['mode'] == 'one-time-extension'
    assert finite['counts'] == dict(counts) and finite['bytes_by_scope'] == dict(sizes)
    assert finite['bytes'] == 13229175341 and finite['scope_identity_sha256'] == scope_digest.hexdigest()
    assert finite['before']['headroom'] == 14532608 and finite['after']['headroom'] == 4955549696
    assert finite['nominal_bytes_not_credited_as_reclaimed']
    assert load(B / 'extension-pass-claimed.json')['one_pass_only']
    assert load(B / 'expanded-scope-initial.json')['counts'] == {'reviewed_finalized_batch_data': 623}
    assert finite['ended_ns'] <= receipt['ended_ns']
    for name, digest in load(B / 'preparation-checks.json')['supervisor_byte_identity'].items():
        assert sha(B / name) == digest
        assert (B / name).read_bytes() == (R / 'checkpoints/light-eft-resume298-retained-root-20261017' / name).read_bytes()
    ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    original = load(B / 'retained-root-binding.json')
    assert len(ledger['objects']) == len(original['objects']) == 94
    assert {row['path']: row for row in ledger['objects']} == {row['path']: row for row in original['objects']}
    for row in ledger['objects']:
        path = Path(row['path'])
        copy = B / 'preserved-objects' / path.relative_to(path.parents[1])
        assert sha(path) == sha(copy) == row['sha256']
    assert len(original['resolutions']) == 23
    for row in original['resolutions']:
        assert sha(Path(row['path'])) == row['sha256']
    assert {str(path) for path in (R / plan['retained_work_root']).rglob('*') if path.is_file()} == set(original['files'])
    assert not (R / plan['retained_work_root'] / 'objects/LightEFTSpanners/BernoulliFlagEncoding.olean').exists()
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
    result = {'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline reconciliation; no archive extraction, extra full input-content pass, advice, fixture or Lean invocation',
        'source_commit': SOURCE, 'base_evidence': plan['base_evidence'], 'result': 'ONE_FINITE_SCOPE_PASS_COMPLETED_FIRST_5GIB_COMPILE_ADMISSION_REFUSED_NO_LEAN_CHILD',
        'planned_modules': 77, 'planned_stages': 231, 'attempted_stage_receipts': 1, 'failed_admission_stages': 1, 'executed_tool_children': 0, 'skipped_later_stages': 230,
        'completed_new_module_chains': 0, 'accepted_chains_preserved': 94, 'accepted_stage_reruns': 0,
        'scope_A_files': 3809, 'scope_A_bytes': 818684031, 'scope_B_files': 708, 'scope_B_bytes': 385582329, 'scope_B_checkpoint_counts': checkpoint_counts,
        'new_combined_scope_files': 4517, 'new_combined_scope_bytes': 1204266360, 'new_scope_ceiling_not_exceeded': True, 'new_hash_then_advice_passes': 1,
        'combined_legacy_and_new_scope_counts': dict(counts), 'combined_legacy_and_new_nominal_bytes': finite['bytes'],
        'finite_pass_before_visible_bytes': 14532608, 'finite_pass_after_visible_bytes': 4955549696, 'admission_actual_visible_bytes': 4955549696,
        'first_compile_required_visible_bytes': 5368709120, 'shortfall_bytes': 413159424, 'host_MemAvailable_at_refusal_bytes': 17715765248,
        'preexec_gate_not_reached': True, 'no_followup_advice_or_retry': True, 'archive_extractions': 0, 'stronger_provenance_claim': False,
        'canonical_inventory': state['canonical_inputs'], 'saved_final_full_preservation_match': True, 'full_input_content_pass_count': 2,
        'one_continuous_universal_lock': True, 'kernel_ECHILD_before_release': True, 'original_root_objects_unchanged': 94, 'original_resolutions_unchanged': 23,
        'reviewed_supervisor_byte_identical': True, 'new_fixture_runs': 0, 'new_ci_runs': 0, 'new_exhaustive_audits': 0,
        'manifest_entries_verified': manifest_entries, 'active_compilers_checkers_tracers': active, 'common_lock_free': True,
        'failed_receipt': attempt['receipt'], 'attempt_id': receipt['attempt_id'], 'created_utc': receipt['created_utc'], 'ended_utc': receipt['ended_utc'],
        'planned_argv_not_executed': receipt['argv'], 'planned_environment_not_executed': receipt['environment']}
    if '--write' in sys.argv:
        assert not manifest.exists()
        (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if not key.startswith('planned_argv') and not key.startswith('planned_environment')}, indent=2))


if __name__ == '__main__':
    main()
