"""Offline reconciliation only; never reruns the batch, a child, or cache advice."""
from pathlib import Path
from collections import Counter
import datetime
import fcntl
import hashlib
import json
import re
import subprocess

B = Path(__file__).resolve().parent
R = B.parents[1]


def load(path):
    return json.loads(path.read_text())


def sha(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def main():
    state = load(B / 'batch-result.json')
    plan = load(B / 'PLAN.json')
    final = load(B / 'final-content-verification.json')
    lease = load(B / 'batch-lock.json')
    assert state['accepted_modules'] == state['provisional_modules'] == []
    assert state['status'] == 'stopped-first-failure' and len(state['stages']) == 2
    assert final['matching'] and final['all_paths_attempted'] and not final['changes']
    assert final['paths_checked'] == 74609
    assert sha(B / 'inputs.jsonl') == final['before_sha256'] == final['after_stream_sha256'] == '50a2e51d63e167bbf4410dbb84b59b3724071be2daff59ea7ea577fd3611ac2d'
    assert lease['state'] == 'released' and lease['kernel_echild_at_release']
    assert lease['acquired_ns'] < final['started_ns'] < final['ended_ns'] < lease['release_verified_ns']
    role_counts = Counter()
    scope_counts = Counter()
    scope_bytes = 0
    scope_digest = hashlib.sha256()
    ordinary = set()
    evidence = set()
    with (B / 'inputs.jsonl').open() as f:
        for line in f:
            row = json.loads(line)
            role_counts[row['role']] += 1
            if row['advice_scope']:
                scope_counts[row['advice_scope']] += 1
                scope_bytes += row['bytes']
                scope_digest.update((json.dumps({'path': row['path'], 'identity': row['identity']}, separators=(',', ':')) + '\n').encode())
                (ordinary if row['advice_scope'] == 'reviewed_dependency_or_tool_object' else evidence).add(row['path'])
    priorroot = R / 'checkpoints/light-eft-finitelaw-finite-recovery-20261017'
    manifest = load(priorroot / 'evidence-sha256.json')
    priorlog = priorroot / 'evidence/replay/hash-advice-before.jsonl'
    expected_prior_hash = next(x['sha256'] for x in manifest if x['path'] == 'evidence/replay/hash-advice-before.jsonl')
    assert sha(priorlog) == expected_prior_hash
    prior = set()
    with priorlog.open() as f:
        for line in f:
            x = json.loads(line)
            if x.get('advised'):
                prior.add(x['path'])
    assert ordinary == prior and len(ordinary) == 66961
    prior_data = {str(R / x['path']) for x in [json.loads(t) for t in (R / plan['recovery_scope_reference']).read_text().splitlines()] if x['status'] == 'advised'}
    assert evidence <= prior_data and len(evidence) == 7129
    idle = [json.loads(x) for x in (B / 'cache-advice.jsonl').read_text().splitlines()]
    for event in idle:
        assert event['state'] == 'completed' and event['counts'] == dict(scope_counts)
        assert event['bytes'] == scope_bytes and event['scope_identity_sha256'] == scope_digest.hexdigest()
    rows = []
    receipts = []
    for stage in state['stages']:
        path = B / stage['receipt']
        r = load(path)
        receipts.append(r)
        assert r['kernel_no_children_verified'] and r['all_descendants_gone'] and r['direct_reaped']
        assert r['between_child_preservation_passed'] and r['final_full_content_verification_required']
        assert r['canonical_input_inventory']['sha256'] == final['before_sha256']
        assert r['lock']['outer_acquired_ns'] == lease['acquired_ns']
        assert (r['lock']['device'], r['lock']['inode']) == (33, 3849)
        assert r['handshake']['limits']['RLIMIT_AS'] == [12884901888, 12884901888]
        assert sha(B / r['source_snapshot']) == r['submitted_source_sha256']
        raw = (path.parent / 'raw.log').read_text()
        assert not re.findall(r'^.*\.lean:\d+:\d+: warning:', raw, re.M)
        ss = [json.loads(x) for x in (path.parent / 'samples.jsonl').read_text().splitlines()]
        assert ss[-1] == r['latest_decision_sample']
        rows.append({'module': r['module'], 'stage': r['stage'], 'attempt_id': r['attempt_id'],
                     'created_utc': r['created_utc'], 'ended_utc': r['ended_utc'], 'child_pid': r['child_pid'],
                     'exit': r['exit'], 'supervised_state': r['state'], 'failure': r.get('failure'),
                     'source_sha256': r['submitted_source_sha256'], 'argv': r['argv'], 'environment': r['environment'],
                     'admission_visible_bytes': r['admission']['headroom'], 'preexec_visible_bytes': r['preexec_admission']['headroom'],
                     'samples': len(ss), 'sampled_rss_peak_bytes': r['sampled_rss_peak_bytes'],
                     'wait4_rss_bytes': r['wait4_maxrss_kib'] * 1024,
                     'minimum_sampled_visible_headroom': min(x['accounting']['headroom'] for x in ss),
                     'source_snapshot': r['source_snapshot'], 'receipt': stage['receipt']})
    compiler, resolver = receipts
    assert compiler['state'] == 'finished' and compiler['exit'] == 0
    assert compiler['ended_ns'] < resolver['lock']['child_entry_ns']
    assert resolver['state'] == 'failed' and resolver['exit'] == 0
    stop = resolver['stop_decision_sample']
    assert stop == resolver['latest_decision_sample']
    assert stop['child']['state'] == 'Z' and stop['child']['stat_threads'] == stop['child']['status_threads'] == 2
    assert stop['child']['rss'] is None and stop['child']['vm'] is None
    assert stop['child']['stat_flags'] & 4 and stop['child']['stat_vsize_bytes'] == stop['child']['stat_rss_pages'] == 0
    probes = stop['exit_lifecycle']['probes']
    assert len(probes) == 3 and all(not p['terminal'] for p in probes)
    assert not stop['exit_lifecycle']['allow_missing_memory'] and not stop['exit_lifecycle']['exact_transition_candidate']
    assert resolver['memory_stop_signal_sent']
    assert max([stop['sample_finished_ns']] + [x['finished_ns'] for x in probes]) <= resolver['memory_stop_signal_started_ns']
    (B / 'resolver-stop-sample.json').write_text(json.dumps(stop, indent=2) + '\n')
    ledger = load_ledger = json.loads((B / 'output-records.jsonl').read_text().splitlines()[-1])
    assert len(ledger['objects']) == 2
    for obj in ledger['objects']:
        rel = Path(obj['path']).relative_to(Path(obj['path']).parents[1])
        # Both objects are in this one namespace; preserve the exact relative path.
        assert sha(B / 'preserved-objects' / rel) == obj['sha256'] == sha(Path(obj['path']))
    fixtures = load(B / 'shared-fixture-results.json')['cases']
    assert len(fixtures) == 3 and all(x['passed'] for x in fixtures)
    fixture_receipts = []
    for case in fixtures:
        l = load(B / case['folder'] / 'lease.json')
        assert l['state'] == 'released' and l['kernel_echild_at_release']
        for path in case['receipts']:
            r = load(B / path)
            assert r['fixture_only'] and not r['compiler_or_checker'] and r['kernel_no_children_verified']
            for name, value in r['harness_hashes'].items():
                assert sha(B / name) == value
            fixture_receipts.append(r)
    assert len(fixture_receipts) == 4 and sum(x.get('child_pid') is not None for x in fixture_receipts) == 3
    statuses = []
    for index, module in enumerate(plan['modules']):
        statuses.append({'module': module['module'], 'accepted': False,
                         'compile': 'passed' if index == 0 else 'skipped_after_first_failure',
                         'resolve': 'failed_closed_on_two_thread_terminal_transition' if index == 0 else 'skipped_after_first_failure',
                         'replay': 'skipped_after_first_failure'})
    (B / 'module-status.json').write_text(json.dumps(statuses, indent=2) + '\n')
    result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Offline reconciliation, no Lean/advice retry or third full input pass',
              'source_commit': plan['source_commit'], 'result': 'FIRST_COMPILE_PASSED_RESOLVER_TELEMETRY_FAILED_NO_NEW_MODULE_ACCEPTED',
              'planned_modules': 20, 'accepted_modules': [], 'attempted_children': 2, 'skipped_stages': 58,
              'stages': rows, 'canonical_inventory': state['canonical_inputs'], 'final_full_content_verified': True,
              'full_content_pass_count': 2, 'one_lock_held_across_batch': True, 'nonoverlap': True,
              'all_children_reaped': True, 'scope_not_expanded': True, 'scoped_advice_counts': dict(scope_counts),
              'scoped_advice_bytes_per_pass': scope_bytes, 'idle_passes': len(idle),
              'output_records': ledger, 'focused_fixture_cases_passed': 3, 'fixture_receipts': 4,
              'new_recursive_axiom_audits': 0, 'new_ci_runs': 0,
              'remaining_blocker': 'Identity-matching PF_EXITING zero-memory zombie leader has two sampled threads; all waitid probes unconfirmed, outside approved single-thread exception'}
    (B / 'result-reconciliation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('stages', 'output_records')}, indent=2))


if __name__ == '__main__':
    main()
