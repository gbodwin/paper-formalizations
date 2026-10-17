"""Focused harmless tests of the actual shared lease, bindings and child runner."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import sys
import time
import uuid
import child_runner as child
from shared_preservation import Lease, FrozenInputs, inspect

B = Path(__file__).resolve().parent


def held():
    with child.LOCK.open('r+') as other:
        try:
            fcntl.flock(other, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        return False


class FakeAccounting:
    def __init__(self, fail=False):
        self.calls = 0
        self.fail = fail
    def sample(self):
        self.calls += 1
        return {'namespace': 'synthetic-fixture', 'membership': '0::/\n', 'identities': [], 'collection_errors': [],
                'headroom': 8 * 1024**3, 'system_available': 0 if self.fail and self.calls >= 6 else 8 * 1024**3,
                'nodes': [{'path': '/synthetic/group', 'limit': str(16 * 1024**3), 'current': 1,
                           'memory_stat': {'anon': 100, 'file': 200, 'kernel': 50}, 'memory_events': {'oom': 0},
                           'oom': {'oom': 0}, 'pids_current': 1, 'pids_max': 'max', 'pids_events': {'max': 0}}]}


class TestContext:
    preservation_failed = False
    def __init__(self, lock, lease, frozen, source):
        self.lock = lock
        self.acquired_ns = lease.record['acquired_ns']
        self.frozen = frozen
        self.source = source
    def visible_gate(self, plan):
        return 3221225472
    def before_child(self, plan, record, save):
        record.update(fixture_only=True, compiler_or_checker=False, module='fixture',
                      canonical_input_sha256=self.frozen.digest,
                      submitted_source_sha256=hashlib.sha256(self.source.read_bytes()).hexdigest(),
                      harness_hashes={n: hashlib.sha256((B / n).read_bytes()).hexdigest()
                                      for n in ['child_runner.py', 'shared_preservation.py', 'pilot_child.py', 'exit_transition.py', 'decision_telemetry.py', 'test_shared_batch.py']})
        save()
        self.frozen.identities()
        assert held()
    def prepare_child(self, plan, record, save, accounting):
        now = accounting.sample()
        record['admission'] = now
        save()
        return now
    def after_child(self, plan, record, save):
        self.frozen.identities()
        assert held()
        record['between_child_preservation_passed'] = True
        save()
    def complete_log(self, path, record, save):
        with path.open('rb') as f:
            os.fsync(f.fileno())
    def output_summary(self):
        return {'fixture_only': True}


def case(label, mode):
    folder = B / 'shared-fixtures' / (label + '-' + uuid.uuid4().hex)
    folder.mkdir(parents=True)
    source = folder / 'submitted.py'
    source.write_text('import time\ntime.sleep(' + ('60' if mode == 'failure' else '.2') + ')\n')
    bound = folder / 'bound.txt'
    bound.write_text('old data\n')
    (folder / 'bound-before.txt').write_bytes(bound.read_bytes())
    lease = Lease(folder / 'lease.json')
    receipts = []
    with lease as lock:
        frozen = FrozenInputs({source: {'role': 'fixture_source'}, bound: {'role': 'fixture_data'}}, folder)
        frozen.freeze()
        assert held()
        context = TestContext(lock, lease, frozen, source)
        if mode == 'changed':
            bound.write_text('new data\n')
        for index in range(2 if mode == 'success' else 1):
            path = folder / ('child-%d' % index)
            plan = {'stage': 'fixture', 'module': 'fixture', 'argv': [sys.executable, '-I', str(source)],
                    'env': {'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}}
            try:
                r = child.run_child(plan, folder, path, context, accounting=FakeAccounting(mode == 'failure'))
                assert mode == 'success'
            except RuntimeError:
                assert mode in ('changed', 'failure')
                r = json.loads((path / 'receipt.json').read_text())
                assert r['state'] == 'failed'
                if mode == 'changed':
                    assert r.get('child_pid') is None and 'identity changed' in r['failure']
                else:
                    assert r['exit'] == -9 and r['memory_stop_signal_sent'] and r['direct_reaped']
            assert r['kernel_no_children_verified'] and held()
            receipts.append(str((path / 'receipt.json').relative_to(B)))
        final = frozen.final_verify()
        assert held() and final['matching'] == (mode != 'changed')
        assert final['all_paths_attempted']
    assert not held()
    return {'case': label, 'folder': str(folder.relative_to(B)), 'receipts': receipts,
            'passed': True, 'lease_held_through_final_verification': True, 'released_only_after_echild': True}


if __name__ == '__main__':
    with (B / 'shared-fixtures-claimed.json').open('x') as f:
        json.dump({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'one_focused_suite': True}, f)
    results = []
    for label, mode in [('shared-lock-two-children', 'success'), ('changed-input-no-spawn', 'changed'), ('failure-cleanup-lock-held', 'failure')]:
        results.append(case(label, mode))
        print(label + ' PASS', flush=True)
    (B / 'shared-fixture-results.json').write_text(json.dumps({'scope': 'Harmless Python only, synthetic accounting labeled; actual shared lease/child runner/waitid/wait4/cleanup', 'cases': results}, indent=2) + '\n')
