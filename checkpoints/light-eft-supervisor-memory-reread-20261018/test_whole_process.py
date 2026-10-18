"""Harmless native-pthread/Python fixtures for whole-process supervision."""
from pathlib import Path
from unittest.mock import patch
from contextlib import ExitStack
import datetime
import hashlib
import json
import os
import sys
import uuid
import child_runner as child
import decision_telemetry as telemetry
from pilot_accounting import AccountingSampleError
from shared_preservation import Lease, FrozenInputs

B = Path(__file__).resolve().parent
CASES = ['multithread_leader_exit', 'live_sibling_telemetry', 'all_thread_teardown',
         'timeout_no_reset', 'live_sibling_missing', 'live_leader_missing',
         'accounting_during_grace', 'headroom_during_grace', 'sibling_rss_breach',
         'nonzero_exit', 'signal_exit', 'waitid_ownership_failure',
         'sibling_tgid_mismatch', 'sibling_start_mismatch']


def source_for(case):
    if case == 'nonzero_exit':
        return 'import time,os\ntime.sleep(.25)\nos._exit(7)\n'
    if case == 'signal_exit':
        return 'import time,os,signal\ntime.sleep(.25)\nos.kill(os.getpid(),signal.SIGTERM)\n'
    seconds = [1, 1, 1] if case == 'multithread_leader_exit' else [1, 1]
    if case == 'timeout_no_reset':
        seconds = [1, 3]
    elif case not in ('multithread_leader_exit', 'live_sibling_telemetry', 'all_thread_teardown'):
        seconds = [3, 3]
    return '''import ctypes,time,os
libc=ctypes.CDLL(None)
libc.pthread_create.argtypes=[ctypes.POINTER(ctypes.c_ulong),ctypes.c_void_p,ctypes.c_void_p,ctypes.c_void_p]
libc.pthread_create.restype=ctypes.c_int
workers=[]
for seconds in SECONDS:
    handle=ctypes.c_ulong()
    result=libc.pthread_create(ctypes.byref(handle),None,ctypes.cast(libc.sleep,ctypes.c_void_p),ctypes.c_void_p(seconds))
    if result:os._exit(90)
    workers.append(handle)
time.sleep(.25)
libc.pthread_exit.argtypes=[ctypes.c_void_p]
libc.pthread_exit.restype=None
libc.pthread_exit(None)
os._exit(91)
'''.replace('SECONDS', repr(seconds))


class Context:
    preservation_failed = False
    def __init__(self, lock, lease, frozen, source, case):
        self.lock = lock
        self.acquired_ns = lease.record['acquired_ns']
        self.frozen = frozen
        self.source = source
        self.case = case
        self.record = None
    def visible_gate(self, plan):
        return 3221225472
    def before_child(self, plan, record, save):
        self.record = record
        record.update(fixture_only=True, compiler_or_checker=False, case=self.case,
                      submitted_source_sha256=hashlib.sha256(self.source.read_bytes()).hexdigest(),
                      harness_hashes={name: hashlib.sha256((B / name).read_bytes()).hexdigest()
                                      for name in ['child_runner.py', 'decision_telemetry.py', 'exit_transition.py', 'pilot_child.py', 'shared_preservation.py', 'test_whole_process.py']})
        self.frozen.identities()
        save()
    def prepare_child(self, plan, record, save, accounting):
        now = accounting.sample()
        record['admission'] = now
        save()
        return now
    def after_child(self, plan, record, save):
        self.frozen.identities()
        record['between_child_preservation_passed'] = True
        save()
    def output_summary(self):
        return {'fixture_only': True}
    def complete_log(self, path, record, save):
        with path.open('rb') as f:
            os.fsync(f.fileno())


class Accounting:
    def __init__(self, ctx):
        self.ctx = ctx
    def sample(self):
        grace = bool(self.ctx.record and self.ctx.record.get('process_teardown'))
        if grace and self.ctx.case == 'accounting_during_grace':
            raise AccountingSampleError('Synthetic accounting failure during grace',
                                        {'partial_raw': 'fixture preserved', 'collection_errors': [{'operation': 'fixture accounting', 'error': 'injected failure'}]})
        return {'namespace': 'synthetic-fixture', 'membership': '0::/\n', 'identities': [], 'collection_errors': [],
                'headroom': 1073741823 if grace and self.ctx.case == 'headroom_during_grace' else 8*1024**3,
                'system_available': 8*1024**3,
                'nodes': [{'path': '/synthetic/group', 'limit': str(16*1024**3), 'current': 1,
                           'memory_stat': {'anon': 100, 'file': 200, 'kernel': 50}, 'memory_events': {'oom': 0},
                           'oom': {'oom': 0}, 'pids_current': 1, 'pids_max': 'max', 'pids_events': {'max': 0}}]}


def run_case(case):
    folder = B / 'whole-process-fixtures' / (case + '-' + uuid.uuid4().hex)
    folder.mkdir(parents=True)
    source = folder / 'submitted.py'
    source.write_text(source_for(case))
    lease = Lease(folder / 'lease.json')
    with lease as lock:
        frozen = FrozenInputs({source: {'role': 'fixture_source'}}, folder)
        frozen.freeze()
        ctx = Context(lock, lease, frozen, source, case)
        original = telemetry.capture_child
        def capture(tid, *args, **kwargs):
            row = original(tid, *args, **kwargs)
            record = ctx.record or {}
            known = str(tid) in record.get('tid_catalog', {})
            sibling = record.get('child_pid') is not None and tid != record['child_pid']
            if known and sibling:
                if case == 'sibling_tgid_mismatch':
                    row['tgid'] += 1
                    row['synthetic_fixture_override'] = 'tgid mismatch'
                elif case == 'sibling_start_mismatch':
                    row['start_ticks'] += 1
                    row['synthetic_fixture_override'] = 'start-time mismatch'
            missing = (case == 'live_sibling_missing' and known and sibling) or (case == 'live_leader_missing' and known and not sibling)
            if missing and row.get('stat_vsize_bytes', 0) > 0:
                row.update(rss=None, vm=None, synthetic_fixture_override='live memory omitted')
                row['collection_errors'] += [{'operation': 'VmRSS', 'error': 'Missing required live value'}, {'operation': 'VmSize', 'error': 'Missing required live value'}]
            if case == 'all_thread_teardown' and sibling and record.get('process_teardown'):
                row.update(rss=None, vm=None, state='Z', stat_flags=row.get('stat_flags', 0)|4,
                           stat_vsize_bytes=0, stat_rss_pages=0, synthetic_fixture_override='positive exiting/no-mm task')
                row['collection_errors'] = [{'operation': 'VmRSS', 'error': 'Missing required live value'}, {'operation': 'VmSize', 'error': 'Missing required live value'}]
            if case == 'sibling_rss_breach' and sibling and record.get('process_teardown') and row.get('rss') is not None:
                row['rss'] = child.RSS_STOP
                row['synthetic_fixture_override'] = 'RSS ceiling breach'
            return row
        plan = {'stage': 'fixture', 'module': 'fixture', 'argv': [sys.executable, '-I', str(source)],
                'env': {'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}}
        success = case in ('multithread_leader_exit', 'live_sibling_telemetry', 'all_thread_teardown')
        with ExitStack() as stack:
            stack.enter_context(patch.object(telemetry, 'capture_child', side_effect=capture))
            if case == 'waitid_ownership_failure':
                stack.enter_context(patch.object(os, 'waitid', side_effect=ChildProcessError('synthetic unowned PID')))
            try:
                r = child.run_child(plan, folder, folder/'attempt', ctx, accounting=Accounting(ctx))
                assert success, 'Expected fail-closed fixture'
            except RuntimeError:
                assert not success
                r = json.loads((folder/'attempt/receipt.json').read_text())
                assert r['state'] == 'failed'
        samples = [json.loads(x) for x in (folder/'attempt/samples.jsonl').read_text().splitlines()]
        if success:
            assert r['exit'] == 0 and r['waitid_wait4_status_match'] and r['terminal_confirmation']['terminal']
            assert any(s['child'].get('state') == 'Z' and not s['exit_lifecycle']['terminal_confirmed'] for s in samples)
            assert len(r['tid_catalog']) >= (4 if case == 'multithread_leader_exit' else 3)
        if case in ('multithread_leader_exit', 'live_sibling_telemetry'):
            sibling_samples = [s for s in samples if s['exit_lifecycle'].get('using_live_sibling_memory')]
            assert sibling_samples
            for s in sibling_samples:
                m = s['process_memory']
                assert m['source_tid'] != r['child_pid'] and m['tgid'] == r['child_pid']
                assert s['exit_lifecycle']['live_lock_verification']['tid'] == m['source_tid']
                assert m['aggregation'].endswith('never summed')
        if case == 'all_thread_teardown':
            assert any(s['exit_lifecycle'].get('teardown_pending') and s['process_memory']['rss'] is None for s in samples)
        if case == 'timeout_no_reset':
            assert 'grace expired' in r['failure']
            deadlines = [s['exit_lifecycle']['teardown_deadline_ns'] for s in samples if 'teardown_deadline_ns' in s['exit_lifecycle']]
            assert len(deadlines) >= 3 and len(set(deadlines)) == 1
            g = r['process_teardown']
            assert g['deadline_ns'] - g['started_ns'] <= 1_000_000_000
        if case in ('nonzero_exit', 'signal_exit'):
            assert r['waitid_wait4_status_match'] and r['exit'] == (7 if case == 'nonzero_exit' else -15)
        if 'stop_decision_sample' in r:
            assert r['stop_decision_sample'] == r['latest_decision_sample'] == samples[-1]
            assert r['memory_stop_signal_sent'] and r['exit'] == -9
        assert r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
        final = frozen.final_verify()
        assert final['matching']
    return {'case': case, 'folder': str(folder.relative_to(B)), 'passed': True,
            'receipt': str((folder/'attempt/receipt.json').relative_to(B)), 'child_exit': r['exit'],
            'synthetic_accounting': True, 'telemetry_overrides': case not in ('multithread_leader_exit','live_sibling_telemetry','nonzero_exit','signal_exit')}


if __name__ == '__main__':
    with (B/'whole-process-fixtures-claimed.json').open('x') as f:
        json.dump({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'one_focused_suite': True}, f)
    results = []
    for case in CASES:
        results.append(run_case(case))
        print(case + ' PASS', flush=True)
    (B/'whole-process-fixture-results.json').write_text(json.dumps({'cases': results,
        'scope': 'Harmless native-pthread/Python children; no Lean or C compilation; real waitid/wait4/lock/cleanup, explicitly labeled synthetic fault injections'},indent=2)+'\n')
