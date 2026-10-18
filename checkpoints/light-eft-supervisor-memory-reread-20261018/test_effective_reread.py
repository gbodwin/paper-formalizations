"""Deterministic synthetic transition inputs, real owned child/waitid/wait4.

No compiler/checker. Every override is recorded beside original proc reads.
"""
from pathlib import Path
from unittest.mock import patch
import copy
import datetime
import fcntl
import hashlib
import json
import os
import resource
import select
import signal
import subprocess
import sys
import time
import uuid
import child_runner as runner
import decision_telemetry as telemetry
import exit_transition as exits
from shared_preservation import Lease
from test_whole_process import Accounting

B = Path(__file__).resolve().parent
CASES = ['leader_reread', 'sibling_reread', 'sibling_disappeared',
         'fresh_live_missing', 'fresh_identity_mismatch', 'fresh_nonmemory_error',
         'fresh_live_lock_missing', 'earlier_rss_breach', 'fresh_rss_breach',
         'grace_expired', 'sibling_live_missing', 'sibling_identity_mismatch']
SOURCE = '''import threading,json,sys
event=threading.Event()
workers=[threading.Thread(target=event.wait) for _ in range(2)]
for worker in workers:worker.start()
print(json.dumps([threading.get_native_id()]+[worker.native_id for worker in workers]),flush=True)
sys.stdin.readline()
event.set()
for worker in workers:worker.join()
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def no_memory(row):
    row = copy.deepcopy(row)
    row.update(state='R', stat_flags=row['stat_flags'] | 4, rss=None, vm=None,
               stat_vsize_bytes=0, stat_rss_pages=0,
               synthetic_fixture_override='identity-preserving exiting/no-mm')
    row['collection_errors'] = [{'operation': key, 'error': 'Missing required live value'} for key in ['VmRSS', 'VmSize']]
    return row


def run_case(case):
    folder = B / 'effective-reread-fixtures' / (case + '-' + uuid.uuid4().hex)
    folder.mkdir(parents=True)
    source = folder / 'submitted.py'
    source.write_text(SOURCE)
    record = {'attempt_id': uuid.uuid4().hex, 'fixture_only': True, 'compiler_or_checker': False,
              'case': case, 'synthetic_telemetry_and_fd_inputs': True,
              'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'started_ns': time.monotonic_ns(), 'submitted_source_sha256': sha(source),
              'harness_hashes': {name: sha(B / name) for name in ['exit_transition.py', 'decision_telemetry.py', 'child_runner.py', 'test_effective_reread.py']},
              'deadline_seconds': 90, 'runtime_wall_started_ns': time.monotonic_ns()}
    child = None
    samples = []
    captures = []
    with Lease(folder / 'lease.json') as lock:
        stat = os.fstat(lock.fileno())
        record['lock'] = {'fd': lock.fileno(), 'device': stat.st_dev, 'inode': stat.st_ino}
        def limits():
            for name, value in runner.LIMITS.items():
                resource.setrlimit(getattr(resource, name), (value, value))
        try:
            child = subprocess.Popen([sys.executable, '-I', str(source)], stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, pass_fds=(lock.fileno(),),
                start_new_session=True, preexec_fn=limits)
            record['child_pid'] = child.pid
            assert select.select([child.stdout], [], [], 3)[0], 'Fixture readiness timeout'
            tids = json.loads(child.stdout.readline())
            assert tids[0] == child.pid and len(tids) == 3
            original_rows = {tid: telemetry.capture_child(tid) for tid in tids}
            record['original_proc_rows'] = original_rows
            record['child_identity'] = original_rows[child.pid]
            record['tid_catalog'] = {str(tid): {'tid': tid, 'tgid': child.pid,
                'start_ticks': original_rows[tid]['start_ticks']} for tid in tids}
            sibling_case = case.startswith('sibling_')
            target = tids[1] if sibling_case else child.pid
            initial = copy.deepcopy(original_rows)
            if sibling_case:
                initial[child.pid] = no_memory(initial[child.pid])
            initial[target]['rss'] = 6442450944 if case == 'earlier_rss_breach' else 100_000_000
            initial[target]['synthetic_fixture_override'] = 'deterministic selected live memory source'
            vanished = {tid for tid in tids if tid not in (child.pid, target)}
            for tid in vanished:
                initial[tid] = {'pid': tid, 'rss': None, 'vm': None, 'collection_errors': [{'operation': 'child stat', 'error': 'synthetic ENOENT'}]}
            fresh = no_memory(original_rows[target])
            if case in ('fresh_live_missing', 'sibling_live_missing'):
                fresh = copy.deepcopy(original_rows[target])
                fresh.update(rss=None, vm=None)
                fresh['collection_errors'] = [{'operation': key, 'error': 'Missing required live value'} for key in ['VmRSS', 'VmSize']]
            if case in ('fresh_identity_mismatch', 'sibling_identity_mismatch'):
                fresh['start_ticks'] += 1
            if case == 'fresh_nonmemory_error':
                fresh['collection_errors'].append({'operation': 'parse child identity', 'error': 'synthetic parse fault'})
            if case in ('fresh_live_lock_missing', 'fresh_rss_breach'):
                fresh = copy.deepcopy(original_rows[target])
                if case == 'fresh_rss_breach':
                    fresh['rss'] = 6442450944
            if case == 'sibling_disappeared':
                fresh = {'pid': target, 'rss': None, 'vm': None, 'collection_errors': [{'operation': 'child stat', 'error': 'synthetic ENOENT'}]}
                vanished.add(target)
            fresh['synthetic_fixture_override'] = 'deterministic FD-transition reread: ' + case
            calls = {}
            def capture(tid):
                calls[tid] = calls.get(tid, 0) + 1
                row = copy.deepcopy(fresh if tid == target and (not sibling_case or calls[tid] > 1) else initial[tid])
                row.update(tid_read_started_ns=time.monotonic_ns(), tid_read_finished_ns=time.monotonic_ns())
                captures.append(copy.deepcopy(row))
                return row
            real_stat = os.stat
            def fd_stat(path, *args, **kwargs):
                if str(path) == '/proc/%d/fd/%d' % (target, lock.fileno()):
                    raise PermissionError('synthetic captured FD loss')
                return real_stat(path, *args, **kwargs)
            if case == 'grace_expired':
                record['process_teardown'] = {'started_ns': time.monotonic_ns() - 2_000_000_000,
                    'deadline_ns': time.monotonic_ns() - 1_000_000_000, 'state': 'awaiting-whole-process-confirmation'}
            decision = {'sample_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        'child': initial[child.pid], 'collection_errors': []}
            before = exits.probe(child)
            assert not before['terminal'] and 'error' not in before
            with patch.object(telemetry, 'capture_child', side_effect=capture), \
                 patch.object(os, 'stat', side_effect=fd_stat), \
                 patch.object(exits, 'is_gone', side_effect=lambda tid: tid in vanished):
                exits.assess(child, decision, record, before, lambda: [{'pid': child.pid}])
            decision['fixture_synthetic_overrides'] = True
            samples.append(decision)
            assert not decision['exit_lifecycle']['terminal_confirmed']
            raw_target = next(row for row in decision['exit_lifecycle']['threads'] if row['pid'] == target)
            assert raw_target['fd_transition_reread']['synthetic_fixture_override'] == fresh['synthetic_fixture_override']
            errors = decision['collection_errors']
            positive = case in ('leader_reread', 'sibling_reread', 'sibling_disappeared')
            if positive or case == 'earlier_rss_breach':
                assert not errors, errors
                assert decision['exit_lifecycle']['teardown_pending'] and decision['exit_lifecycle']['allow_missing_memory']
                effective = decision['exit_lifecycle']['effective_classifications']
                assert all(row['no_mm'] for row in effective.values())
                if case == 'sibling_disappeared':
                    assert str(target) not in effective and record['tid_catalog'][str(target)]['positively_gone']
                else:
                    assert str(target) in effective
            else:
                assert errors, 'Expected fail-closed fresh validation/grace error'
            if case == 'earlier_rss_breach':
                assert decision['observed_process_memory']['rss'] == 6442450944
                account = Accounting(type('Ctx', (), {'record': None, 'case': case})()).sample()
                policy_sample = dict(decision, accounting=account)
                policy = telemetry.policy_errors(policy_sample, account, None, runner.STOP_HEADROOM,
                    runner.RSS_STOP, runner.ANON_GROWTH_STOP, runner.check_memory)
                assert 'Observed live RSS reached 6 GiB stop' in policy
                record['policy_errors'] = policy
            if case == 'fresh_rss_breach':
                assert decision['observed_process_memory']['rss'] == 6442450944
            # Fresh no-mm is deliberately not a completion event. A second
            # decision while the real child is parked is still pending.
            if positive:
                second = {'sample_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                          'child': no_memory(original_rows[child.pid]), 'collection_errors': []}
                effective_rows = {tid: no_memory(original_rows[tid]) for tid in tids}
                with patch.object(telemetry, 'capture_child', side_effect=lambda tid: copy.deepcopy(effective_rows[tid])), \
                     patch.object(Path, 'iterdir', return_value=iter(Path('/proc/%d/task/%d' % (child.pid, tid)) for tid in tids if tid not in vanished)):
                    exits.assess(child, second, record, exits.probe(child), lambda: [{'pid': child.pid}])
                assert not second['collection_errors'], second['collection_errors']
                assert not second['exit_lifecycle']['terminal_confirmed']
                assert second['exit_lifecycle']['teardown_deadline_ns'] == decision['exit_lifecycle']['teardown_deadline_ns']
                samples.append(second)
            child.stdin.write(b'finish\n')
            child.stdin.flush()
            deadline = time.monotonic() + 2
            while True:
                terminal = exits.probe(child)
                if terminal['terminal']:
                    break
                assert time.monotonic() < deadline, 'Real terminal confirmation timeout'
                time.sleep(.005)
            if positive:
                last = {'sample_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        'child': telemetry.capture_child(child.pid), 'collection_errors': []}
                exits.assess(child, last, record, terminal, lambda: [{'pid': child.pid}])
                assert not last['collection_errors'] and last['exit_lifecycle']['terminal_confirmed']
                record['latest_decision_sample'] = last
                assert runner.finish_confirmed(child, record, True)
                samples.append(last)
            else:
                assert runner.owned_wait4(child, record)
                assert record['exit'] == 0
            assert child.returncode == 0 and record['direct_reaped']
            try:
                os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                record['kernel_no_children_verified'] = True
            else:
                raise AssertionError('Fixture child remains')
            record.update(passed=True, state='finished', terminal_confirmation_real=True)
        except BaseException as exc:
            record.update(passed=False, state='failed', failure=repr(exc))
            raise
        finally:
            if child is not None and child.returncode is None:
                os.killpg(child.pid, signal.SIGKILL)
                os.waitpid(child.pid, 0)
                child.returncode = -9
            if child is not None:
                for pipe in [child.stdin, child.stdout, child.stderr]:
                    pipe.close()
            record.update(ended_ns=time.monotonic_ns(), ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
            (folder / 'samples.json').write_text(json.dumps(samples, indent=2) + '\n')
            (folder / 'captures.json').write_text(json.dumps(captures, indent=2) + '\n')
            (folder / 'receipt.json').write_text(json.dumps(record, indent=2) + '\n')
    return {'case': case, 'passed': True, 'receipt': str((folder / 'receipt.json').relative_to(B))}


if __name__ == '__main__':
    with (B / 'effective-reread-fixtures-claimed.json').open('x') as handle:
        json.dump({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'one_suite': True}, handle)
    results = []
    for case in CASES:
        results.append(run_case(case))
        print(case + ' PASS', flush=True)
    (B / 'effective-reread-fixture-results.json').write_text(json.dumps({'cases': results,
        'scope': 'Synthetic deterministic proc/FD transition data with real parked pthread children, universal leases and owned waitid/wait4; no Lean'}, indent=2) + '\n')
