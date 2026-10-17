"""Focused sequential harmless child fixtures; synthetic fields are labeled."""
from pathlib import Path
from unittest.mock import patch
import datetime
import fcntl
import hashlib
import json
import os
import subprocess
import sys
import time
import uuid
import pilot_runner as p
import decision_telemetry as telemetry
from pilot_accounting import AccountingSampleError

B = Path(__file__).resolve().parent
CASES = ['successful_transition', 'live_missing', 'transition_timeout', 'identity_mismatch',
         'accounting_failure', 'visible_breach', 'host_breach', 'anon_breach', 'rss_breach',
         'nonzero_exit', 'signal_exit']


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def accounting():
    return {'namespace': 'synthetic-fixture', 'membership': '0::/\n', 'identities': [],
            'collection_errors': [], 'headroom': 8 * 1024**3, 'system_available': 8 * 1024**3,
            'nodes': [{'path': '/synthetic/group', 'limit': str(16 * 1024**3), 'current': 1,
                       'memory_stat': {'anon': 100, 'file': 200, 'kernel': 50},
                       'memory_events': {'oom': 0}, 'oom': {'oom': 0}, 'pids_current': 1,
                       'pids_max': 'max', 'pids_events': {'max': 0}}]}


def run_case(case, lock, root):
    folder = root / uuid.uuid4().hex
    folder.mkdir()
    code = 'import time,os,signal\ntime.sleep(60)\n'
    if case == 'successful_transition':
        code = 'import time\ntime.sleep(.12)\n'
    if case == 'nonzero_exit':
        code = 'import time,os\ntime.sleep(.12)\nos._exit(7)\n'
    if case == 'signal_exit':
        code = 'import time,os,signal\ntime.sleep(.12)\nos.kill(os.getpid(),signal.SIGTERM)\n'
    source = folder / 'submitted-child.py'
    source.write_text(code)
    st = os.fstat(lock.fileno())
    r = {'attempt_id': folder.name, 'fixture_only': True, 'compiler_or_checker': False,
         'case': case, 'created_utc': utc(), 'started_ns': time.monotonic_ns(),
         'lock': {'fd': lock.fileno(), 'device': st.st_dev, 'inode': st.st_ino},
         'submitted_source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
         'submitted_sources': {name: hashlib.sha256((B / name).read_bytes()).hexdigest()
                               for name in ['pilot_runner.py', 'decision_telemetry.py', 'exit_transition.py', 'test_exit_transition.py']},
         'supervisor_pid': os.getpid(), 'deadline_seconds': 90,
         'synthetic_telemetry': case not in ('nonzero_exit', 'signal_exit')}

    def save():
        temp = folder / 'receipt.tmp'
        with temp.open('w') as f:
            json.dump(r, f, indent=2)
            f.write('\n')
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp, folder / 'receipt.json')

    old_subreaper = p.life.set_subreaper(True)
    child = None
    outcome = None
    try:
        with p.LOCK.open('r+') as other:
            try:
                fcntl.flock(other, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                r['exclusive_lock_verified'] = True
            else:
                raise AssertionError('Universal lock not exclusive')
        r['runtime_wall_started_ns'] = time.monotonic_ns()
        argv = [sys.executable, '-I', str(source)]
        r['argv'] = argv
        child = subprocess.Popen(argv, env={'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'},
                                 pass_fds=(lock.fileno(),), start_new_session=True,
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        r['child_pid'] = child.pid
        real_capture = telemetry.capture_child
        r['child_identity'] = real_capture(child.pid)
        r['inherited_lock_verified'] = os.stat('/proc/%s/fd/%s' % (child.pid, lock.fileno())).st_ino == st.st_ino
        assert r['inherited_lock_verified']
        baseline = accounting()
        anon_baseline = {'/synthetic/group': 100}

        class Accounting:
            calls = 0
            def sample(self):
                self.calls += 1
                data = accounting()
                if self.calls >= 2:
                    if case == 'accounting_failure':
                        raise AccountingSampleError('Synthetic accounting failure during transition',
                                                    {'collection_errors': [{'operation': 'synthetic accounting', 'error': 'fixture'}], 'partial_raw': 'preserved'})
                    if case == 'visible_breach':
                        data['headroom'] = p.STOP_HEADROOM - 1
                    if case == 'host_breach':
                        data['system_available'] = p.STOP_HEADROOM - 1
                    if case == 'anon_breach':
                        data['nodes'][0]['memory_stat']['anon'] += p.ANON_GROWTH_STOP
                return data

        accounting_instance = Accounting()

        def capture(pid):
            data = real_capture(pid)
            if case in ('nonzero_exit', 'signal_exit'):
                return data
            data.update(state='R', rss=None, vm=None, stat_threads=1, status_threads=1,
                        stat_flags=data.get('stat_flags', 0) | 4,
                        stat_vsize_bytes=0, stat_rss_pages=0,
                        collection_errors=[{'operation': 'VmRSS', 'error': 'Missing required live value'},
                                           {'operation': 'VmSize', 'error': 'Missing required live value'}],
                        partial_stat='SYNTHETIC identity-matching single-thread PF_EXITING zero memory',
                        partial_status='SYNTHETIC State R without VmRSS/VmSize')
            if case == 'live_missing':
                data['stat_flags'] &= ~4
                data['stat_vsize_bytes'] = 4096
            if case == 'identity_mismatch':
                data['start_ticks'] += 1
            if case == 'rss_breach':
                data['rss'] = p.RSS_STOP
            return data

        save()
        with (folder / 'samples.jsonl').open('x') as samples, patch.object(telemetry, 'capture_child', side_effect=capture):
            try:
                while True:
                    p.runtime_sample(child, baseline, anon_baseline, accounting_instance, r, save, samples)
                    if r['latest_decision_sample']['exit_lifecycle'].get('terminal_confirmed'):
                        assert child.returncode is None  # WNOWAIT has not reaped.
                        r['waitid_nonreaping_verified'] = True
                        r['terminal_child_fd_closed'] = not Path('/proc/%s/fd/%s' % (child.pid, lock.fileno())).exists()
                    if p.finish_confirmed(child, r, True):
                        outcome = 'success'
                        break
                    time.sleep(.02)
            except (p.MemoryGuardError, RuntimeError) as exc:
                r['expected_fixture_exception'] = repr(exc)
                outcome = 'fail-closed'
        if case == 'successful_transition':
            assert outcome == 'success' and child.returncode == 0
            assert r['exit_transition']['state'] == 'kernel-confirmed'
            assert r['waitid_nonreaping_verified'] and r['terminal_child_fd_closed']
            assert not r.get('memory_stop_attempted')
        else:
            assert outcome == 'fail-closed'
        if case in ('nonzero_exit', 'signal_exit'):
            assert r['waitid_nonreaping_verified'] and r['waitid_wait4_status_match']
            assert child.returncode == (7 if case == 'nonzero_exit' else -15)
        if case == 'transition_timeout':
            assert 'timeout' in r['expected_fixture_exception']
        if case == 'identity_mismatch':
            assert 'identity mismatch' in r['expected_fixture_exception']
        if 'stop_decision_sample' in r:
            last = json.loads((folder / 'samples.jsonl').read_text().splitlines()[-1])
            assert last == r['stop_decision_sample'] == r['latest_decision_sample']
            assert last['sample_finished_ns'] <= r['memory_stop_signal_started_ns'] <= r['memory_stop_signal_finished_ns']
            r['exact_stop_sample_and_signal_order_verified'] = True
        r['fixture_assertions_passed'] = True
    finally:
        if child is not None:
            p.reap_direct(child, r, save)
            p.life.cleanup(child, r, save)
        p.life.set_subreaper(old_subreaper)
        r.update(ended_utc=utc(), ended_ns=time.monotonic_ns(), outcome=outcome)
        save()
    assert r['direct_reaped'] and r['kernel_no_children_verified'] and r['all_descendants_gone']
    return {'case': case, 'attempt_id': folder.name, 'receipt': str((folder / 'receipt.json').relative_to(B)),
            'fixture_passed': True, 'child_exit': child.returncode}


if __name__ == '__main__':
    with (B / 'focused-fixtures-claimed.json').open('x') as f:
        json.dump({'utc': utc(), 'one_focused_suite': True}, f)
    root = B / 'focused-fixtures'
    root.mkdir(exist_ok=False)
    results = []
    with p.LOCK.open('r+') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        assert (os.fstat(lock.fileno()).st_dev, os.fstat(lock.fileno()).st_ino) == (33, 3849)
        for case in CASES:
            results.append(run_case(case, lock, root))
            print(case, 'PASS', flush=True)
    (B / 'focused-fixture-results.json').write_text(json.dumps({'utc': utc(), 'fixtures': results,
        'scope': 'Sequential harmless Python children, synthetic transition/accounting fields labeled; real owned waitid/wait4, lock and reaping'}, indent=2) + '\n')
