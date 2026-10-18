"""Harmless deterministic proc snapshots; real owned children and lock/waits.

Synthetic state/identity/FD overrides are recorded alongside original proc reads.
The historical Core snapshot is preserved verbatim; only its process identities
are remapped to this fixture's owned four-thread child, explicitly below.
"""
from pathlib import Path
from unittest.mock import patch
from contextlib import ExitStack
import copy, datetime, hashlib, json, os, resource, select, signal, subprocess, sys, time, uuid
import child_runner as runner
import decision_telemetry as telemetry
import exit_transition as exits
from shared_preservation import Lease
from test_whole_process import Accounting

B = Path(__file__).resolve().parent
CASES = ['saved_mixed_exiting', 'saved_mixed_healthy', 'fresh_healthy', 'fresh_exiting',
         'fresh_gone', 'persistent_missing', 'start_mismatch', 'tgid_mismatch',
         'fresh_malformed', 'fresh_access_error', 'initial_malformed', 'lost_lock',
         'sibling_lost_lock', 'earlier_rss', 'unrelated_memory_error',
         'unrelated_collection_error', 'grace_expiry', 'fd_first_missing']
SOURCE = '''import threading,json,sys
event=threading.Event()
workers=[threading.Thread(target=event.wait) for _ in range(3)]
for worker in workers:worker.start()
print(json.dumps([threading.get_native_id()]+[worker.native_id for worker in workers]),flush=True)
sys.stdin.readline()
event.set()
for worker in workers:worker.join()
'''


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def stamp(row):
    row = copy.deepcopy(row)
    row.update(tid_read_started_ns=time.monotonic_ns(), tid_read_finished_ns=time.monotonic_ns())
    return row


def missing(row, rss_too=True):
    # Use the real parser on a deterministic incomplete status capture.
    lines = [s for s in row['raw_status'].splitlines()
             if not s.startswith('VmSize:') and (not rss_too or not s.startswith('VmRSS:'))]
    value = telemetry.capture_child(row['pid'], row['raw_stat'], '\n'.join(lines)+'\n')
    value['synthetic_fixture_override'] = 'omit VmSize' + (' and VmRSS' if rss_too else '')
    return value


def exiting(row):
    row = missing(row)
    row.update(state='Z', stat_flags=row['stat_flags'] | exits.PF_EXITING,
               stat_vsize_bytes=0, stat_rss_pages=0,
               synthetic_fixture_override='identity-preserving positive exiting/no-mm')
    return row


def gone(tid):
    # Exact capture_child shape for two actual ENOENT proc reads, including
    # consequential parser failures. The real child remains parked for safety.
    with patch.object(Path, 'read_text', side_effect=FileNotFoundError(2, 'synthetic owned TID gone')):
        row = telemetry.capture_child(tid)
    row['synthetic_fixture_override'] = 'positive owned-sibling disappearance'
    return row


def run_case(case):
    folder = B/'memory-reread-fixtures'/(case+'-'+uuid.uuid4().hex)
    folder.mkdir(parents=True)
    source = folder/'submitted.py'; source.write_text(SOURCE)
    record = {'attempt_id': uuid.uuid4().hex, 'case': case, 'fixture_only': True,
              'compiler_or_checker': False, 'synthetic_proc_overrides': True,
              'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'started_ns': time.monotonic_ns(), 'submitted_source_sha256': sha(source),
              'harness_hashes': {n: sha(B/n) for n in ['test_memory_reread.py', 'exit_transition.py',
                  'decision_telemetry.py', 'child_runner.py', 'shared_preservation.py']},
              'runtime_wall_started_ns': time.monotonic_ns(), 'deadline_seconds': 90}
    child = None; samples = []; captures = []; fd_checks = []
    with Lease(folder/'lease.json') as lock:
        st = os.fstat(lock.fileno())
        record['lock'] = {'fd': lock.fileno(), 'device': st.st_dev, 'inode': st.st_ino}
        def limits():
            for name, value in runner.LIMITS.items():
                resource.setrlimit(getattr(resource, name), (value, value))
        try:
            child = subprocess.Popen([sys.executable, '-I', str(source)], stdin=subprocess.PIPE,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, pass_fds=(lock.fileno(),),
                start_new_session=True, preexec_fn=limits)
            record['child_pid'] = child.pid
            assert select.select([child.stdout], [], [], 3)[0], 'Readiness timeout'
            tids = json.loads(child.stdout.readline()); assert len(tids) == 4 and tids[0] == child.pid
            original = {tid: telemetry.capture_child(tid) for tid in tids}
            assert all(not row['collection_errors'] for row in original.values())
            record['original_proc_rows'] = original
            record['child_identity'] = original[child.pid]
            record['tid_catalog'] = {str(tid): {'tid': tid, 'tgid': child.pid,
                'start_ticks': original[tid]['start_ticks']} for tid in tids}
            sibling_case = case in ('fresh_gone', 'sibling_lost_lock') or case.startswith('saved_mixed_')
            target = tids[1] if sibling_case else child.pid
            initial = {tid: exiting(row) for tid, row in original.items()}
            initial[target] = missing(original[target])
            fresh = copy.deepcopy(original[target])
            vanished = set(tids[2:]) if case.startswith('saved_mixed_') else set()
            fd_lost = {target} if case in ('lost_lock', 'sibling_lost_lock', 'fd_first_missing') else set()
            if case == 'sibling_lost_lock':
                initial[child.pid] = copy.deepcopy(original[child.pid]); initial[child.pid]['rss'] = 200_000_000
                fresh['rss'] = 100_000_000
            if case in ('fresh_exiting', 'grace_expiry'):
                fresh = exiting(original[target])
            if case == 'fresh_gone': fresh = gone(target)
            if case in ('persistent_missing', 'fd_first_missing'): fresh = missing(original[target])
            if case == 'fd_first_missing': initial[target] = copy.deepcopy(original[target])
            if case == 'start_mismatch': fresh['start_ticks'] += 1
            if case == 'tgid_mismatch': fresh['tgid'] += 1
            if case == 'fresh_malformed': fresh['collection_errors'].append({'operation': 'parse child identity', 'error': 'synthetic malformed stat'})
            if case == 'fresh_access_error': fresh['collection_errors'].append({'operation': 'child status', 'error': "PermissionError(13, 'synthetic denied')"})
            if case == 'initial_malformed': initial[target]['collection_errors'].append({'operation': 'parse child identity', 'error': 'synthetic initial malformed stat'})
            if case == 'earlier_rss':
                initial[target] = missing(original[target], rss_too=False)
                initial[target]['rss'] = runner.RSS_STOP
                fresh['rss'] = 100_000_000
            if case.startswith('saved_mixed_'):
                historical = json.loads((B/'saved-mixed-snapshot.json').read_text())
                raw = historical['stop_decision_sample']
                saved = {row['pid']: row for row in raw['exit_lifecycle']['threads']}
                mapping = dict(zip(sorted(saved), tids))
                record['historical_identity_remapping'] = {str(k): v for k,v in mapping.items()}
                for old, new in mapping.items():
                    initial[new] = copy.deepcopy(saved[old])
                    initial[new].pop('fd_transition_reread', None)
                    if new not in vanished:
                        for key in ['pid','stat_pid','status_pid','tgid','ppid','sid','pgid','start_ticks']:
                            initial[new][key] = original[new][key]
                    else: initial[new] = gone(new)
                    initial[new]['synthetic_fixture_override'] = 'saved mixed snapshot with explicit owned identity remapping'
                leader_fresh = copy.deepcopy(saved[275244]['fd_transition_reread'])
                for key in ['pid','stat_pid','status_pid','tgid','ppid','sid','pgid','start_ticks']:
                    leader_fresh[key] = original[child.pid][key]
                leader_fresh['synthetic_fixture_override'] = 'saved identity-matched zombie leader reread'
                fd_lost.add(child.pid)
                fresh = exiting(original[target]) if case.endswith('exiting') else copy.deepcopy(original[target])
                fresh['synthetic_fixture_override'] = 'fresh worker response to saved mixed snapshot'
                assert initial[target]['state'] == 'R' and initial[target]['stat_vsize_bytes'] > 0
                assert initial[target]['rss'] is None and initial[target]['vm'] is None
                assert exits.no_mm(leader_fresh)
            calls = {}
            def capture(tid):
                calls[tid] = calls.get(tid, 0) + 1
                if tid == child.pid:
                    row = leader_fresh if case.startswith('saved_mixed_') else fresh
                elif tid == target and calls[tid] > 1: row = fresh
                else: row = initial[tid]
                row = stamp(row); captures.append(copy.deepcopy(row)); return row
            real_stat = os.stat
            def fd_stat(path, *args, **kwargs):
                for tid in tids:
                    if str(path) == '/proc/%d/fd/%d' % (tid, lock.fileno()):
                        fd_checks.append({'tid':tid, 'ns':time.monotonic_ns(), 'lost':tid in fd_lost})
                        if tid in fd_lost: raise PermissionError('synthetic live inherited lock loss')
                return real_stat(path, *args, **kwargs)
            decision = {'sample_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        'child': stamp(initial[child.pid]), 'collection_errors': []}
            # Exactly mirror collect(): original-leader error object identities.
            decision['collection_errors'] += decision['child']['collection_errors']
            extra = None
            if case == 'unrelated_memory_error': extra = {'operation':'VmRSS','error':'Missing required live value'}
            if case == 'unrelated_collection_error': extra = {'operation':'accounting','error':'synthetic unrelated error'}
            if extra is not None: decision['collection_errors'].append(extra)
            record['synthetic_initial_rows'] = copy.deepcopy(initial)
            record['synthetic_fresh_row'] = copy.deepcopy(fresh)
            before = exits.probe(child); assert not before['terminal'] and not before.get('error')
            with patch.object(telemetry,'capture_child',side_effect=capture), \
                 patch.object(os,'stat',side_effect=fd_stat), \
                 patch.object(exits,'is_gone',side_effect=lambda tid: tid in vanished or (case=='fresh_gone' and tid==target)):
                exits.assess(child, decision, record, before, lambda:[{'pid':child.pid}])
            samples.append(decision)
            assert not decision['exit_lifecycle']['terminal_confirmed'], 'Incomplete fields/zombie must not complete child'
            negative = case in ['persistent_missing','start_mismatch','tgid_mismatch','fresh_malformed',
                'fresh_access_error','initial_malformed','lost_lock','sibling_lost_lock','fd_first_missing']
            assert bool(decision['collection_errors'][-1:]) if negative else True
            account = Accounting(type('Ctx',(),{'record':None,'case':case})()).sample()
            def policy(sample):
                return telemetry.policy_errors(dict(sample,accounting=account),account,None,
                    runner.STOP_HEADROOM,runner.RSS_STOP,runner.ANON_GROWTH_STOP,runner.check_memory)
            errors = policy(decision); record['policy_errors'] = errors
            reject = negative or case in ('earlier_rss','unrelated_memory_error','unrelated_collection_error')
            assert bool(errors) == reject, errors
            rereads = decision['exit_lifecycle'].get('immediate_rereads',[])
            assert len({r['tid'] for r in rereads}) == len(rereads), 'Second reread of same TID'
            target_reads = [r for r in rereads if r['tid']==target]
            assert len(target_reads)==(0 if case=='initial_malformed' else 1)
            for r in rereads:
                assert r['original_started_ns'] <= r['original_finished_ns'] <= r['fresh_started_ns'] <= r['fresh_finished_ns']
            if case in ('fresh_healthy','saved_mixed_healthy','earlier_rss'):
                assert any(r['tid']==target and not r['lost'] for r in fd_checks)
                assert decision['exit_lifecycle']['effective_classifications'][str(target)]['rss']==fresh['rss']
            if case=='earlier_rss':
                assert decision['observed_process_memory']['rss']==runner.RSS_STOP
                assert 'Observed live RSS reached 6 GiB stop' in errors
            if extra is not None:
                assert repr(extra) in errors
                assert len(decision['exit_lifecycle']['superseded_original_leader_memory_errors'])==2
                assert extra is decision['collection_errors'][2]
            if case=='fresh_gone':
                assert record['tid_catalog'][str(target)]['positively_gone']
                assert str(target) not in decision['exit_lifecycle']['effective_classifications']
            if case=='grace_expiry':
                fixed=record['process_teardown']['deadline_ns']
                assert fixed-record['process_teardown']['started_ns']<=exits.TRANSITION_NS
                for tick in [fixed-1,fixed+1]:
                    later={'sample_utc':decision['sample_utc'],'child':stamp(exiting(original[child.pid])),'collection_errors':[]}
                    with patch.object(telemetry,'capture_child',side_effect=lambda tid:stamp(exiting(original[tid]))), \
                         patch.object(exits.time,'monotonic_ns',return_value=tick):
                        exits.assess(child,later,record,exits.probe(child),lambda:[{'pid':child.pid}])
                    assert record['process_teardown']['deadline_ns']==fixed
                    assert bool(later['collection_errors'])==(tick>fixed)
                    samples.append(later)
                assert any('grace expired' in str(e) for e in later['collection_errors'])
                record['guard_rejection_preserved']=True
            record['expected_policy_rejection']=reject
            record['capture_counts']={str(k):v for k,v in calls.items()}
            child.stdin.write(b'finish\n'); child.stdin.flush()
            deadline=time.monotonic()+3
            while True:
                terminal=exits.probe(child)
                if terminal['terminal']:break
                assert time.monotonic()<deadline,'Owned terminal timeout'
                time.sleep(.005)
            assert runner.owned_wait4(child,record) and record['exit']==0
            expected=terminal['status'] if terminal['code']==os.CLD_EXITED else -terminal['status']
            assert record['exit']==expected
            record['owned_terminal_probe']=terminal;record['waitid_wait4_status_match']=True
            assert record['direct_reaped']
            try:os.waitpid(-1,os.WNOHANG)
            except ChildProcessError:record['kernel_no_children_verified']=True
            else:raise AssertionError('Unreaped fixture child')
            # Exit zero is a cleanup result, never an override of policy failure.
            assert bool(policy(decision))==reject
            record.update(passed=True,state='finished')
        except BaseException as exc:
            record.update(passed=False,state='failed',failure=repr(exc));raise
        finally:
            if child is not None and child.returncode is None:
                os.killpg(child.pid,signal.SIGKILL)
                while not runner.owned_wait4(child,record):time.sleep(.005)
            if child is not None:
                for pipe in [child.stdin,child.stdout,child.stderr]:pipe.close()
            record.update(ended_ns=time.monotonic_ns(),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
            for name,data in [('receipt',record),('samples',samples),('captures',captures),('fd-checks',fd_checks)]:
                (folder/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    return {'case':case,'passed':True,'receipt':str((folder/'receipt.json').relative_to(B))}


if __name__=='__main__':
    invocation=uuid.uuid4().hex
    selected=sys.argv[1:] or CASES
    assert all(c in CASES for c in selected)
    results=[]
    for case in selected:
        results.append(run_case(case));print(case+' PASS',flush=True)
    (B/('memory-reread-results-'+invocation+'.json')).write_text(json.dumps({'cases':results,
        'scope':'harmless Python thread children; synthetic proc snapshots; real universal leases and owned waitid/wait4'},indent=2)+'\n')
