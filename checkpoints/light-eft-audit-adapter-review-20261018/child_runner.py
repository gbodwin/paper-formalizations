"""Reviewed child supervision adapted only for the whole-batch shared lease/hooks."""
from pathlib import Path
from contextlib import nullcontext
import datetime,fcntl,json,os,resource,select,signal,subprocess,sys,time,uuid
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
sys.path.insert(0,str(REPO/'scripts'))
import LightEFTProcessLifecycle as life
from pilot_accounting import VisibleAccounting
from pilot_child import LIMITS
import decision_telemetry as telemetry
import exit_transition as exits
from audit_outputs import runtime_errors as audit_output_errors
LOCK=Path('/tmp/distance-sparsification-single-compiler.lock')
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
ADMISSION_HEADROOM=3221225472
STOP_HEADROOM=1073741824
RSS_STOP=6442450944
ANON_GROWTH_STOP=3221225472
DECISION_LOG_BOUND=16*1024**2
INTERVAL=.1
DEADLINE=90.0
class MemoryGuardError(RuntimeError):pass


def child_status(pid):
    row=telemetry.capture_child(pid)
    if row['collection_errors']:
        exc=MemoryGuardError('Partial child telemetry');exc.partial=row;raise exc
    return row

def kill_memory_group(child,record,save,reason):
    if child is None or record.get('memory_stop_attempted'):return
    record['memory_stop_attempted']=True
    record['memory_stop_reason']=reason
    record['memory_stop_signal_started_ns']=time.monotonic_ns()
    # The direct child has its own session/group and is not reaped before this call.
    # Signal precedes persistence or any other diagnostic work.
    try:
        os.killpg(child.pid,signal.SIGKILL);record['memory_stop_signal_sent']=True
    except ProcessLookupError:record['memory_stop_group_already_gone']=True
    record['memory_stop_signal_finished_ns']=time.monotonic_ns();save()

def runtime_sample(child,baseline,anon_baseline,accounting,record,save,samples,minimum_headroom=STOP_HEADROOM,minimum_host_headroom=None):
    before_probe=exits.probe(child)
    decision=telemetry.collect(child,accounting)
    try:
        decision['collection_errors'] += [{'operation':'audit output budget','error':error}
            for error in audit_output_errors(record,preexec=minimum_headroom>STOP_HEADROOM)]
    except Exception as exc:
        decision['collection_errors'].append({'operation':'audit output budget','error':repr(exc)})
    # Capture the exact decision input in memory before any policy evaluation.
    record['latest_decision_sample']=decision
    try:exits.assess(child,decision,record,before_probe,life.descendants)
    except Exception as exc:decision['collection_errors'].append({'operation':'exit supervision','error':repr(exc)})
    current=decision.get('observed_process_memory',decision.get('process_memory',decision.get('child'))) or {}
    for field,key in [('rss','sampled_rss_peak_bytes'),('vm','sampled_vm_peak_bytes')]:
        value=current.get(field)
        if isinstance(value,int):record[key]=max(record.get(key,0),value)
    errors=telemetry.policy_errors(decision,baseline,anon_baseline,minimum_headroom,RSS_STOP,ANON_GROWTH_STOP,check_memory,minimum_host_headroom)
    encoded=json.dumps(decision,separators=(',',':'))+'\n'
    if samples.tell()+len(encoded.encode())>DECISION_LOG_BOUND:errors.append('Decision sample log bound reached; exact sample retained in receipt')
    if errors:
        record['stop_decision_sample']=decision;record['stop_decision_errors']=errors
        kill_memory_group(child,record,save,'; '.join(errors))
        if samples.tell()+len(encoded.encode())<=DECISION_LOG_BOUND:
            samples.write(encoded);samples.flush();os.fsync(samples.fileno())
        raise MemoryGuardError('; '.join(errors))
    try:samples.write(encoded);samples.flush()
    except Exception as exc:
        record['stop_decision_sample']=decision;record['sample_persistence_error']=repr(exc)
        kill_memory_group(child,record,save,repr(exc));raise MemoryGuardError('Decision sample persistence failed') from exc
    return decision['accounting'],decision['child']

def assert_idle(label,record):
    raw=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
    if any(line.split()[-1] in ('lean','lake','leanchecker','leantar','strace') and not line.split()[2].startswith('Z') for line in raw.splitlines()[1:]):raise RuntimeError('Compiler/checker/tracer active during idle verification')
    record.setdefault('idle_verifications',[]).append({'phase':label,'monotonic_ns':time.monotonic_ns(),'processes':raw})

def check_memory(now,baseline,minimum):
    if now['headroom']<minimum:raise MemoryGuardError('Visible headroom below required floor')
    for a,b in zip(now['nodes'],baseline['nodes'],strict=True):
        if a['path']!=b['path'] or a['limit']!=b['limit']:raise RuntimeError('Accounting limit changed')
        if any(a['oom'][k]!=b['oom'][k] for k in b['oom']):raise MemoryGuardError('OOM counters changed')
        if a['pids_max']!=b['pids_max'] or a['pids_events']!=b['pids_events']:raise RuntimeError('PID limit/events changed')
        if a['pids_max']!='max' and a['pids_current']>=int(a['pids_max']):raise RuntimeError('Visible PID limit exhausted')

def verify_ready(packet,child,lockfd,first,current=None):
    if 'error' in packet:raise RuntimeError('Child limit setup/readback failure: '+packet['error'])
    st=os.fstat(lockfd)
    expected={k:[v,v] for k,v in LIMITS.items()}
    if packet['limits']!=expected:raise RuntimeError('Child limit readback mismatch')
    for name,value in LIMITS.items():
        if resource.prlimit(child.pid,getattr(resource,name))!=(value,value):raise RuntimeError('Kernel limit readback mismatch')
    if current is None:current=child_status(child.pid)
    if current['start_ticks']!=first['start_ticks'] or current['ppid']!=os.getpid():raise RuntimeError('Child identity changed')
    for key in ('sid','pgid'):
        if packet[key]!=child.pid or current[key]!=child.pid:raise RuntimeError('No isolated session')
    remote=os.stat(f'/proc/{child.pid}/fd/{lockfd}')
    if packet['pid']!=child.pid or packet['ppid']!=os.getpid() or packet['lock_fd']!=lockfd or not packet['lock_inheritable']:raise RuntimeError('Bad lock handshake')
    if [packet['lock_device'],packet['lock_inode']]!=[st.st_dev,st.st_ino] or (remote.st_dev,remote.st_ino)!=(st.st_dev,st.st_ino):raise RuntimeError('Inherited lock identity mismatch')

def owned_wait4(child,record):
    if child.returncode is not None:return True
    pid,status,usage=os.wait4(child.pid,os.WNOHANG)
    if not pid:return False
    child.returncode=os.waitstatus_to_exitcode(status)
    record.update(exit=child.returncode,direct_wait_owner='runner wait4',direct_reaped=True,wait4_maxrss_kib=usage.ru_maxrss)
    return True

def finish_confirmed(child,record,approved):
    status=record['latest_decision_sample'].get('exit_lifecycle',{})
    if not status.get('terminal_confirmed'):return False
    confirmation=status['confirmation']
    if not owned_wait4(child,record):raise RuntimeError('Confirmed terminal child not wait4-reapable')
    expected=confirmation['status'] if confirmation['code']==os.CLD_EXITED else -confirmation['status']
    if child.returncode!=expected:raise RuntimeError('waitid/wait4 status mismatch')
    record['waitid_wait4_status_match']=True
    if not approved or child.returncode!=0:raise RuntimeError('Child failed before/after exec')
    return True

def reap_direct(child,record,save):
    began=time.monotonic()
    while not owned_wait4(child,record):
        sig=signal.SIGTERM if time.monotonic()-began<1 else signal.SIGKILL
        try:os.kill(child.pid,sig)
        except ProcessLookupError:pass
        time.sleep(.02)

def run_child(plan,pilot,evidence,shared,accounting=None):
    """Private testable supervisor. Production uses run_once with fixed paths/plan."""
    record={'attempt_id':uuid.uuid4().hex,'scope':'AUDIT_ONLY_SINGLE_OFFICIAL_LEAN_INVOCATION','stage':plan['stage'],'source_commit':SOURCE,'argv':plan['argv'],'environment':plan['env'],'memory_policy':{'as_bytes':LIMITS['RLIMIT_AS'],'file_size_bytes':LIMITS['RLIMIT_FSIZE'],'admission_visible_bytes':shared.visible_gate(plan),'admission_host_bytes':ADMISSION_HEADROOM,'stop_visible_host_bytes':STOP_HEADROOM,'rss_observed_stop_bytes':RSS_STOP,'per_cgroup_anon_growth_stop_bytes':ANON_GROWTH_STOP,'sample_seconds':INTERVAL,'immediate_group_signal':'SIGKILL','M_qualification':'Intermittent runtime RSS check, not a kernel heap cap'},'state':'created','started_ns':time.monotonic_ns(),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'supervisor_pid':os.getpid()}
    evidence.mkdir(exist_ok=False,parents=True)
    child=None;old=None;handlers={};fds=[];before=[];anon_baseline=None
    accounting=VisibleAccounting() if accounting is None else accounting
    def save():
        t=evidence/'receipt.tmp'
        with t.open('w') as f:
            json.dump(record,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.replace(t,evidence/'receipt.json')
        fd=os.open(evidence,os.O_RDONLY|os.O_DIRECTORY)
        try:os.fsync(fd)
        finally:os.close(fd)
    save()
    # Existing universal inode only; never create/replace the production lock.
    with nullcontext(shared.lock) as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            record.update(state='refused-lock',failure='Universal lock busy; no child spawned');save();raise
        st=os.fstat(lock.fileno());record['lock']={'path':str(LOCK),'device':st.st_dev,'inode':st.st_ino,'fd':lock.fileno(),'child_entry_ns':time.monotonic_ns(),'outer_acquired_ns':shared.acquired_ns};save()
        try:
            for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP):
                handlers[sig]=signal.getsignal(sig)
                def interrupted(s,f):raise InterruptedError('supervisor signal '+str(s))
                signal.signal(sig,interrupted)
            if life.descendants():raise RuntimeError('Preexisting child process')
            shared.before_child(plan,record,save)
            baseline=shared.prepare_child(plan,record,save,accounting)
            processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True);record['processes_before']=processes
            if any(row.split()[-1] in ('lean','lake','leanchecker','leantar') and not row.split()[2].startswith('Z') for row in processes.splitlines()[1:]):raise RuntimeError('Other compiler/checker/extractor active')
            old=life.set_subreaper(True)
            if life.descendants():raise RuntimeError('Unexpected child before spawn')
            cfg_r,cfg_w=os.pipe();ready_r,ready_w=os.pipe();ack_r,ack_w=os.pipe();fds=[cfg_r,cfg_w,ready_r,ready_w,ack_r,ack_w]
            config=json.dumps({'argv':plan['argv'],'env':plan['env']}).encode()
            if len(config)>4096:raise RuntimeError('Launcher config too long')
            os.write(cfg_w,config);os.close(cfg_w);fds.remove(cfg_w)
            started=time.monotonic();record['runtime_wall_started_ns']=time.monotonic_ns();record['deadline_seconds']=DEADLINE
            with (evidence/'raw.log').open('xb') as log:
                blocked=signal.pthread_sigmask(signal.SIG_BLOCK,set(handlers))
                try:
                    child=subprocess.Popen([sys.executable,'-I',str(HERE/'pilot_child.py'),str(cfg_r),str(ready_w),str(ack_r),str(lock.fileno())],cwd=pilot,env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},stdout=log,stderr=subprocess.STDOUT,pass_fds=(cfg_r,ready_w,ack_r,lock.fileno()),start_new_session=True,
                        preexec_fn=lambda:signal.pthread_sigmask(signal.SIG_SETMASK,blocked))
                finally:signal.pthread_sigmask(signal.SIG_SETMASK,blocked)
                for fd in (cfg_r,ready_w,ack_r):os.close(fd);fds.remove(fd)
                record.update(child_pid=child.pid,state='handshake-wait');save()
                buffer=b'';approved=False
                with (evidence/'samples.jsonl').open('x') as samples:
                    _,first=runtime_sample(child,baseline,None,accounting,record,save,samples)
                    record['child_identity']=first;save()
                    while True:
                        loop_started=time.monotonic()
                        now,current=runtime_sample(child,baseline,anon_baseline,accounting,record,save,samples)
                        record.update(sample_interval_seconds=INTERVAL,vm_peak_qualification='100ms sampled; null teardown metrics preserved; not a continuous peak')
                        if time.monotonic()-started>=DEADLINE:raise TimeoutError('Child wall deadline')
                        if not approved:
                            readable,_,_=select.select([ready_r],[],[],0)
                            if readable:
                                chunk=os.read(ready_r,8192);buffer+=chunk
                                if len(buffer)>8192:raise RuntimeError('Oversized handshake')
                                if b'\n' in buffer:
                                    packet=json.loads(buffer)
                                    fresh,pre_current=runtime_sample(child,baseline,None,accounting,record,save,samples,shared.visible_gate(plan),ADMISSION_HEADROOM)
                                    verify_ready(packet,child,lock.fileno(),first,pre_current)
                                    anon_baseline={node['path']:node['memory_stat']['anon'] for node in fresh['nodes']}
                                    record['anonymous_preexec_baseline']=anon_baseline
                                    record['preexec_decision_sample']=record['latest_decision_sample']
                                    record['preexec_admission']=fresh
                                    record['handshake']=packet;record['preexec_verified_ns']=time.monotonic_ns();save()
                                    os.write(ack_w,b'G');os.close(ack_w);fds.remove(ack_w);approved=True;record['state']='exec-authorized'
                                elif not chunk:raise RuntimeError('Launcher exited without handshake')
                        if finish_confirmed(child,record,approved):break
                        time.sleep(max(0,INTERVAL-(time.monotonic()-loop_started)))
        except BaseException as exc:
            if isinstance(exc,MemoryGuardError):kill_memory_group(child,record,save,repr(exc))
            if hasattr(exc,'partial'):record['partial_collection_failure']=exc.partial
            record['failure']=repr(exc)
        finally:
            # Fail-stop barrier: cleanup/finalization errors cannot release lock.
            while True:
                try:
                    for sig in handlers:life.retry_locked('ignore-cleanup-signal',lambda sig=sig:signal.signal(sig,signal.SIG_IGN),record,save)
                    for fd in fds:
                        try:os.close(fd)
                        except OSError:pass
                    fds=[]
                    if child is not None:
                        life.retry_locked('runner-direct-wait4',lambda:reap_direct(child,record,save),record,save)
                        # returncode is already set; lifecycle poll never reaps direct PID.
                        life.cleanup(child,record,save)
                        if record.get('descendants_observed'):record.setdefault('failure','Unexpected detached/adopted descendant during cleanup')
                    else:
                        if life.descendants():raise RuntimeError('Unexpected children before spawn')
                        try:os.waitpid(-1,os.WNOHANG)
                        except ChildProcessError:record['kernel_no_children_verified']=True
                        else:raise RuntimeError('Kernel child remains')
                    try:
                        shared.after_child(plan,record,save)
                    except BaseException as exc:
                        record.setdefault('failure',repr(exc));record['between_child_preservation_passed']=False
                        shared.preservation_failed=True
                    try:
                        for filename in ['raw.log','samples.jsonl']:
                            path=evidence/filename
                            if path.exists():shared.complete_log(path,record,save)
                    except BaseException as exc:
                        record.setdefault('failure',repr(exc));record['completed_file_housekeeping_error']=repr(exc)
                    record['outputs_after']=shared.output_summary()
                    if old is not None:life.retry_locked('restore-subreaper',lambda:life.set_subreaper(old),record,save)
                    record.update(ended_ns=time.monotonic_ns(),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),state='failed' if 'failure' in record else 'finished')
                    life.retry_locked('finalize',save,record,save)
                    for sig,handler in handlers.items():life.retry_locked('restore-signals',lambda sig=sig,handler=handler:signal.signal(sig,handler),record,save)
                    break
                except BaseException as e:life.cleanup_error('pilot-finalization-barrier',e,record,save)
    if 'failure' in record:raise RuntimeError(record['failure'])
    return record
