"""One bounded import attempt. No command-line execution entry point.
Production run_once is for subsequent reviewed authorization only; tests patch
validate_plan to permit harmless Python, never a replacement Lean executable.
"""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,resource,select,shutil,signal,subprocess,sys,time,uuid
HERE=Path(__file__).resolve().parent
REPO=HERE.parent.parent
sys.path.insert(0,str(REPO/'scripts'))
import LightEFTProcessLifecycle as life
from pilot_accounting import VisibleAccounting
from pilot_child import LIMITS
import integrated_housekeeping as housekeeping
ADMISSION_HEADROOM=3758096384
STOP_HEADROOM=1073741824
RSS_STOP=2147483648

class MemoryGuardError(RuntimeError):pass
LOCK=Path('/tmp/distance-sparsification-single-compiler.lock')
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux')
LEAN=TOOL/'bin/lean'
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
PACKAGES=Path('/workspace/paper-formalizations/.lake/packages')
PILOT=REPO/'.lake/finitelaw-bounded-chain-20261017-ee73db0a907a4ca0b183ed0fcd5c95c6'
EVIDENCE=HERE/'evidence'
OUT=PILOT/'objects'
MODULE='LightEFTSpanners.FiniteLaw'
MODULE_ROOT=REPO/'Light Edge Fault Tolerant Graph Spanners'
PROJECT_SOURCE=MODULE_ROOT/'LightEFTSpanners/FiniteLaw.lean'
PROJECT_SHA='7c7f5ded9abec4a60ee9dfe5fa36c100e4bce0bfef26c474a98bbd6c5c6cc240'
RESOLVER=REPO/'scripts/LightEFTResolveCheckerTarget.lean'
RESOLVER_SHA='9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf'
CHECKER=TOOL/'bin/leanchecker'
CHECKER_SHA='ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'
OBJECT=OUT/'LightEFTSpanners/FiniteLaw.olean'
RESOLUTION=PILOT/'resolution.json'
MAP=REPO/'checkpoints/light-eft-provenance-fixes-20261017/evidence/dependency-map.json'
MAP_SHA='7c5150b666457ce16e835cdb2b5044ea8d2a29f005d05a79d5cbaf772af540b5'
INTERVAL=.25
DEADLINE=90.0
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir')

from pilot_cache_advice import hash_input, load_inventory

def digest(path,expected=None,advice_log=None):
    return hash_input(path,expected,advice_log)

def dep_roots():
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    if digest(MAP)['sha256']!=MAP_SHA:raise RuntimeError('Frozen dependency map changed')
    used={row['package'] for row in json.loads(MAP.read_text())['modules']}
    return [PACKAGES/p['name']/'.lake/build/lib/lean' for p in pins if p['name'] in used]+[TOOL/'lib/lean']

def environment(stage):
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_SYSROOT':str(TOOL),
        'LEAN_PATH':os.pathsep.join(map(str,[OUT]+dep_roots())),
        'LEAN_SRC_PATH':os.pathsep.join([str(MODULE_ROOT)]+[str(PACKAGES/p['name']) for p in pins]+[str(TOOL/'src/lean')])}
    env['MIMALLOC_ARENA_RESERVE']='128MiB'
    if stage=='compile':env['MIMALLOC_VERBOSE']='1'
    if stage=='resolve':env.update(LIGHTEFT_CHECKER_TARGET=MODULE,LIGHTEFT_CHECKER_RESOLUTION_FILE=str(RESOLUTION))
    if stage=='replay':env.update(LEAN_NUM_THREADS='1',LEAN_STACK_SIZE_KB='65536')
    return env

def production_inputs(source):
    files={source,MAP,LEAN,Path(sys.executable).resolve(),HERE/'pilot_runner.py',HERE/'pilot_child.py',HERE/'pilot_accounting.py',HERE/'pilot_cache_advice.py',HERE/'chain.py',HERE/'pid_observations.py',HERE/'integrated_housekeeping.py',HERE/'history-whitelist.json',PROJECT_SOURCE,RESOLVER,CHECKER,REPO/'scripts/LightEFTProcessLifecycle.py',REPO/'lake-manifest.json',REPO/'lean-toolchain'}
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    for p in pins:
        base=PACKAGES/p['name']
        # Read-only git inspection; this completes before the supervised child.
        if subprocess.check_output(['git','rev-parse','HEAD'],cwd=base,text=True).strip()!=p['rev']:raise RuntimeError('Package pin drift')
        if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=base):raise RuntimeError('Package source drift')
        files.update(base.rglob('*.lean'))
    for root in dep_roots():
        if not root.is_dir() or root.is_symlink():raise RuntimeError('Missing/symlink dependency root')
        for p in root.rglob('*'):
            if p.is_symlink():raise RuntimeError('Symlink in dependency search tree')
            if p.is_file() and (str(p).endswith(SUFFIXES) or '.so' in p.name):
                if p.relative_to(root).parts[0].split('.')[0] in ('LightEFTSpanners','LightSpanners'):raise RuntimeError('Inherited project object')
                files.add(p)
    return sorted(files)

def object_inventory():
    return [digest(p) for p in sorted(OUT.rglob('*')) if p.is_file()]

def stage_argv(stage):
    flags=['-j1','-s65536','-M1536','-DautoImplicit=false','-DwarningAsError=true']
    if stage=='compile':return [str(LEAN),*flags,'--root='+str(MODULE_ROOT),'-o',str(OBJECT),str(PROJECT_SOURCE)]
    if stage=='resolve':return [str(LEAN),*flags,str(RESOLVER)]
    if stage=='replay':return [str(CHECKER),'-v',MODULE]
    raise ValueError('No other stage authorized')

def verify_resolution():
    data=json.loads(RESOLUTION.read_text())
    if data['target']!=MODULE or data['count']!=1 or data['resolved']!=[{'module':MODULE,'object':str(OBJECT)}]:raise RuntimeError('Official resolution not exact singleton/new object')
    found=[]
    for root in [OUT]+dep_roots():
        for path in root.rglob('*.olean'):
            name='.'.join(path.relative_to(root).with_suffix('').parts)
            if name==MODULE or name.startswith(MODULE+'.'):found.append((name,str(path)))
    if found!=[(MODULE,str(OBJECT))]:raise RuntimeError('Missing/shadowed/prefix-expanded checker object')
    return data

def validate_plan(plan):
    stage=plan['stage']
    source=RESOLVER if stage=='resolve' else PROJECT_SOURCE
    if plan['argv']!=stage_argv(stage) or plan['env']!=environment(stage) or plan['cwd']!=str(PILOT) or plan['source']!=str(source):raise RuntimeError('Not the exact finite authorized stage')
    for path,expected in [(LEAN,LEAN_SHA),(CHECKER,CHECKER_SHA),(PROJECT_SOURCE,PROJECT_SHA),(RESOLVER,RESOLVER_SHA)]:
        if digest(path)['sha256']!=expected:raise RuntimeError('Pinned source/executable/harness drift: '+str(path))
    expected_inputs=production_inputs(source)
    if stage!='compile':
        if object_inventory()!=plan['object_bindings']:raise RuntimeError('Fresh output inventory changed')
        if not OBJECT.is_file():raise RuntimeError('No fresh target object')
        expected_inputs += [Path(r['path']) for r in plan['object_bindings']]
    if stage=='replay':
        verify_resolution();expected_inputs.append(RESOLUTION)
    expected_inputs=list(map(str,sorted(set(expected_inputs))))
    if plan['inputs'] is None:plan['inputs']=expected_inputs
    elif plan['inputs']!=expected_inputs:raise RuntimeError('Incomplete input inventory')

def parse_child_status(pid,stat_text,status_text):
    fields=stat_text.rsplit(')',1)[1].split()
    statuses={line.split(':',1)[0]:line.split(':',1)[1] for line in status_text.splitlines() if ':' in line}
    state=statuses.get('State',fields[0]).strip().split()[0]
    values={key:int(statuses[key].split()[0])*1024 for key in ('VmRSS','VmSize') if key in statuses}
    if state not in ('Z','X') and any(key not in values for key in ('VmRSS','VmSize')):raise MemoryGuardError('Missing live RSS/VM sample')
    return dict(pid=pid,ppid=int(fields[1]),pgid=int(fields[2]),sid=int(fields[3]),start_ticks=int(fields[19]),state=state,rss=values.get('VmRSS',0),vm=values.get('VmSize',0))

def child_status(pid):
    return parse_child_status(pid,Path(f'/proc/{pid}/stat').read_text(),Path(f'/proc/{pid}/status').read_text())

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

def enforce_host_stop(now):
    if now['system_available']<STOP_HEADROOM:raise MemoryGuardError('Host MemAvailable below 1 GiB stop floor')

def enforce_rss_stop(current):
    if current['state'] not in ('Z','X') and current['rss']>=RSS_STOP:raise MemoryGuardError('Observed live RSS reached 2 GiB stop')

def runtime_sample(child,baseline,accounting,record,save):
    try:
        now=accounting.sample();check_memory(now,baseline,STOP_HEADROOM);enforce_host_stop(now)
        current=child_status(child.pid);enforce_rss_stop(current)
        return now,current
    except Exception as exc:
        kill_memory_group(child,record,save,repr(exc));raise

def check_memory(now,baseline,minimum):
    if now['headroom']<minimum:raise MemoryGuardError('Visible headroom below required floor')
    for a,b in zip(now['nodes'],baseline['nodes'],strict=True):
        if a['path']!=b['path'] or a['limit']!=b['limit']:raise RuntimeError('Accounting limit changed')
        if any(a['oom'][k]!=b['oom'][k] for k in b['oom']):raise MemoryGuardError('OOM counters changed')
        if a['pids_max']!=b['pids_max'] or a['pids_events']!=b['pids_events']:raise RuntimeError('PID limit/events changed')
        if a['pids_max']!='max' and a['pids_current']>=int(a['pids_max']):raise RuntimeError('Visible PID limit exhausted')

def verify_ready(packet,child,lockfd,first):
    if 'error' in packet:raise RuntimeError('Child limit setup/readback failure: '+packet['error'])
    st=os.fstat(lockfd)
    expected={k:[v,v] for k,v in LIMITS.items()}
    if packet['limits']!=expected:raise RuntimeError('Child limit readback mismatch')
    for name,value in LIMITS.items():
        if resource.prlimit(child.pid,getattr(resource,name))!=(value,value):raise RuntimeError('Kernel limit readback mismatch')
    current=child_status(child.pid)
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

def reap_direct(child,record,save):
    began=time.monotonic()
    while not owned_wait4(child,record):
        sig=signal.SIGTERM if time.monotonic()-began<1 else signal.SIGKILL
        try:os.kill(child.pid,sig)
        except ProcessLookupError:pass
        time.sleep(.02)

def _run(plan,pilot,evidence,accounting=None):
    """Private testable supervisor. Production uses run_once with fixed paths/plan."""
    record={'attempt_id':uuid.uuid4().hex,'scope':'BOUNDED_FINITE_LAW_CHAIN_NOT_FULL_CLEAN','stage':plan['stage'],'source_commit':SOURCE,'argv':plan['argv'],'environment':plan['env'],'memory_policy':{'as_bytes':LIMITS['RLIMIT_AS'],'admission_visible_host_bytes':ADMISSION_HEADROOM,'stop_visible_host_bytes':STOP_HEADROOM,'rss_observed_stop_bytes':RSS_STOP,'sample_seconds':INTERVAL,'immediate_group_signal':'SIGKILL','M_qualification':'Intermittent runtime RSS check, not a kernel heap cap'},'state':'created','started_ns':time.monotonic_ns(),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'supervisor_pid':os.getpid()}
    evidence.mkdir(exist_ok=False,parents=True)
    child=None;old=None;handlers={};fds=[];before=[]
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
    with LOCK.open('r+') as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            record.update(state='refused-lock',failure='Universal lock busy; no child spawned');save();raise
        st=os.fstat(lock.fileno());record['lock']={'path':str(LOCK),'device':st.st_dev,'inode':st.st_ino,'fd':lock.fileno(),'acquired_ns':time.monotonic_ns()};save()
        try:
            for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP):
                handlers[sig]=signal.getsignal(sig)
                def interrupted(s,f):raise InterruptedError('supervisor signal '+str(s))
                signal.signal(sig,interrupted)
            if life.descendants():raise RuntimeError('Preexisting child process')
            validate_plan(plan)
            if plan['stage']=='compile' and object_inventory():raise RuntimeError('Compile output root must initially be empty')
            prior_inventory=load_inventory()
            before=[digest(p,expected=prior_inventory.get(str(p)) if str(p).startswith(str(PACKAGES)+'/') else None,advice_log=evidence/'hash-advice-before.jsonl') for p in plan['inputs']]
            del prior_inventory
            record['prior_inventory_dictionary_released']=True
            (evidence/'submitted-source.txt').write_bytes(Path(plan['source']).read_bytes())
            record['submitted_source_sha256']=digest(Path(plan['source']))['sha256'];record['object_bindings_before']=plan.get('object_bindings',[])
            def admission_gate(now):
                check_memory(now,now,ADMISSION_HEADROOM)
                if now['system_available']<ADMISSION_HEADROOM:raise MemoryGuardError('Host MemAvailable below admission gate')
                if shutil.disk_usage(pilot).free<=2*1024**3:raise RuntimeError('Insufficient disk')
            baseline=housekeeping.admit_after_preflight(evidence,before,plan['stage'],lock.fileno(),accounting,record,save,admission_gate)
            processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True);record['processes_before']=processes
            if any(row.split()[-1] in ('lean','lake','leanchecker','leantar') and not row.split()[2].startswith('Z') for row in processes.splitlines()[1:]):raise RuntimeError('Other compiler/checker/extractor active')
            old=life.set_subreaper(True)
            if life.descendants():raise RuntimeError('Unexpected child before spawn')
            cfg_r,cfg_w=os.pipe();ready_r,ready_w=os.pipe();ack_r,ack_w=os.pipe();fds=[cfg_r,cfg_w,ready_r,ready_w,ack_r,ack_w]
            config=json.dumps({'argv':plan['argv'],'env':plan['env']}).encode()
            if len(config)>4096:raise RuntimeError('Launcher config too long')
            os.write(cfg_w,config);os.close(cfg_w);fds.remove(cfg_w)
            started=time.monotonic();record['deadline_seconds']=DEADLINE
            with (evidence/'raw.log').open('xb') as log:
                blocked=signal.pthread_sigmask(signal.SIG_BLOCK,set(handlers))
                try:
                    child=subprocess.Popen([sys.executable,'-I',str(HERE/'pilot_child.py'),str(cfg_r),str(ready_w),str(ack_r),str(lock.fileno())],cwd=pilot,env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},stdout=log,stderr=subprocess.STDOUT,pass_fds=(cfg_r,ready_w,ack_r,lock.fileno()),start_new_session=True,
                        preexec_fn=lambda:signal.pthread_sigmask(signal.SIG_SETMASK,blocked))
                finally:signal.pthread_sigmask(signal.SIG_SETMASK,blocked)
                for fd in (cfg_r,ready_w,ack_r):os.close(fd);fds.remove(fd)
                first=child_status(child.pid);record.update(child_pid=child.pid,child_identity=first,state='handshake-wait');save()
                buffer=b'';approved=False;peak_rss=peak_vm=0
                with (evidence/'samples.jsonl').open('x') as samples:
                    while True:
                        now,current=runtime_sample(child,baseline,accounting,record,save)
                        rows=life.descendants()
                        if any(row['pid']!=child.pid for row in rows):record['unexpected_descendants']=rows;raise RuntimeError('Unexpected process descendant')
                        if current['start_ticks']!=first['start_ticks'] or current['ppid']!=os.getpid() or current['sid']!=child.pid or current['pgid']!=child.pid:raise RuntimeError('Process identity changed')
                        if current['state']!='Z':
                            inherited=os.stat(f'/proc/{child.pid}/fd/{lock.fileno()}')
                            if (inherited.st_dev,inherited.st_ino)!=(st.st_dev,st.st_ino):raise RuntimeError('Child lock descriptor changed')
                        peak_rss=max(peak_rss,current['rss']);peak_vm=max(peak_vm,current['vm'])
                        samples.write(json.dumps({'monotonic_ns':time.monotonic_ns(),'child':current,'nodes':now['nodes'],'headroom':now['headroom']})+'\n');samples.flush()
                        record.update(sampled_rss_peak_bytes=peak_rss,sampled_vm_peak_bytes=peak_vm,sample_interval_seconds=INTERVAL,vm_peak_qualification='250ms sampled, not a continuous peak')
                        if time.monotonic()-started>=DEADLINE:raise TimeoutError('Child wall deadline')
                        if not approved:
                            readable,_,_=select.select([ready_r],[],[],0)
                            if readable:
                                chunk=os.read(ready_r,8192);buffer+=chunk
                                if len(buffer)>8192:raise RuntimeError('Oversized handshake')
                                if b'\n' in buffer:
                                    packet=json.loads(buffer);verify_ready(packet,child,lock.fileno(),first)
                                    fresh=accounting.sample();check_memory(fresh,baseline,ADMISSION_HEADROOM)
                                    if fresh['system_available']<ADMISSION_HEADROOM:raise MemoryGuardError('Pre-exec MemAvailable below 3.5 GiB')
                                    record['preexec_admission']=fresh
                                    record['handshake']=packet;record['preexec_verified_ns']=time.monotonic_ns();save()
                                    os.write(ack_w,b'G');os.close(ack_w);fds.remove(ack_w);approved=True;record['state']='exec-authorized'
                                elif not chunk:raise RuntimeError('Launcher exited without handshake')
                        if owned_wait4(child,record):
                            if not approved or child.returncode!=0:raise RuntimeError('Child failed before/after exec')
                            break
                        time.sleep(INTERVAL)
        except BaseException as exc:
            if isinstance(exc,MemoryGuardError):kill_memory_group(child,record,save,repr(exc))
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
                    if before:
                        try:
                            after=[digest(x['path'],expected=x,advice_log=evidence/'hash-advice-after.jsonl') for x in before]
                            housekeeping.write_inventory(after,evidence/'inputs-after.json',record,save)
                            housekeeping.complete_one(evidence/'hash-advice-after.jsonl',record,save)
                            if before!=after:raise RuntimeError('Preserved input changed')
                            validate_plan(plan)  # Recheck search tree membership and pins as well as bytes.
                            record['preserved_inputs_verified']=True
                        except BaseException as e:record.setdefault('failure',repr(e));record['preserved_inputs_verified']=False
                    try:
                        for filename in ['hash-advice-before.jsonl','inputs-before.json','hash-advice-after.jsonl','inputs-after.json','raw.log','samples.jsonl']:
                            path=evidence/filename
                            if path.exists():housekeeping.complete_one(path,record,save)
                    except BaseException as exc:
                        record.setdefault('failure',repr(exc));record['completed_file_housekeeping_error']=repr(exc)
                    record['output_inventory_after']=object_inventory()
                    if old is not None:life.retry_locked('restore-subreaper',lambda:life.set_subreaper(old),record,save)
                    record.update(ended_ns=time.monotonic_ns(),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),state='failed' if 'failure' in record else 'finished')
                    life.retry_locked('finalize',save,record,save)
                    for sig,handler in handlers.items():life.retry_locked('restore-signals',lambda sig=sig,handler=handler:signal.signal(sig,handler),record,save)
                    break
                except BaseException as e:life.cleanup_error('pilot-finalization-barrier',e,record,save)
    if 'failure' in record:raise RuntimeError(record['failure'])
    return record

if __name__=='__main__':raise SystemExit('Use the one-shot finite chain entry point; no standalone retries.')
