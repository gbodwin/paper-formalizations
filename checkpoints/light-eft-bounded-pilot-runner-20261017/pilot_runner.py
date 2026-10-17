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
LOCK=Path('/tmp/distance-sparsification-single-compiler.lock')
TOOL=Path('/workspace/toolchains/lean-4.34.0-linux')
LEAN=TOOL/'bin/lean'
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
PACKAGES=Path('/workspace/paper-formalizations/.lake/packages')
PILOT=REPO/'.lake/bounded-import-20261017-5ba09dcb949541f29eb286e312c9f8ea'
EVIDENCE=REPO/'.lake/bounded-import-evidence-20261017-5ba09dcb949541f29eb286e312c9f8ea'
BODY=b'import Aesop.Script.Tactic\n'
MAP=REPO/'checkpoints/light-eft-provenance-fixes-20261017/evidence/dependency-map.json'
MAP_SHA='7c5150b666457ce16e835cdb2b5044ea8d2a29f005d05a79d5cbaf772af540b5'
INTERVAL=.25
DEADLINE=90.0
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir')

def digest(path):
    path=Path(path)
    if path.is_symlink() or not path.is_file():raise RuntimeError('Not a regular input: '+str(path))
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
    with os.fdopen(fd,'rb') as f:
        before=os.fstat(f.fileno());h=hashlib.file_digest(f,'sha256').hexdigest();after=os.fstat(f.fileno())
    signature=lambda s:(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
    if signature(before)!=signature(after):raise RuntimeError('Input changed during hashing')
    return {'path':str(path),'sha256':h,'bytes':after.st_size,'identity':list(signature(after))}

def dep_roots():
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    if digest(MAP)['sha256']!=MAP_SHA:raise RuntimeError('Frozen dependency map changed')
    used={row['package'] for row in json.loads(MAP.read_text())['modules']}
    return [PACKAGES/p['name']/'.lake/build/lib/lean' for p in pins if p['name'] in used]+[TOOL/'lib/lean']

def environment():
    pins=json.loads((REPO/'lake-manifest.json').read_text())['packages']
    return {'LANG':'C.UTF-8','LC_ALL':'C.UTF-8','LEAN_SYSROOT':str(TOOL),
        'LEAN_PATH':os.pathsep.join(map(str,dep_roots())),
        'LEAN_SRC_PATH':os.pathsep.join([str(PACKAGES/p['name']) for p in pins]+[str(TOOL/'src/lean')])}

def production_inputs(source):
    files={source,MAP,LEAN,Path(sys.executable).resolve(),HERE/'pilot_runner.py',HERE/'pilot_child.py',HERE/'pilot_accounting.py',REPO/'scripts/LightEFTProcessLifecycle.py',REPO/'lake-manifest.json',REPO/'lean-toolchain'}
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

def validate_plan(plan):
    expected=[str(LEAN),'-j1','-M512','-DautoImplicit=false','-DwarningAsError=true',str(PILOT/'ImportSmoke.lean')]
    if plan['argv']!=expected or plan['env']!=environment() or plan['cwd']!=str(PILOT):raise RuntimeError('Not the exact production pilot')
    if plan['source']!=str(PILOT/'ImportSmoke.lean') or Path(plan['source']).read_bytes()!=BODY:raise RuntimeError('Wrong smoke source')
    if digest(LEAN)['sha256']!=LEAN_SHA:raise RuntimeError('Official Lean executable hash mismatch')
    expected_inputs=list(map(str,production_inputs(Path(plan['source']))))
    if plan['inputs'] is None:plan['inputs']=expected_inputs
    elif plan['inputs']!=expected_inputs:raise RuntimeError('Incomplete input inventory')

def child_status(pid):
    fields=Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()
    raw=Path(f'/proc/{pid}/status').read_text()
    values={k:int(v.split()[0])*1024 for line in raw.splitlines() if ':' in line for k,v in [line.split(':',1)] if k in ('VmRSS','VmSize')}
    return dict(pid=pid,ppid=int(fields[1]),pgid=int(fields[2]),sid=int(fields[3]),start_ticks=int(fields[19]),state=fields[0],rss=values.get('VmRSS',0),vm=values.get('VmSize',0))

def check_memory(now,baseline,minimum):
    if now['headroom']<minimum:raise RuntimeError('Visible headroom below required floor')
    for a,b in zip(now['nodes'],baseline['nodes'],strict=True):
        if a['path']!=b['path'] or a['limit']!=b['limit']:raise RuntimeError('Accounting limit changed')
        if any(a['oom'][k]!=b['oom'][k] for k in b['oom']):raise RuntimeError('OOM counters changed')

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
    record={'attempt_id':uuid.uuid4().hex,'scope':'BOUNDED_IMPORT_ONLY_NOT_PROOF_RECHECK','source_commit':SOURCE,'argv':plan['argv'],'environment':plan['env'],'state':'created','started_ns':time.monotonic_ns(),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'supervisor_pid':os.getpid()}
    evidence.mkdir(exist_ok=False,parents=True)
    child=None;old=None;handlers={};fds=[];before=[]
    accounting=VisibleAccounting() if accounting is None else accounting
    def save():
        t=evidence/'receipt.tmp'
        with t.open('w') as f:
            f.write(json.dumps(record,indent=2)+'\n');f.flush();os.fsync(f.fileno())
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
            before=[digest(p) for p in plan['inputs']]
            (evidence/'inputs-before.json').write_text(json.dumps(before,indent=2)+'\n')
            (evidence/'submitted-source.txt').write_bytes(Path(plan['source']).read_bytes())
            record['inputs_manifest_sha256']=digest(evidence/'inputs-before.json')['sha256'];save()
            # Admission is AFTER all streaming hashing and source/pin checks.
            baseline=accounting.sample();record['admission']=baseline
            check_memory(baseline,baseline,2*1024**3)
            if baseline['system_available']<2*1024**3 or shutil.disk_usage(pilot).free<=2*1024**3:raise RuntimeError('Insufficient memory/disk')
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
                        now=accounting.sample();check_memory(now,baseline,512*1024**2)
                        rows=life.descendants()
                        if any(row['pid']!=child.pid for row in rows):record['unexpected_descendants']=rows;raise RuntimeError('Unexpected process descendant')
                        current=child_status(child.pid)
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
                                    record['handshake']=packet;record['preexec_verified_ns']=time.monotonic_ns();save()
                                    os.write(ack_w,b'G');os.close(ack_w);fds.remove(ack_w);approved=True;record['state']='exec-authorized'
                                elif not chunk:raise RuntimeError('Launcher exited without handshake')
                        if owned_wait4(child,record):
                            if not approved or child.returncode!=0:raise RuntimeError('Child failed before/after exec')
                            break
                        time.sleep(INTERVAL)
        except BaseException as exc:
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
                            after=[digest(x['path']) for x in before]
                            (evidence/'inputs-after.json').write_text(json.dumps(after,indent=2)+'\n')
                            if before!=after:raise RuntimeError('Preserved input changed')
                            validate_plan(plan)  # Recheck search tree membership and pins as well as bytes.
                            record['preserved_inputs_verified']=True
                        except BaseException as e:record.setdefault('failure',repr(e));record['preserved_inputs_verified']=False
                    if old is not None:life.retry_locked('restore-subreaper',lambda:life.set_subreaper(old),record,save)
                    record.update(ended_ns=time.monotonic_ns(),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),state='failed' if 'failure' in record else 'finished')
                    life.retry_locked('finalize',save,record,save)
                    for sig,handler in handlers.items():life.retry_locked('restore-signals',lambda sig=sig,handler=handler:signal.signal(sig,handler),record,save)
                    break
                except BaseException as e:life.cleanup_error('pilot-finalization-barrier',e,record,save)
    if 'failure' in record:raise RuntimeError(record['failure'])
    return record

def run_once():
    """Not invoked in preparation. Fixed fresh paths enforce one attempt, no retry."""
    if PILOT.exists() or EVIDENCE.exists():raise FileExistsError('Pilot/evidence collision; never retry or reuse')
    PILOT.mkdir(parents=True,exist_ok=False)
    source=PILOT/'ImportSmoke.lean';source.write_bytes(BODY)
    plan={'source':str(source),'argv':[str(LEAN),'-j1','-M512','-DautoImplicit=false','-DwarningAsError=true',str(source)],'env':environment(),'cwd':str(PILOT),'inputs':None}
    return _run(plan,PILOT,EVIDENCE)

if __name__=='__main__':raise SystemExit('Preparation only: no command-line execution authorized. Independent implementation review required.')
