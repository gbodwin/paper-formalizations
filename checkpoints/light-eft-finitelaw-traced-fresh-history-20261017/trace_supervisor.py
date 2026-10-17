"""One bounded tracer/Lean pair, with actual tracee limit verification and fail-stop cleanup."""
from pathlib import Path
import datetime,hashlib,json,os,resource,select,shutil,signal,subprocess,sys,time,uuid,fcntl
import pilot_runner as p
import integrated_housekeeping as housekeeping
life=p.life
TRACER_AS=256*1024**2
TRACE_BOUND=16*1024**2
MAP_BOUND=4*1024**2
SYSCALLS='open,openat,openat2,stat,lstat,fstat,newfstatat,statx,mmap,mremap,munmap,mprotect,brk,lseek,read,pread64,readv,preadv,preadv2,close,clone,clone3,fork,vfork,execve,exit,exit_group,setsid'
RAW_READS='read,pread64,readv,preadv,preadv2'

def tracer_argv(tracefile,cfg,ready,ack,lockfd):
    return [str(p.TRACER),'-f','-q','-ttt','-T','-v','-yy','-s','4096','-e','trace='+SYSCALLS,'-e','raw='+RAW_READS,'-o',str(tracefile),sys.executable,'-I',str(p.HERE/'pilot_child.py'),str(cfg),str(ready),str(ack),str(lockfd)]

def verify_actual(packet,tracer,lockfd,candidate):
    if 'error' in packet:raise RuntimeError('Tracee launch setup failed: '+packet['error'])
    pid=packet['pid'];current=p.child_status(pid);st=os.fstat(lockfd)
    if candidate is not None and (pid,current['start_ticks'])!=(candidate['pid'],candidate['start_ticks']):raise RuntimeError('Tracee candidate identity changed')
    if packet['ppid']!=tracer.pid or current['ppid']!=tracer.pid:raise RuntimeError('Actual tracee is not the identified tracer child')
    if any(packet[k]!=pid or current[k]!=pid for k in ('sid','pgid')):raise RuntimeError('Tracee lacks own session/group')
    if packet['limits']!={k:[v,v] for k,v in p.LIMITS.items()}:raise RuntimeError('Actual tracee handshake limits differ')
    for name,value in p.LIMITS.items():
        if resource.prlimit(pid,getattr(resource,name))!=(value,value):raise RuntimeError('Actual tracee kernel limit mismatch')
    fields=dict(line.split(':',1) for line in Path(f'/proc/{pid}/status').read_text().splitlines() if ':' in line)
    if int(fields['TracerPid'])!=tracer.pid:raise RuntimeError('Actual tracee is not traced by pinned tracer PID')
    inherited=os.stat(f'/proc/{pid}/fd/{lockfd}')
    if packet['lock_fd']!=lockfd or not packet['lock_inheritable'] or [packet['lock_device'],packet['lock_inode']]!=[st.st_dev,st.st_ino] or (inherited.st_dev,inherited.st_ino)!=(st.st_dev,st.st_ino):raise RuntimeError('Actual tracee inherited lock mismatch')
    return current

def sample_maps(pid,evidence):
    target=evidence/'map-samples.jsonl';size=target.stat().st_size if target.exists() else 0
    if size>=MAP_BOUND-1024:return
    row={'monotonic_ns':time.monotonic_ns(),'pid':pid}
    try:
        with open(f'/proc/{pid}/maps') as f:content=f.read(1024**2+1)
        row.update(maps=content[:1024**2],truncated=len(content)>1024**2)
    except OSError as exc:row['read_error']=repr(exc)
    encoded=(json.dumps(row)+'\n').encode()
    if size+len(encoded)>MAP_BOUND:return
    with target.open('ab') as f:f.write(encoded)

def run(plan,evidence):
    r={'attempt_id':uuid.uuid4().hex,'scope':'ONE_TRACED_FINITE_LAW_COMPILE_ONLY','source_commit':p.SOURCE,'argv':plan['argv'],'environment':plan['env'],'stage':'compile','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'started_ns':time.monotonic_ns(),'supervisor_pid':os.getpid(),'state':'created','tracer_sha256':p.TRACER_SHA,'tracer_bootstrap_limits':p.LIMITS,'tracer_postfork_as_bytes':TRACER_AS,'trace_bound_bytes':TRACE_BOUND,'maps_bound_bytes':MAP_BOUND}
    evidence.mkdir(parents=True,exist_ok=False);child=None;actual=None;candidate=None;before=[];old=None;fds=[];handlers={};accounting=p.VisibleAccounting()
    def save():
        temp=evidence/'receipt.tmp'
        with temp.open('w') as f:json.dump(r,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        temp.replace(evidence/'receipt.json')
        fd=os.open(evidence,os.O_RDONLY|os.O_DIRECTORY)
        try:os.fsync(fd)
        finally:os.close(fd)
    save()
    with p.LOCK.open('r+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(lock.fileno())
        if (st.st_dev,st.st_ino)!=(33,3849):raise RuntimeError('Common lock identity changed')
        r['lock']={'path':str(p.LOCK),'device':st.st_dev,'inode':st.st_ino,'fd':lock.fileno(),'acquired_ns':time.monotonic_ns()};save()
        try:
            for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP):
                handlers[sig]=signal.getsignal(sig)
                def interrupted(s,f):raise InterruptedError('supervisor signal '+str(s))
                signal.signal(sig,interrupted)
            if life.descendants():raise RuntimeError('Preexisting supervisor children')
            p.validate_plan(plan)
            if p.object_inventory():raise RuntimeError('Trace compile output root not initially empty')
            prior=p.load_inventory()
            before=[p.digest(x,expected=prior.get(str(x)) if str(x).startswith(str(p.PACKAGES)+'/') else None,advice_log=evidence/'hash-advice-before.jsonl') for x in plan['inputs']]
            del prior;r['prior_inventory_dictionary_released']=True
            (evidence/'submitted-source.txt').write_bytes(Path(plan['source']).read_bytes());r['submitted_source_sha256']=p.digest(Path(plan['source']))['sha256']
            def gate(now):
                p.check_memory(now,now,4026531840)
                if now['system_available']<4026531840 or shutil.disk_usage(p.PILOT).free<=2*1024**3:raise RuntimeError('Insufficient host memory/disk')
            baseline=housekeeping.admit_after_preflight(evidence,before,'compile',lock.fileno(),accounting,r,save,gate)
            processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True);r['processes_before']=processes
            if any(row.split()[-1] in ('lean','lake','leanchecker','leantar','strace') and not row.split()[2].startswith('Z') for row in processes.splitlines()[1:]):raise RuntimeError('Another compiler/checker/tracer active')
            old=life.set_subreaper(True)
            if life.descendants():raise RuntimeError('Unexpected child before spawn')
            cfg_r,cfg_w=os.pipe();ready_r,ready_w=os.pipe();ack_r,ack_w=os.pipe();fds=[cfg_r,cfg_w,ready_r,ready_w,ack_r,ack_w]
            config=json.dumps({'argv':plan['argv'],'env':plan['env']}).encode()
            if len(config)>4096:raise RuntimeError('Launcher config too long')
            os.write(cfg_w,config);os.close(cfg_w);fds.remove(cfg_w)
            command=tracer_argv(evidence/'syscalls.trace',cfg_r,ready_w,ack_r,lock.fileno());r['tracer_argv']=command;r['deadline_seconds']=p.DEADLINE;save()
            def bootstrap():
                signal.pthread_sigmask(signal.SIG_SETMASK,blocked)
                for name,value in p.LIMITS.items():resource.setrlimit(getattr(resource,name),(value,value))
            began=time.monotonic()
            with (evidence/'raw.log').open('xb') as log:
                blocked=signal.pthread_sigmask(signal.SIG_BLOCK,set(handlers))
                try:child=subprocess.Popen(command,cwd=p.PILOT,env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},stdout=log,stderr=subprocess.STDOUT,pass_fds=(cfg_r,ready_w,ack_r,lock.fileno()),start_new_session=True,preexec_fn=bootstrap)
                finally:signal.pthread_sigmask(signal.SIG_SETMASK,blocked)
                for fd in (cfg_r,ready_w,ack_r):os.close(fd);fds.remove(fd)
                first=p.child_status(child.pid);r.update(tracer_pid=child.pid,child_pid=child.pid,tracer_first_identity=first,state='tracee-handshake-wait');save()
                approved=False;buffer=b'';peaks={'tracer_rss':0,'tracer_vm':0,'lean_rss':0,'lean_vm':0,'combined_rss':0}
                with (evidence/'samples.jsonl').open('x') as samples:
                    while True:
                        now=accounting.sample();p.check_memory(now,baseline,512*1024**2)
                        rows=life.descendants();others=[row for row in rows if row['pid']!=child.pid]
                        if candidate is None:
                            if len(others)>1 or any(row['ppid']!=child.pid for row in others):raise RuntimeError('Unexpected descendants before actual PID identification')
                            if others:candidate=p.child_status(others[0]['pid']);r['tracee_candidate']=candidate;save()
                        elif any((row['pid'],row['start_ticks'])!=(candidate['pid'],candidate['start_ticks']) for row in others):raise RuntimeError('Descendant outside fixed tracer/tracee pair')
                        current=p.child_status(child.pid)
                        if current['start_ticks']!=first['start_ticks'] or current['ppid']!=os.getpid() or current['sid']!=child.pid or current['pgid']!=child.pid:raise RuntimeError('Tracer identity/session changed')
                        if current['state']!='Z':
                            inherited=os.stat(f'/proc/{child.pid}/fd/{lock.fileno()}')
                            if (inherited.st_dev,inherited.st_ino)!=(st.st_dev,st.st_ino):raise RuntimeError('Tracer lock descriptor changed')
                        tracee=None
                        if candidate is not None:
                            try:tracee=p.child_status(candidate['pid'])
                            except (FileNotFoundError,ProcessLookupError):pass
                            if tracee is not None:
                                if tracee['start_ticks']!=candidate['start_ticks'] or tracee['ppid']!=child.pid:raise RuntimeError('Actual tracee identity/parent changed')
                                if approved and (tracee['sid']!=tracee['pid'] or tracee['pgid']!=tracee['pid']):raise RuntimeError('Actual Lean session changed')
                                if tracee['state']!='Z':
                                    if approved:
                                        try:
                                            inherited=os.stat(f"/proc/{tracee['pid']}/fd/{lock.fileno()}")
                                            if (inherited.st_dev,inherited.st_ino)!=(st.st_dev,st.st_ino):raise RuntimeError('Actual Lean lock descriptor changed')
                                        except (FileNotFoundError,ProcessLookupError):
                                            try:
                                                if p.child_status(tracee['pid'])['state']!='Z':raise RuntimeError('Actual Lean lock vanished while live')
                                            except (FileNotFoundError,ProcessLookupError):pass
                                    sample_maps(tracee['pid'],evidence)
                        peaks['tracer_rss']=max(peaks['tracer_rss'],current['rss']);peaks['tracer_vm']=max(peaks['tracer_vm'],current['vm'])
                        if tracee is not None:
                            peaks['lean_rss']=max(peaks['lean_rss'],tracee['rss']);peaks['lean_vm']=max(peaks['lean_vm'],tracee['vm'])
                        peaks['combined_rss']=max(peaks['combined_rss'],current['rss']+(tracee['rss'] if tracee else 0));r['sampled_peaks_bytes']=peaks.copy()
                        samples.write(json.dumps({'monotonic_ns':time.monotonic_ns(),'tracer':current,'tracee':tracee,'nodes':now['nodes'],'headroom':now['headroom']})+'\n');samples.flush()
                        trace=evidence/'syscalls.trace'
                        if trace.exists() and trace.stat().st_size>=TRACE_BOUND:raise RuntimeError('Trace output reached fixed bound')
                        if approved and current['vm']>TRACER_AS:raise RuntimeError('Tracer exceeded verified address budget')
                        if time.monotonic()-began>=p.DEADLINE:raise TimeoutError('Traced pair wall deadline')
                        if not approved:
                            ready,_,_=select.select([ready_r],[],[],0)
                            if ready:
                                chunk=os.read(ready_r,8192);buffer+=chunk
                                if len(buffer)>8192:raise RuntimeError('Oversized actual tracee handshake')
                                if b'\n' in buffer:
                                    packet=json.loads(buffer);actual=verify_actual(packet,child,lock.fileno(),candidate)
                                    if candidate is None:candidate=actual
                                    r.update(actual_lean_pid=actual['pid'],actual_lean_identity=actual,handshake=packet,actual_tracee_limits_verified_ns=time.monotonic_ns())
                                    initial={name:list(resource.prlimit(child.pid,getattr(resource,name))) for name in p.LIMITS}
                                    if initial!={name:[v,v] for name,v in p.LIMITS.items()}:raise RuntimeError('Tracer bootstrap kernel limits differ')
                                    r['tracer_bootstrap_kernel_limits']=initial
                                    resource.prlimit(child.pid,resource.RLIMIT_AS,(TRACER_AS,TRACER_AS))
                                    reduced={name:list(resource.prlimit(child.pid,getattr(resource,name))) for name in p.LIMITS}
                                    expected={name:[TRACER_AS,TRACER_AS] if name=='RLIMIT_AS' else [v,v] for name,v in p.LIMITS.items()}
                                    if reduced!=expected:raise RuntimeError('Tracer reduced kernel limits differ')
                                    r['tracer_postfork_kernel_limits']=reduced
                                    fresh=accounting.sample();p.check_memory(fresh,baseline,4026531840)
                                    if fresh['system_available']<4026531840:raise RuntimeError('Fresh pre-exec host headroom failed')
                                    r['preexec_admission']=fresh;r['preexec_verified_ns']=time.monotonic_ns();save()
                                    os.write(ack_w,b'G');os.close(ack_w);fds.remove(ack_w);approved=True;r['state']='actual-lean-exec-authorized'
                                elif not chunk:raise RuntimeError('Tracee exited without handshake')
                        if p.owned_wait4(child,r):
                            r['tracer_direct_reaped']=True
                            if not approved:raise RuntimeError('Tracer ended before actual Lean authorization')
                            if child.returncode!=0:raise RuntimeError('Traced compiler/tracer exited nonzero')
                            break
                        time.sleep(p.INTERVAL)
        except BaseException as exc:r['failure']=repr(exc)
        finally:
            while True:
                try:
                    for sig in handlers:life.retry_locked('ignore-cleanup-signal',lambda sig=sig:signal.signal(sig,signal.SIG_IGN),r,save)
                    for fd in fds:
                        try:os.close(fd)
                        except OSError:pass
                    fds=[]
                    if child is not None:
                        # Stop the actual Lean group first on interruption, then reap tracer and adoptees.
                        if child.returncode is None and candidate is not None:
                            try:
                                status=p.child_status(candidate['pid'])
                                if status['start_ticks']==candidate['start_ticks'] and status['pgid']==candidate['pid']:os.killpg(candidate['pid'],signal.SIGTERM)
                            except (FileNotFoundError,ProcessLookupError):pass
                        life.retry_locked('tracer-owned-wait4',lambda:p.reap_direct(child,r,save),r,save);r['tracer_direct_reaped']=True
                        life.cleanup(child,r,save)
                        allowed={child.pid,candidate['pid'] if candidate else None}
                        if any(row['pid'] not in allowed for row in r.get('descendants_observed',[])):r.setdefault('failure','Unexpected extra cleanup descendant')
                    else:
                        if life.descendants():raise RuntimeError('Unexpected child before tracer spawn')
                        try:os.waitpid(-1,os.WNOHANG)
                        except ChildProcessError:r['kernel_no_children_verified']=True
                        else:raise RuntimeError('Kernel child remains')
                    if before:
                        try:
                            after=[p.digest(row['path'],expected=row,advice_log=evidence/'hash-advice-after.jsonl') for row in before]
                            housekeeping.write_inventory(after,evidence/'inputs-after.json',r,save);housekeeping.complete_one(evidence/'hash-advice-after.jsonl',r,save)
                            if before!=after:raise RuntimeError('Preserved input changed')
                            p.validate_plan(plan);r['preserved_inputs_verified']=True
                        except BaseException as exc:r.setdefault('failure',repr(exc));r['preserved_inputs_verified']=False
                    try:
                        for name in ['hash-advice-before.jsonl','inputs-before.json','hash-advice-after.jsonl','inputs-after.json','raw.log','samples.jsonl','syscalls.trace','map-samples.jsonl']:
                            path=evidence/name
                            if path.exists():housekeeping.complete_one(path,r,save)
                    except BaseException as exc:r.setdefault('failure',repr(exc));r['completed_file_housekeeping_error']=repr(exc)
                    r['output_inventory_after']=p.object_inventory()
                    if old is not None:life.retry_locked('restore-subreaper',lambda:life.set_subreaper(old),r,save)
                    r.update(ended_ns=time.monotonic_ns(),ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),state='failed' if 'failure' in r else 'finished')
                    life.retry_locked('finalize',save,r,save)
                    for sig,handler in handlers.items():life.retry_locked('restore-signals',lambda sig=sig,handler=handler:signal.signal(sig,handler),r,save)
                    break
                except BaseException as exc:life.cleanup_error('traced-finalization-barrier',exc,r,save)
    if 'failure' in r:raise RuntimeError(r['failure'])
    return r
