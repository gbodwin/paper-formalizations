"""External process supervision; does not alter the Lean runtime or toolchain.
All new compiler/checker entry points must use this runner, not historical scripts.
"""
from pathlib import Path
import datetime,fcntl,json,os,signal,subprocess,time,uuid,hashlib,shutil
LOCK=Path('/tmp/distance-sparsification-single-compiler.lock')

def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()

def run_locked(label,argv,cwd,evidence,env=None,submitted_sources=None):
    evidence=Path(evidence);receipts=evidence/'attempts';receipts.mkdir(parents=True,exist_ok=True)
    # Never unlink the lock inode, and never explicitly unlock a shared description:
    # the direct exec child inherits the same open-file description through pass_fds.
    with LOCK.open('a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        attempt=uuid.uuid4().hex
        folder=receipts/attempt;folder.mkdir()
        record={'attempt_id':attempt,'label':label,'argv':list(argv),'cwd':str(cwd),
                'supervisor_pid':os.getpid(),'lock_path':str(LOCK),'lock_fd':lock.fileno(),
                'lock_device':os.fstat(lock.fileno()).st_dev,'lock_inode':os.fstat(lock.fileno()).st_ino,
                'lock_acquired_utc':stamp(),'lock_acquired_monotonic_ns':time.monotonic_ns(),
                'child_pid':None,'exit':None,'state':'lock-held-before-spawn'}
        if Path(argv[0]).name == 'leanchecker':
            if list(argv[1:2]) != ['-v'] or len(argv) != 3:
                raise ValueError('Only one explicit verbose singleton checker target is permitted')
            target = argv[2]
            if target in ['LightEFTSpanners', 'LightSpanners']:
                raise ValueError('Aggregate-prefix replay is forbidden')
            search = [Path(p).resolve() for p in (env or os.environ).get('LEAN_PATH', '').split(os.pathsep) if p]
            matches = set()
            for root in search:
                if not root.is_dir(): continue
                for path in root.rglob('*.olean'):
                    real = path.resolve()
                    for base in search:
                        try: parts = real.relative_to(base).with_suffix('').parts
                        except ValueError: continue
                        module = '.'.join(parts)
                        if module == target or module.startswith(target + '.'):
                            matches.add(module)
                        break
            record['checker_resolution'] = {'target': target, 'actual_modules': sorted(matches),
                'search_path': [str(p) for p in search], 'under_lock': True}
            if matches != {target}:
                raise ValueError('Checker target does not resolve to exactly one actual module: ' + repr(sorted(matches)))
        ps=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
        preflight=dict(attempt_id=attempt,utc=stamp(),processes=ps,
            free_disk=shutil.disk_usage(cwd).free,
            memory_limit=Path('/sys/fs/cgroup/memory.max').read_text(),
            memory_current=Path('/sys/fs/cgroup/memory.current').read_text())
        (folder/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
        record['preflight_sha256']=hashlib.sha256((folder/'preflight.json').read_bytes()).hexdigest()
        with (evidence/'preflights.jsonl').open('a') as f:f.write(json.dumps(preflight)+'\n')
        assert not any(x.split()[-1] in ['lean','lake','leanchecker'] and 'Z' not in x.split()[2] for x in ps.splitlines()[1:])
        assert preflight['free_disk']>2*1024**3
        sources=submitted_sources if submitted_sources is not None else [x for x in argv if str(x).endswith('.lean')]
        if not sources and Path(argv[0]).name=='leanchecker':
            suffix=Path(*argv[-1].split('.')).with_suffix('.lean')
            sources=[p for p in Path(cwd).rglob(suffix.name) if str(p).endswith(str(suffix))]
            if len(sources)!=1:raise ValueError('Provide submitted_sources explicitly for this checker invocation')
        record['submitted_sources']=[]
        for source in sources:
            path=Path(source)
            if not path.is_absolute():path=Path(cwd)/path
            data=path.read_bytes();digest=hashlib.sha256(data).hexdigest()
            (folder/(digest+'.lean')).write_bytes(data)
            record['submitted_sources'].append({'path':str(path),'sha256':digest,'bytes':len(data)})
        if env is not None:record['lean_environment']={k:env[k] for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT'] if k in env}
        def save():
            temp=folder/'receipt.tmp';temp.write_text(json.dumps(record,indent=2)+'\n');os.replace(temp,folder/'receipt.json')
            with (folder/'receipt.json').open() as f:os.fsync(f.fileno())
        save();child=None;old_handlers={}
        def interrupted(sig,frame):raise InterruptedError(f'signal {sig}')
        for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:
            old_handlers[sig]=signal.signal(sig,interrupted)
        try:
            with (folder/'raw.log').open('w') as log:
                # Defer catchable interrupts until the PID is recorded.
                blocked=signal.pthread_sigmask(signal.SIG_BLOCK,set(old_handlers))
                try:
                    record['start_utc']=stamp();record['start_monotonic_ns']=time.monotonic_ns()
                    child=subprocess.Popen(argv,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,
                                           pass_fds=(lock.fileno(),),start_new_session=True,
                                           preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK,blocked))
                    record['child_pid']=child.pid;record['process_group']=child.pid
                    record['state']='running-lock-held';save()
                finally:signal.pthread_sigmask(signal.SIG_SETMASK,blocked)
                record['exit']=child.wait()
        except BaseException as exc:
            record['interruption']=repr(exc)
            raise
        finally:
            # During cleanup, ignore repeat catchable interrupts; retain lock until reaped.
            for sig in old_handlers:signal.signal(sig,signal.SIG_IGN)
            if child is not None:
                if child.poll() is None:
                    try:os.killpg(child.pid,signal.SIGTERM)
                    except ProcessLookupError:pass
                    try:child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try:os.killpg(child.pid,signal.SIGKILL)
                        except ProcessLookupError:pass
                        child.wait()
                record['exit']=child.returncode
            record['end_utc']=stamp();record['end_monotonic_ns']=time.monotonic_ns()
            record['child_reaped']=child is not None and child.poll() is not None
            record['state']='finished-lock-held';save()
            with (evidence/'commands.jsonl').open('a') as f:
                f.write(json.dumps(record)+'\n');f.flush();os.fsync(f.fileno())
            for sig,handler in old_handlers.items():signal.signal(sig,handler)
        raw=(folder/'raw.log').read_text()
        # Semantic labels are convenience copies; UUID directories are authoritative.
        (evidence/(label+'.log')).write_text(raw)
        if record['exit']:raise RuntimeError(f'{label} failed ({record["exit"]}); attempt {attempt}')
        return raw

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--label',required=True);p.add_argument('--cwd',required=True)
    p.add_argument('--evidence',required=True);p.add_argument('--submitted-source',action='append');p.add_argument('command',nargs=argparse.REMAINDER)
    a=p.parse_args();cmd=a.command[1:] if a.command[:1]==['--'] else a.command
    run_locked(a.label,cmd,Path(a.cwd),Path(a.evidence),submitted_sources=a.submitted_source)
