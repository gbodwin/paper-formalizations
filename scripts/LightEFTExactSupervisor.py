"""Fail-closed admission and receipts for the clean LightEFT gate only.
No Lean runtime changes. The existing universal lock inode is never replaced.
"""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, shutil, signal, subprocess, time, uuid

LOCK = Path('/tmp/distance-sparsification-single-compiler.lock')
MIN_MEMORY = 4 * 1024**3
MIN_DISK = 2 * 1024**3

def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

from LightEFTCgroup import memory_snapshot
from LightEFTProcessLifecycle import set_subreaper, descendants, cleanup, retry_locked

def admit(preflight):
    m = preflight['memory']
    if 'discovery_error' in m:
        raise RuntimeError('REFUSED: effective cgroup accounting unavailable: '+m['discovery_error'])
    if m['system_available'] < MIN_MEMORY or (m['cgroup_headroom'] is not None and m['cgroup_headroom'] < MIN_MEMORY):
        raise RuntimeError('REFUSED: less than 4 GiB system available memory or cgroup headroom')
    if preflight['free_disk'] <= MIN_DISK:
        raise RuntimeError('REFUSED: at most 2 GiB free disk')
    for row in preflight['processes'].splitlines()[1:]:
        fields = row.split()
        if fields[-1] in ('lean', 'lake', 'leanchecker') and not fields[2].startswith('Z'):
            raise RuntimeError('REFUSED: another compiler/checker is active: ' + row)

def singleton(argv, env):
    if len(argv) != 3 or argv[1] != '-v' or argv[2] in ('LightEFTSpanners', 'LightSpanners'):
        raise ValueError('Only an explicit nonaggregate singleton replay is allowed')
    target = argv[2]
    search = [Path(p).resolve() for p in env['LEAN_PATH'].split(os.pathsep) if p]
    found = {}
    for base in search:
        for path in base.rglob('*.olean'):
            module = '.'.join(path.relative_to(base).with_suffix('').parts)
            if module == target or module.startswith(target + '.'):
                found.setdefault(module, set()).add(str(path.resolve()))
    if set(found) != {target} or len(found[target]) != 1:
        raise ValueError('REFUSED: missing, shadowed or prefix-expanded checker target: ' + repr(found))
    resolution = json.loads(Path(env['LIGHTEFT_CHECKER_RESOLUTION_FILE']).read_text())
    expected = next(iter(found[target]))
    if resolution['count'] != 1 or resolution['target'] != target or resolution['resolved'] != [{'module': target, 'object': expected}]:
        raise ValueError('Official resolver disagrees with singleton object')
    return dict(target=target, object=expected, sha256=hashlib.sha256(Path(expected).read_bytes()).hexdigest(),
                search_path=[str(p) for p in search], under_lock=True)

def validate_command(argv,env):
    tool=Path(env['LEAN_SYSROOT']).resolve()
    if Path(argv[0]).resolve() not in [tool/'bin/lean',tool/'bin/leanchecker']:
        raise ValueError('Only explicit official Lean/checker executables are allowed')
    if not env.get('LEAN_PATH') or not env.get('LEAN_SRC_PATH'):
        raise ValueError('Explicit search paths are required')

def run_locked(label, argv, cwd, evidence, env=None, submitted_sources=None):
    """argv=[] performs startup admission with a receipt and no child process."""
    cwd=Path(cwd); evidence=Path(evidence); env=dict(os.environ if env is None else env)
    folder=evidence/'attempts'/uuid.uuid4().hex; folder.mkdir(parents=True)
    record=dict(attempt_id=folder.name,label=label,argv=list(argv),cwd=str(cwd),
                supervisor_pid=os.getpid(),child_pid=None,exit=None,state='created',
                created_utc=stamp(),created_monotonic_ns=time.monotonic_ns(),submitted_sources=[],
                lean_environment={k:env.get(k) for k in ['LEAN_SYSROOT','LEAN_PATH','LEAN_SRC_PATH']},
                source_commit=env.get('LIGHTEFT_SOURCE_COMMIT'),harness_commit=env.get('LIGHTEFT_HARNESS_COMMIT'))
    def save():
        temp=folder/'receipt.tmp';temp.write_text(json.dumps(record,indent=2)+'\n')
        os.replace(temp,folder/'receipt.json')
    save(); (folder/'raw.log').touch(); child=None; handlers={}; old_subreaper=None
    with LOCK.open('a+') as lock:
        try:
            # Nonblocking refusal prevents an unnoticed second worker waiting to start.
            fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            record.update(lock_path=str(LOCK),lock_device=os.fstat(lock.fileno()).st_dev,
                          lock_inode=os.fstat(lock.fileno()).st_ino,lock_fd=lock.fileno(),
                          lock_acquired_utc=stamp(),lock_acquired_monotonic_ns=time.monotonic_ns())
            for source in submitted_sources or []:
                p=Path(source).resolve(); data=p.read_bytes(); digest=hashlib.sha256(data).hexdigest()
                (folder/(digest+'.source')).write_bytes(data)
                record['submitted_sources'].append(dict(path=str(p),sha256=digest,bytes=len(data)))
            save()
            preflight=dict(utc=stamp(),processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True),
                           free_disk=shutil.disk_usage(cwd).free,memory=memory_snapshot())
            (folder/'preflight.json').write_text(json.dumps(preflight,indent=2)+'\n')
            record['preflight_sha256']=hashlib.sha256((folder/'preflight.json').read_bytes()).hexdigest(); save()
            admit(preflight)
            if not argv:
                record.update(exit=0,state='admitted-no-child'); return ''
            validate_command(argv,env)
            if descendants():raise RuntimeError('Supervisor has preexisting children')
            old_subreaper=set_subreaper(True)
            record['subreaper_enabled']=True;save()
            if Path(argv[0]).name=='leanchecker':
                record['checker_resolution']=singleton(argv,env); save()
            def interrupted(sig,frame):
                raise InterruptedError(f'signal {sig}')
            for sig in [signal.SIGTERM,signal.SIGINT,signal.SIGHUP]:
                handlers[sig]=signal.signal(sig,interrupted)
            with (folder/'raw.log').open('w') as log:
                blocked=signal.pthread_sigmask(signal.SIG_BLOCK,set(handlers))
                try:
                    record.update(start_utc=stamp(),start_monotonic_ns=time.monotonic_ns())
                    child=subprocess.Popen(argv,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,
                        pass_fds=(lock.fileno(),),start_new_session=True,
                        preexec_fn=lambda: signal.pthread_sigmask(signal.SIG_SETMASK,blocked))
                    record.update(child_pid=child.pid,process_group=child.pid,state='running-lock-held');save()
                finally:
                    signal.pthread_sigmask(signal.SIG_SETMASK,blocked)
                record['exit']=child.wait()
            if record['exit']:
                raise RuntimeError(f'{label} failed ({record["exit"]}); attempt {folder.name}')
        except BaseException as exc:
            record['failure']=repr(exc)
            raise
        finally:
            # Outer fail-stop barrier also catches failures in cleanup helpers or
            # signal/finalization setup. The lock context cannot unwind through it.
            while True:
                try:
                    for sig in handlers:
                        retry_locked('ignore-cleanup-signal',lambda sig=sig:signal.signal(sig,signal.SIG_IGN),record,save)
                    if child is not None:
                        cleanup(child,record,save)
                    if old_subreaper is not None:
                        retry_locked('restore-subreaper',lambda:set_subreaper(old_subreaper),record,save)
                    def finalize_attempt():
                        record.update(end_utc=stamp(),end_monotonic_ns=time.monotonic_ns(),
                                      child_reaped=child is not None and child.poll() is not None,
                                      state='failed' if 'failure' in record else ('finished' if child is not None else 'no-child'))
                        save()
                        with (evidence/'commands.jsonl').open('a') as f:
                            f.write(json.dumps(record)+'\n'); f.flush();os.fsync(f.fileno())
                        (evidence/(label+'.log')).write_bytes((folder/'raw.log').read_bytes())
                    retry_locked('finalize-attempt',finalize_attempt,record,save)
                    for sig,handler in handlers.items():
                        retry_locked('restore-signal',lambda sig=sig,handler=handler:signal.signal(sig,handler),record,save)
                    break
                except BaseException as exc:
                    from LightEFTProcessLifecycle import cleanup_error
                    cleanup_error('finalization-barrier',exc,record,save)
            if record.get('cleanup_errors'):
                # Keep the recovered error visible; never turn cleanup recovery
                # into a successful compiler/checker invocation.
                record['state']='failed';retry_locked('persist-failed-cleanup',save,record,save)
                raise RuntimeError('Cleanup/finalization errors; all descendants reaped before lock release')
        return (folder/'raw.log').read_text()
