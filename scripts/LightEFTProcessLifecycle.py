"""Linux child supervision. Cleanup errors retain exclusion until proven quiescent."""
import ctypes,os,signal,time
from pathlib import Path


def set_subreaper(value=None):
    libc=ctypes.CDLL(None,use_errno=True);old=ctypes.c_int()
    if libc.prctl(37,ctypes.byref(old),0,0,0)!=0:raise OSError(ctypes.get_errno(),'PR_GET_CHILD_SUBREAPER')
    if value is not None and libc.prctl(36,int(value),0,0,0)!=0:raise OSError(ctypes.get_errno(),'PR_SET_CHILD_SUBREAPER')
    return old.value


def descendants():
    entries={}
    for p in Path('/proc').iterdir():
        if not p.name.isdecimal():continue
        try:
            fields=(p/'stat').read_text().rsplit(')',1)[1].split()
            entries[int(p.name)]=dict(pid=int(p.name),ppid=int(fields[1]),pgid=int(fields[2]),
                                      state=fields[0],start_ticks=int(fields[19]))
        except (FileNotFoundError,ProcessLookupError):continue
    selected={os.getpid()};changed=True
    while changed:
        new={pid for pid,row in entries.items() if row['ppid'] in selected}
        changed=not new<=selected;selected|=new
    return [entries[pid] for pid in sorted(selected-{os.getpid()}) if pid in entries]


def cleanup_error(stage,exc,record,persist):
    record.setdefault('cleanup_errors',[]).append(dict(stage=stage,error=repr(exc),monotonic_ns=time.monotonic_ns()))
    record.setdefault('failure','Cleanup/finalization failed; exclusion retained until recovery')
    record['state']='cleanup-error-lock-held'
    try:persist()
    except BaseException as diagnostic_error:
        # Diagnostic I/O must not unwind the exclusion either. Finalization retries.
        record['diagnostic_persistence_error']=repr(diagnostic_error)
        try:os.write(2,('LOCK RETAINED: '+stage+': '+repr(exc)+'; receipt write: '+repr(diagnostic_error)+'\n').encode())
        except BaseException:pass


def retry_locked(stage,operation,record,persist):
    """No timeout/unwind while outcome is unknown. Any recovered error is sticky failure."""
    while True:
        try:return operation()
        except BaseException as exc:
            cleanup_error(stage,exc,record,persist)
            time.sleep(0.05)


def cleanup(child,record,persist,grace=1.0):
    """Caller owns lock, has enabled subreaping, and had no preexisting children.
    Never propagate a cleanup error before all descendants are proven reaped.
    """
    started=time.monotonic();seen={};reaped={};sent=set()
    while True:
        try:
            child.poll()  # Popen alone owns/reaps the direct child.
            rows=descendants()
            for row in rows:seen[(row['pid'],row['start_ticks'])]=row
            sig=signal.SIGTERM if time.monotonic()-started<grace else signal.SIGKILL
            groups={row['pgid'] for row in rows if row['pgid']!=os.getpgrp()}
            for group in groups:
                if ('group',group,sig) not in sent:
                    try:os.killpg(group,sig)
                    except ProcessLookupError:pass
                    sent.add(('group',group,sig))
            for row in rows:
                key=(row['pid'],row['start_ticks'],sig)
                if key not in sent:
                    try:os.kill(row['pid'],sig)
                    except ProcessLookupError:pass
                    sent.add(key)
                if row['pid']!=child.pid:
                    try:
                        pid,status=os.waitpid(row['pid'],os.WNOHANG)
                        if pid:reaped[pid]=status
                    except ChildProcessError:pass  # May still belong to a living parent.
            if child.poll() is not None and not descendants():
                # A /proc scan alone is not the release proof. As subreaper, no
                # kernel children (ECHILD) also rules out unobserved live orphans.
                try:
                    pid,status=os.waitpid(-1,os.WNOHANG)
                    if pid:reaped[pid]=status
                except ChildProcessError:
                    break
        except BaseException as exc:
            cleanup_error('terminate-discover-reap',exc,record,persist)
        time.sleep(0.02)
    record['descendants_observed']=list(seen.values())
    record['adopted_descendants_reaped']=[dict(pid=p,wait_status=s) for p,s in sorted(reaped.items())]
    record['all_descendants_gone']=True
    record['kernel_no_children_verified']=True
    record['exit']=child.returncode
