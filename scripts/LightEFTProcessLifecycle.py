"""Linux child supervision helpers. No compiler execution in this module."""
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


def cleanup(child,record,grace=1.0):
    """Reap direct and adopted descendants before returning/releasing the lock.
    Caller must enable subreaper and have no preexisting children.
    """
    started=time.monotonic();seen={};reaped={};sent=set()
    while True:
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
                except ChildProcessError:pass  # Still owned/reaped by its living parent.
        if child.poll() is not None and not descendants():break
        # Do not release the lock with a surviving descendant: continue SIGKILL
        # and reaping even for a stuck process. No compiler can start behind it.
        time.sleep(0.02)
    record['descendants_observed']=list(seen.values())
    record['adopted_descendants_reaped']=[dict(pid=p,wait_status=s) for p,s in sorted(reaped.items())]
    record['all_descendants_gone']=True
    record['exit']=child.returncode
