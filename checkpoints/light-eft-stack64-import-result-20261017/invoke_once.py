"""Single authorized attempt with before/after PID-limit observations; no retry."""
from pathlib import Path
import datetime,fcntl,json,os,resource,traceback
import pilot_runner as p
BASE=Path(__file__).resolve().parent

def observe():
    result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pid':os.getpid(),'uid':os.getuid(),'rlimit_nproc':list(resource.getrlimit(resource.RLIMIT_NPROC)),'rlimit_stack':list(resource.getrlimit(resource.RLIMIT_STACK)),'visible_pid_cgroups':[],'same_uid_threads':0,'active_compilers':[]}
    for directory in ['/sys/fs/cgroup','/sys/fs/cgroup/init']:
        row={'path':directory}
        for name in ['pids.current','pids.max','pids.events']:
            fd=os.open(Path(directory)/name,os.O_RDONLY|os.O_NOFOLLOW)
            try:row[name]=os.read(fd,65536).decode()
            finally:os.close(fd)
        result['visible_pid_cgroups'].append(row)
    for directory in Path('/proc').glob('[0-9]*'):
        try:
            fields=dict(line.split(':',1) for line in (directory/'status').read_text().splitlines() if ':' in line)
            name=(directory/'comm').read_text().strip()
            if int(fields['Uid'].split()[0])==os.getuid():result['same_uid_threads']+=int(fields['Threads'])
            if name in ('lean','lake','leanchecker','leantar') and not fields['State'].strip().startswith('Z'):result['active_compilers'].append({'pid':directory.name,'name':name})
        except (FileNotFoundError,ProcessLookupError):continue
    result['hidden_ancestor_pid_limits']='UNKNOWN'
    return result

def snapshot(name,admit=False):
    with p.LOCK.open('r+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(lock.fileno())
        if (st.st_dev,st.st_ino)!=(33,3849):raise RuntimeError('Universal lock identity changed')
        data=observe();data['same_lock']={'device':st.st_dev,'inode':st.st_ino}
        (BASE/name).write_text(json.dumps(data,indent=2)+'\n')
        if admit:
            if data['active_compilers']:raise RuntimeError('Another compiler is active')
            for row in data['visible_pid_cgroups']:
                maximum=row['pids.max'].strip();current=int(row['pids.current'])
                if maximum!='max' and current>=int(maximum):raise RuntimeError('Visible PID/thread limit exhausted')
            if data['rlimit_nproc'][0]!=resource.RLIM_INFINITY and data['same_uid_threads']>=data['rlimit_nproc'][0]:raise RuntimeError('Observed inherited NPROC limit exhausted')
        return data

if __name__=='__main__':
    marker=BASE/'invocation-claimed.json'
    with marker.open('x') as f:json.dump({'one_attempt_only':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},f)
    try:
        before=snapshot('pid-limits-before.json',admit=True)
        print('PID limits not observed exhausted; invoking run_once exactly once',flush=True)
        result=p.run_once();print(json.dumps(result,indent=2),flush=True)
    finally:
        snapshot('pid-limits-after.json')
