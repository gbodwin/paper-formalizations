"""Fixed existing namespaced view; no assertion that hidden ancestors are known."""
import ctypes,os
from pathlib import Path

class StatFS(ctypes.Structure):
    _fields_=[('magic',ctypes.c_long),('rest',ctypes.c_byte*248)]

def identity(fd):
    s=os.fstat(fd)
    info=Path(f'/proc/self/fdinfo/{fd}').read_text()
    mount=next(x.split()[1] for x in info.splitlines() if x.startswith('mnt_id:'))
    return [s.st_dev,s.st_ino,mount]

class VisibleAccounting:
    def __init__(self):
        self.expected=None
    def sample(self):
        state={'namespace':os.readlink('/proc/self/ns/cgroup'),'membership':Path('/proc/self/cgroup').read_text(),'mountinfo':Path('/proc/self/mountinfo').read_text(),'nodes':[]}
        if state['membership']!='0::/\n':raise RuntimeError('Unexpected membership')
        lines=[x for x in state['mountinfo'].splitlines() if ' - cgroup2 ' in x]
        if len(lines)!=1:raise RuntimeError('Ambiguous cgroup mount')
        fields=lines[0].split()
        if fields[3:5]!=['/..','/sys/fs/cgroup']:raise RuntimeError('Unreviewed visible mount')
        expected_mount=fields[0]
        identities=[]
        for directory in ['/sys/fs/cgroup','/sys/fs/cgroup/init']:
            fd=os.open(directory,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
            try:
                statfs=StatFS();libc=ctypes.CDLL(None,use_errno=True)
                if libc.fstatfs(fd,ctypes.byref(statfs))!=0 or statfs.magic!=0x63677270:raise RuntimeError('Not cgroupfs')
                ident=identity(fd)
                if ident[2]!=expected_mount:raise RuntimeError('Directory overmount')
                ids={'directory':ident};values={}
                for name in ['memory.max','memory.current','memory.events','cgroup.procs','pids.current','pids.max','pids.events']:
                    f=os.open(name,os.O_RDONLY|os.O_NOFOLLOW,dir_fd=fd)
                    try:
                        ids[name]=identity(f)
                        if ids[name][2]!=expected_mount:raise RuntimeError('Accounting overmount')
                        values[name]=os.read(f,65536).decode()
                    finally:os.close(f)
                if directory.endswith('/init') and str(os.getpid()) not in values['cgroup.procs'].split():raise RuntimeError('Observer not in visible child')
                limit=values['memory.max'].strip();current=int(values['memory.current'])
                if current<0 or (limit!='max' and (not limit.isdecimal() or int(limit)<=0)):raise RuntimeError('Bad memory value')
                events=dict(line.split() for line in values['memory.events'].splitlines())
                oom={k:int(events[k]) for k in ['oom','oom_kill','oom_group_kill']}
                state['nodes'].append({'path':directory,'limit':limit,'current':current,'oom':oom,'pids_current':int(values['pids.current']),'pids_max':values['pids.max'].strip(),'pids_events':{k:int(v) for k,v in (line.split() for line in values['pids.events'].splitlines())}})
                identities.append(ids)
            finally:os.close(fd)
        state['identities']=identities
        stable={k:state[k] for k in ['namespace','membership','mountinfo','identities']}
        stable['limits']=[(n['limit'],n['pids_max']) for n in state['nodes']]
        if self.expected is None:self.expected=stable
        elif stable!=self.expected:raise RuntimeError('Accounting identity/limit changed')
        if Path('/proc/self/mountinfo').read_text()!=state['mountinfo'] or Path('/proc/self/cgroup').read_text()!=state['membership'] or os.readlink('/proc/self/ns/cgroup')!=state['namespace']:raise RuntimeError('Accounting changed during read')
        heads=[int(n['limit'])-n['current'] for n in state['nodes'] if n['limit']!='max']
        if not heads:raise RuntimeError('No visible finite bound')
        state['headroom']=min(heads)
        available=[x.split() for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')]
        if len(available)!=1 or available[0][2]!='kB':raise RuntimeError('Bad MemAvailable')
        state['system_available']=int(available[0][1])*1024
        state['qualification']='PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN'
        return state
