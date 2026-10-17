"""Identity-checked visible accounting with required stats and preserved partial errors."""
import ctypes,os,time,datetime
from pathlib import Path
class StatFS(ctypes.Structure):_fields_=[('magic',ctypes.c_long),('rest',ctypes.c_byte*248)]
def identity(fd):
 s=os.fstat(fd);info=Path(f'/proc/self/fdinfo/{fd}').read_text();mount=next(x.split()[1] for x in info.splitlines() if x.startswith('mnt_id:'));return [s.st_dev,s.st_ino,mount]
class AccountingSampleError(RuntimeError):
 def __init__(self,message,partial):super().__init__(message);self.partial=partial
class VisibleAccounting:
 def __init__(self):self.expected=None;self.last_partial=None
 def sample(self):
  state={'sample_started_ns':time.monotonic_ns(),'sample_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'nodes':[],'identities':[],'collection_errors':[]};self.last_partial=state;operation='namespace'
  try:
   state.update(namespace=os.readlink('/proc/self/ns/cgroup'),membership=Path('/proc/self/cgroup').read_text(),mountinfo=Path('/proc/self/mountinfo').read_text())
   if state['membership']!='0::/\n':raise RuntimeError('Unexpected membership')
   lines=[x for x in state['mountinfo'].splitlines() if ' - cgroup2 ' in x]
   if len(lines)!=1 or lines[0].split()[3:5]!=['/..','/sys/fs/cgroup']:raise RuntimeError('Unreviewed visible cgroup mount')
   mount=lines[0].split()[0]
   for directory in ['/sys/fs/cgroup','/sys/fs/cgroup/init']:
    operation=directory;row={'path':directory,'partial_raw':{}};state['nodes'].append(row);ids={};state['identities'].append(ids)
    fd=os.open(directory,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
    try:
     fs=StatFS();libc=ctypes.CDLL(None,use_errno=True)
     if libc.fstatfs(fd,ctypes.byref(fs))!=0 or fs.magic!=0x63677270:raise RuntimeError('Not cgroupfs')
     ids['directory']=identity(fd)
     if ids['directory'][2]!=mount:raise RuntimeError('Directory overmount')
     values=row['partial_raw']
     for name in ['memory.max','memory.current','memory.stat','memory.events','cgroup.procs','pids.current','pids.max','pids.events']:
      operation=directory+'/'+name;f=os.open(name,os.O_RDONLY|os.O_NOFOLLOW,dir_fd=fd)
      try:
       ids[name]=identity(f)
       if ids[name][2]!=mount:raise RuntimeError('Accounting overmount')
       values[name]=os.read(f,65536).decode()
      finally:os.close(f)
     if directory.endswith('/init') and str(os.getpid()) not in values['cgroup.procs'].split():raise RuntimeError('Observer not in expected visible child')
     limit=values['memory.max'].strip();current=int(values['memory.current'])
     if current<0 or (limit!='max' and (not limit.isdecimal() or int(limit)<=0)):raise RuntimeError('Bad memory value')
     stats={k:int(v) for k,v in [x.split() for x in values['memory.stat'].splitlines()]};events={k:int(v) for k,v in [x.split() for x in values['memory.events'].splitlines()]}
     required={key:stats[key] for key in ('anon','file','kernel')}
     if any(value<0 for value in required.values()):raise RuntimeError('Negative memory.stat value')
     row.update(limit=limit,current=current,memory_stat=stats,memory_stat_raw=values['memory.stat'],memory_events=events,oom={key:events[key] for key in ('oom','oom_kill','oom_group_kill')},pids_current=int(values['pids.current']),pids_max=values['pids.max'].strip(),pids_events={k:int(v) for k,v in [x.split() for x in values['pids.events'].splitlines()]})
     del row['partial_raw']
    finally:os.close(fd)
   stable={key:state[key] for key in ('namespace','membership','mountinfo','identities')};stable['limits']=[(x['limit'],x['pids_max']) for x in state['nodes']]
   if self.expected is None:self.expected=stable
   elif stable!=self.expected:raise RuntimeError('Accounting identity/limit changed')
   if Path('/proc/self/mountinfo').read_text()!=state['mountinfo'] or Path('/proc/self/cgroup').read_text()!=state['membership'] or os.readlink('/proc/self/ns/cgroup')!=state['namespace']:raise RuntimeError('Accounting changed during read')
   heads=[int(x['limit'])-x['current'] for x in state['nodes'] if x['limit']!='max']
   if not heads:raise RuntimeError('No visible finite bound')
   state['headroom']=min(heads);operation='host MemAvailable';available=[x.split() for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')]
   if len(available)!=1 or available[0][2]!='kB':raise RuntimeError('Missing/bad MemAvailable')
   state['system_available']=int(available[0][1])*1024;state['qualification']='PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN';state['sample_finished_ns']=time.monotonic_ns();return state
  except Exception as exc:
   state['collection_errors'].append({'operation':operation,'error':repr(exc)});state['sample_finished_ns']=time.monotonic_ns();raise AccountingSampleError('Accounting collection failed: '+repr(exc),state) from exc
