"""Read-only observation; never changes admission or namespace state."""
import ctypes,datetime,errno,json,os,stat
from pathlib import Path

class StatFS(ctypes.Structure):
    _fields_=[('f_type',ctypes.c_long),('f_bsize',ctypes.c_long),('f_blocks',ctypes.c_ulong),('f_bfree',ctypes.c_ulong),('f_bavail',ctypes.c_ulong),('f_files',ctypes.c_ulong),('f_ffree',ctypes.c_ulong),('f_fsid',ctypes.c_int*2),('f_namelen',ctypes.c_long),('f_frsize',ctypes.c_long),('f_flags',ctypes.c_long),('f_spare',ctypes.c_long*4)]

def inspect(root=Path('/sys/fs/cgroup')):
    libc=ctypes.CDLL(None,use_errno=True);result=dict(pid=os.getpid(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),namespace=os.readlink('/proc/self/ns/cgroup'))
    result['membership_before']=Path('/proc/self/cgroup').read_text();result['mountinfo_before']=Path('/proc/self/mountinfo').read_text()
    observations=[]
    for directory in [root,root/'init']:
        fd=os.open(directory,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        try:
            data=StatFS()
            if libc.fstatfs(fd,ctypes.byref(data))!=0:raise OSError(ctypes.get_errno(),'fstatfs')
            entry=dict(path=str(directory),filesystem_magic=hex(data.f_type),fdinfo=Path(f'/proc/self/fdinfo/{fd}').read_text(),inode=os.fstat(fd).st_ino,device=os.fstat(fd).st_dev,entries=sorted(os.listdir(fd)),files={})
            for name in ['cgroup.type','cgroup.controllers','cgroup.procs','cgroup.threads','cgroup.stat','memory.current','memory.max','memory.high']:
                try:
                    filefd=os.open(name,os.O_RDONLY|os.O_NOFOLLOW,dir_fd=fd)
                    try:
                        st=os.fstat(filefd);content=b''
                        while chunk:=os.read(filefd,65536):content+=chunk
                        entry['files'][name]=dict(content=content.decode(),inode=st.st_ino,device=st.st_dev,fdinfo=Path(f'/proc/self/fdinfo/{filefd}').read_text())
                    finally:os.close(filefd)
                except OSError as exc:entry['files'][name]=dict(error=repr(exc),errno=exc.errno)
            entry['self_in_procs']=str(os.getpid()) in entry['files'].get('cgroup.procs',{}).get('content','').split()
            observations.append(entry)
        finally:os.close(fd)
    result['observations']=observations
    result['membership_after']=Path('/proc/self/cgroup').read_text();result['mountinfo_after']=Path('/proc/self/mountinfo').read_text()
    result['namespace_after']=os.readlink('/proc/self/ns/cgroup')
    result['stable']=result['membership_before']==result['membership_after'] and result['mountinfo_before']==result['mountinfo_after'] and result['namespace']==result['namespace_after']
    result['conclusion']='Observation only; visible mount root has cgroup.type and is not global hierarchy root. Hidden ancestor accounting is not established.'
    return result

if __name__=='__main__':print(json.dumps(inspect(),indent=2))
