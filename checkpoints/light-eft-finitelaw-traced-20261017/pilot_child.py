"""Limit/lock handshake, then exec the exact parent-supplied plan in the same PID.
Not a Lean runtime replacement. Parent validates production command before spawning.
"""
import json,os,resource,sys
LIMITS={'RLIMIT_AS':3221225472,'RLIMIT_CPU':60,'RLIMIT_FSIZE':16*1024**2,'RLIMIT_CORE':0}

def configure():
    result={}
    for name,value in LIMITS.items():
        key=getattr(resource,name)
        resource.setrlimit(key,(value,value))
        actual=resource.getrlimit(key)
        if actual!=(value,value):raise RuntimeError('limit readback failed: '+name)
        result[name]=list(actual)
    return result

def main():
    configfd,readyfd,ackfd,lockfd=map(int,sys.argv[1:])
    try:
        os.setsid()  # Tracee owns an isolated group; tracer has a separate group.
        with os.fdopen(configfd) as f:plan=json.load(f)
        actual=configure()
        st=os.fstat(lockfd)
        packet=dict(limits=actual,pid=os.getpid(),ppid=os.getppid(),sid=os.getsid(0),pgid=os.getpgrp(),lock_fd=lockfd,lock_device=st.st_dev,lock_inode=st.st_ino,lock_inheritable=os.get_inheritable(lockfd))
        os.write(readyfd,(json.dumps(packet)+'\n').encode());os.close(readyfd)
        if os.read(ackfd,1)!=b'G':raise RuntimeError('No verified pre-exec authorization')
        os.close(ackfd)
        os.execve(plan['argv'][0],plan['argv'],plan['env'])
    except BaseException as e:
        try:os.write(readyfd,(json.dumps({'error':repr(e)})+'\n').encode())
        except OSError:pass
        os.write(2,('pilot launch refused: '+repr(e)+'\n').encode())
        os._exit(125)
if __name__=='__main__':main()
