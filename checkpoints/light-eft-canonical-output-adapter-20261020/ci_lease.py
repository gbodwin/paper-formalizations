"""New CI-run lock only. Never opens/reuses the ordinary executor's lock."""
from pathlib import Path
import datetime, fcntl, json, os, stat, time, uuid

class CILease:
    def __init__(self,root,save,check_identity):
        self.path=Path(root)/'ci-single-compiler.lock';self.report=Path(root)/'lease.json'
        self.save=save;self.check_identity=check_identity;self.record={};self.file=None

    def __enter__(self):
        self.check_identity()
        for p in self.path.parents:
            if p.is_symlink():raise ValueError('Symlink CI lock parent')
        self.dirfd=os.open(self.path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        try:
            fd=os.open(self.path.name,os.O_RDWR|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=self.dirfd)
        except BaseException:os.close(self.dirfd);raise
        self.file=os.fdopen(fd,'r+')
        try:
            s=os.fstat(fd);self.identity=[s.st_dev,s.st_ino];d=os.fstat(self.dirfd);self.directory=[d.st_dev,d.st_ino]
            self.check();fcntl.flock(self.file,fcntl.LOCK_EX|fcntl.LOCK_NB);self.acquired_ns=time.monotonic_ns()
            self.record=dict(epoch=uuid.uuid4().hex,path=str(self.path),device=s.st_dev,inode=s.st_ino,fd=fd,
                directory_identity=self.directory,acquired_ns=self.acquired_ns,supervisor_pid=os.getpid(),
                supervisor_start_ticks=Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()[19],
                boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
                namespace={n:os.readlink('/proc/self/ns/'+n) for n in ['pid','mnt','cgroup']},
                state='held',synthetic_fixture=False,historical_continuity=False,
                qualification='Fresh CI-run filesystem identity; no local inode or historical continuity claim')
            self.save(self.report,self.record);return self
        except BaseException:self.file.close();os.close(self.dirfd);raise

    def check(self):
        self.check_identity()
        self.check_filesystem()

    def check_filesystem(self):
        a=os.fstat(self.file.fileno());b=os.stat(self.path.name,dir_fd=self.dirfd,follow_symlinks=False)
        d=os.stat(self.path.parent,follow_symlinks=False);opened=os.fstat(self.dirfd)
        if [a.st_dev,a.st_ino]!=self.identity or [b.st_dev,b.st_ino]!=self.identity:
            raise ValueError('CI owner FD/path changed')
        if [d.st_dev,d.st_ino]!=self.directory or [opened.st_dev,opened.st_ino]!=self.directory:
            raise ValueError('CI lock directory changed')
        if not stat.S_ISREG(a.st_mode) or not stat.S_ISREG(b.st_mode) or a.st_nlink!=1 or a.st_uid!=os.getuid() or stat.S_IMODE(a.st_mode)!=0o600:
            raise ValueError('Unsafe CI lock')

    def __exit__(self,typ,value,tb):
        # Keep the lock on cleanup failure, as in the reviewed ordinary lease.
        # Expiry blocks new work; it must not prevent safe final release after ECHILD.
        while True:
            try:
                self.check_filesystem()
                try:os.waitpid(-1,os.WNOHANG)
                except ChildProcessError:break
                raise RuntimeError('Kernel child remains')
            except BaseException as e:
                self.record.setdefault('release_errors',[]).append(repr(e));self.record['state']='release-refused'
                self.save(self.report,self.record);time.sleep(.05)
        self.record.update(state='release-verified',release_ns=time.monotonic_ns(),kernel_echild=True)
        self.save(self.report,self.record);self.file.close();os.close(self.dirfd)
        self.record['state']='released';self.save(self.report,self.record)
