"""Exact reviewed released-inode reuse; separate legacy synthetic creation."""
from pathlib import Path
import fcntl,json,os,stat,time,uuid
from contracts import require,save,ProductionDisabled
COMMON=Path('/tmp/distance-sparsification-single-compiler.lock')
class Lease:
 def __init__(self,path,report,coordinated,fixture=False,authority=None):
  self.path=Path(path).absolute();self.report=Path(report);self.coordinated=coordinated;self.fixture=fixture;self.authority=authority;self.file=None;self.record={}
 def __enter__(self):
  if self.path==COMMON or not self.fixture:
   from authority import ReviewedAuthority
   if not isinstance(self.authority,ReviewedAuthority):raise ProductionDisabled('Fresh production ownership requires independently reviewed implementation and coordinated authority')
   self.authority.check_live();require(self.path==COMMON and not self.fixture,'Wrong production lock path')
   self.reuse=self.authority.released_lock
  else:self.reuse=None
  require(self.coordinated.get('exclusive_worker') is True and self.coordinated.get('same_directory')==str(self.path.parent),'Uncoordinated exclusion')
  for p in self.path.parents:require(not p.is_symlink(),'Symlink lock parent')
  if self.reuse is None:require(not self.path.exists() and not self.path.is_symlink(),'Existing lock is not automatically adopted')
  else:require(str(self.path)==self.reuse['identity']['path'],'Wrong exact released-lock path')
  self.dirfd=os.open(self.path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
  ds=os.fstat(self.dirfd);self.directory_identity=[ds.st_dev,ds.st_ino]
  try:
   if self.reuse is None:
    fd=os.open(self.path.name,os.O_RDWR|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=self.dirfd)
   else:
    expected=self.reuse['identity']
    require(self.directory_identity==expected['directory_identity'],'Released-lock directory identity differs; no adoption')
    before=os.stat(self.path.name,dir_fd=self.dirfd,follow_symlinks=False)
    require(stat.S_ISREG(before.st_mode) and before.st_nlink==1 and before.st_uid==self.reuse['required_uid']==os.getuid() and stat.S_IMODE(before.st_mode)==self.reuse['required_mode']==0o600,'Unsafe released lock')
    require((before.st_dev,before.st_ino)==(expected['device'],expected['inode']),'Released-lock inode differs; no adoption')
    # Intentionally no O_CREAT, O_TRUNC, unlink, fallback or blocking flock.
    fd=os.open(self.path.name,os.O_RDWR|os.O_NOFOLLOW|os.O_CLOEXEC|os.O_NONBLOCK,dir_fd=self.dirfd)
  except BaseException:
   os.close(self.dirfd);raise
  self.file=os.fdopen(fd,'r+')
  try:
   s=os.fstat(fd);self.identity=(s.st_dev,s.st_ino)
   if self.reuse is not None:
    require(self.identity==(expected['device'],expected['inode']),'Opened released-lock FD identity differs; no adoption')
   self.check()
   if self.reuse is not None:self.authority.check_live()
   fcntl.flock(self.file,fcntl.LOCK_EX|fcntl.LOCK_NB)
   self.check()
   self.acquired_ns=time.monotonic_ns()
   self.record=dict(epoch=uuid.uuid4().hex,path=str(self.path),device=s.st_dev,inode=s.st_ino,fd=fd,
    acquired_ns=self.acquired_ns,supervisor_pid=os.getpid(),supervisor_start_ticks=Path('/proc/self/stat').read_text().rsplit(')',1)[1].split()[19],
    boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),namespace={n:os.readlink('/proc/self/ns/'+n) for n in ['pid','mnt','cgroup']},
    directory_identity=self.directory_identity,historical_continuity=False,synthetic_fixture=self.fixture,state='held',
    reused_exact_released_inode=self.reuse is not None,prior_released_epoch=self.reuse['released_epoch'] if self.reuse else None)
   self.check();save(self.report,self.record);return self
  except BaseException:
   self.file.close();os.close(self.dirfd);raise
 def check(self):
  require(self.file is not None and not self.file.closed,'Missing live owner FD')
  a=os.fstat(self.file.fileno());b=os.stat(self.path.name,dir_fd=self.dirfd,follow_symlinks=False)
  d=os.stat(self.path.parent,follow_symlinks=False);opened=os.fstat(self.dirfd)
  require((d.st_dev,d.st_ino)==(opened.st_dev,opened.st_ino),'Lock directory replaced')
  if self.reuse is not None:
   expected=self.reuse['identity']
   require([opened.st_dev,opened.st_ino]==expected['directory_identity'] and (a.st_dev,a.st_ino)==(expected['device'],expected['inode']),'Released-lock directory/FD identity drift')
  require(stat.S_ISREG(a.st_mode) and a.st_nlink==1 and a.st_uid==os.getuid() and a.st_mode&0o777==0o600,'Unsafe lock file')
  require((a.st_dev,a.st_ino)==self.identity==(b.st_dev,b.st_ino),'Owner FD/path identity mismatch')
  require(stat.S_ISREG(b.st_mode),'Symlink lock path')
 def __exit__(self,typ,value,tb):
  # Never release exclusion when a child is still live or unreaped.
  while True:
   try:
    self.check()
    try:pid,status=os.waitpid(-1,os.WNOHANG)
    except ChildProcessError:break
    raise RuntimeError('Kernel child remains: '+str([pid,status]))
   except BaseException as exc:
    self.record.setdefault('release_errors',[]).append(repr(exc));self.record['state']='release-refused'
    save(self.report,self.record);time.sleep(.05)
  self.check();self.record.update(kernel_echild=True,state='release-verified',release_ns=time.monotonic_ns());save(self.report,self.record)
  self.file.close();os.close(self.dirfd);self.record['state']='released';save(self.report,self.record)
