"""Scoped live metadata checks; completed hashes remain in the post-wait hooks."""
from pathlib import Path
import os,stat
from contracts import signature,require,SUFFIXES,EXPORTS
def live_tree(root,allowed):
 root=Path(root)
 for parent in root.absolute().parents:require(not parent.is_symlink(),'Symlink output parent')
 s=root.lstat();require(stat.S_ISDIR(s.st_mode),'Missing/non-directory/symlink output root')
 allowed=set(map(str,allowed));dirs={str(parent) for f in allowed for parent in Path(f).parents if root in parent.parents}
 files={}
 for p in root.rglob('*'):
  s=p.lstat()
  if stat.S_ISDIR(s.st_mode):
   require(str(p) in dirs,'Unexpected live output directory');continue
  require(str(p) in allowed,'Unexpected live output path')
  require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'Nonregular/linked live output')
  # Size/timestamps may change while a legitimate output is being written.
  # No content read and no before/after stability requirement here.
  files[str(p)]={'bytes':s.st_size,'device':s.st_dev,'inode':s.st_ino}
 return files
def live_objects(root,target,complete):
 base=str(target)[:-len('.olean')];files=live_tree(root,{base+s for s in SUFFIXES})
 if complete:require(str(target) in files,'Missing completed target')
 require(all(0<=r['bytes']<=16*1024**2 for r in files.values()),'Live object size exceeds ordinary FSIZE')
 return files
def live_audit(root):
 root=Path(root);files=live_tree(root,{str(root/n) for n in EXPORTS})
 require(all(0<=r['bytes']<=64*1024**2 for r in files.values()) and
   sum(r['bytes'] for r in files.values())<=320*1024**2,'Live audit size budget')
 return files
def runtime_errors(record,preexec=False):
 errors=[]
 try:
  spec=record['output_guard_spec']
  fd=record['lock']['fd'];a=os.fstat(fd);b=os.stat(record['lock']['path'],follow_symlinks=False)
  require(stat.S_ISREG(b.st_mode) and a.st_nlink==1 and (a.st_dev,a.st_ino)==(record['lock']['device'],record['lock']['inode'])==(b.st_dev,b.st_ino),'Live lock FD/path changed')
  # Already completed object/resolution/input bindings remain independently immutable.
  for p,row in spec['protected'].items():require(signature(Path(p).lstat())==row['identity'],'Live protected object/resolution/input changed')
  live_objects(spec['objects'],spec['target'],spec['stage']!='compile')
  if spec['stage']=='audit':live_audit(spec['audit'])
  else:
   live_audit(spec['audit'])
   require(not list(Path(spec['audit']).iterdir()),'Audit exports appeared outside audit stage')
 except Exception as e:errors.append(repr(e))
 return errors
