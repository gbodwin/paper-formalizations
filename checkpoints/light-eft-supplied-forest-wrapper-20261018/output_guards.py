"""Scoped live guards, not the historical full-graph directory guard."""
from pathlib import Path
import os,stat
from contracts import signature,object_outputs,outputs,require
def runtime_errors(record,preexec=False):
 errors=[]
 try:
  spec=record['output_guard_spec']
  fd=record['lock']['fd'];a=os.fstat(fd);b=os.stat(record['lock']['path'],follow_symlinks=False)
  require(stat.S_ISREG(b.st_mode) and a.st_nlink==1 and (a.st_dev,a.st_ino)==(record['lock']['device'],record['lock']['inode'])==(b.st_dev,b.st_ino),'Live lock FD/path changed')
  for p,row in spec['protected'].items():require(signature(Path(p).lstat())==row['identity'],'Live protected object/resolution/input changed')
  object_outputs(spec['objects'],spec['target'],spec['stage']!='compile')
  if spec['stage']=='audit':outputs(spec['audit'])
  else:require(not list(Path(spec['audit']).iterdir()),'Audit exports appeared outside audit stage')
 except Exception as e:errors.append(repr(e))
 return errors
