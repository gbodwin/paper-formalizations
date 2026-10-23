"""Bounded passive Python/C-call attribution; no process or policy entry point.

Instrumentation reports repeated reads, never reuses their results. Exceptions
from the measured implementation propagate unchanged. Observer failure rejects
the diagnostic; it never changes a failed component into a successful one.
"""
import hashlib, os, sys, time
from pathlib import PosixPath

class Collector:
 def __init__(self,python_functions):
  if len(python_functions)>48:raise RuntimeError('Finite profile label limit')
  self.codes={fn.__code__:name for name,fn in python_functions.items()}
  self.c_functions={id(fn):name for name,fn in [('os.fsync',os.fsync),('os.replace',os.replace),('os.open',os.open),('os.fstat',os.fstat)]}
  self.stack=[];self.rows={};self.paths={};self.read_groups={};self.fault=None
  self.callback=self.event;self.regular_code=python_functions['contracts.regular'].__code__
  self.pending_regular={};self.started=None;self.finished=None
 def event(self,frame,event,arg):
  try:self.observe(frame,event,arg)
  except BaseException as error:
   # Preserve the component's own exception/return behavior. __exit__ rejects
   # an otherwise successful measurement if the observer could not record it.
   self.fault=type(error).__name__+': '+str(error)[:512];sys.setprofile(None)
 def observe(self,frame,event,arg):
  if event in ['call','return']:
   name=self.codes.get(frame.f_code);token=('py',id(frame))
  elif event in ['c_call','c_return','c_exception']:
   name=self.c_functions.get(id(arg));token=('c',id(frame),id(arg))
  else:return
  if name is None:return
  now=time.perf_counter_ns()
  if event in ['call','c_call']:
   if len(self.stack)>=128:raise RuntimeError('Profile nesting bound')
   group=next((r[1] for r in reversed(self.stack) if r[1] in
    ['CIInventory.scan','contracts.unchanged','contracts.effective','scope.Context.verify']), 'other')
   if frame.f_code is self.regular_code and event=='call':
    value=frame.f_locals.get('path')
    if type(value) not in [str,PosixPath]:raise RuntimeError('Unsupported path type; no custom __fspath__ calls')
    key=hashlib.sha256(str(value).encode()).hexdigest()
    if key not in self.paths and len(self.paths)>=131072:raise RuntimeError('Distinct read-path bound')
    self.paths[key]=self.paths.get(key,0)+1
    row=self.read_groups.setdefault(group,dict(attempts=0,completed=0,bytes=0));row['attempts']+=1
    self.pending_regular[id(frame)]=group
   self.stack.append([token,name,now,0]);return
  if not self.stack or self.stack[-1][0]!=token:raise RuntimeError('Profile stack mismatch')
  _,name,start,nested=self.stack.pop();elapsed=now-start
  row=self.rows.setdefault(name,dict(calls=0,inclusive_ns=0,exclusive_ns=0))
  row['calls']+=1;row['inclusive_ns']+=elapsed;row['exclusive_ns']+=elapsed-nested
  if self.stack:self.stack[-1][3]+=elapsed
  if frame.f_code is self.regular_code and event=='return':
   group=self.pending_regular.pop(id(frame))
   if type(arg) is tuple and len(arg)==2 and type(arg[0]) is dict and type(arg[1]) is bytes:
    self.read_groups[group]['completed']+=1;self.read_groups[group]['bytes']+=len(arg[1])
 def __enter__(self):
  if sys.getprofile() is not None:raise RuntimeError('Existing profiler; refuse replacement')
  self.started=time.perf_counter_ns();sys.setprofile(self.callback);return self
 def __exit__(self,kind,error,tb):
  if self.fault is None and sys.getprofile() is not self.callback:self.fault='Profiler was replaced'
  sys.setprofile(None);self.finished=time.perf_counter_ns()
  if self.stack or self.pending_regular:self.fault=self.fault or 'Unclosed profile frames'
  if kind is None and self.fault:raise RuntimeError('Incomplete diagnostic profile: '+self.fault)
  return False
 def snapshot(self):
  if self.fault or self.finished is None:raise RuntimeError('Incomplete profile: '+str(self.fault))
  histogram={}
  for count in self.paths.values():histogram[str(count)]=histogram.get(str(count),0)+1
  digest=hashlib.sha256()
  for key,count in sorted(self.paths.items()):digest.update((key+':'+str(count)+'\n').encode())
  return dict(elapsed_ns=self.finished-self.started,counters=self.rows,regular_reads=self.read_groups,
   distinct_regular_paths=len(self.paths),reads_per_path_histogram=histogram,
   path_read_multiset_sha256=digest.hexdigest(),observer_overhead_included=True,
   attribution='exclusive selected-frame costs; unselected work remains with selected caller; no read result cached')
