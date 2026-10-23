"""Finite non-compiler payload; no execution before independent review.

No subprocess, Lean/Lake/checker/audit, network or hosted-root reconstruction.
"""
from pathlib import Path
import contextlib, hashlib, json, os, resource, stat, sys, time, traceback, types
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
SOURCE=REPO/'checkpoints/light-eft-package-prefix-reuse-proposal-20261022'
ENGINE=REPO/'checkpoints/light-eft-canonical-output-adapter-20261020'
MAX_OUTPUT=1024*1024

def load_source(name,path,bindings):
 data=path.read_bytes();row=bindings[str(path.relative_to(REPO))]
 if len(data)!=row['bytes'] or hashlib.sha256(data).hexdigest()!=row['sha256']:
  raise RuntimeError('Unbound diagnostic source: '+str(path))
 m=types.ModuleType(name);m.__file__=str(path)
 exec(compile(data,str(path),'exec'),m.__dict__)
 return m

class Profile:
 """Exclusive selected-frame counters, never per-event output.

 Nested selected inclusive time is subtracted from its selected caller. Work
 in unselected frames remains charged to that caller. Observer overhead is
 included in raw measurements; uninstrumented measurements are separate.
 """
 def __init__(self,module,contracts):
  self.codes={f.__code__:n for n,f in [('validate',module.validate),
    ('selected_path',module.selected_path),('exists',module.exists),
    ('regular',contracts.regular),('bind',contracts.bind)]}
  if hasattr(module,'_selected_root'):self.codes[module._selected_root.__code__]='selected_root'
  for name in ['stat','lstat','is_file','is_dir','is_symlink','exists']:
   f=getattr(Path,name)
   if hasattr(f,'__code__'):self.codes[f.__code__]='Path.'+name
  self.stack=[];self.rows={}
 def event(self,frame,event,arg):
  name=self.codes.get(frame.f_code)
  if name is None:return
  if event=='call':self.stack.append([frame,name,time.perf_counter_ns(),0])
  elif event=='return':
   if not self.stack or self.stack[-1][0] is not frame:raise RuntimeError('Profile stack mismatch')
   _,name,start,nested=self.stack.pop();elapsed=time.perf_counter_ns()-start
   row=self.rows.setdefault(name,dict(calls=0,inclusive_ns=0,exclusive_ns=0))
   row['calls']+=1;row['inclusive_ns']+=elapsed;row['exclusive_ns']+=elapsed-nested
   if self.stack:self.stack[-1][3]+=elapsed
 def __enter__(self):
  if sys.getprofile() is not None:raise RuntimeError('Existing profiler; refuse replacement')
  sys.setprofile(self.event);return self
 def __exit__(self,*error):
  sys.setprofile(None)
  if self.stack:raise RuntimeError('Unclosed profile frames')

# Last two cases use explicit persistent drift, outside immutable equivalence.
CASES=[('absent',('reject','reject')),('directory',('accept','accept')),
 ('missing-no-fallback',('reject','reject')),('mask-later',('reject','reject')),
 ('root-object',('accept','accept')),('many-one-package',('accept','accept')),
 ('multiple-packages',('accept','accept')),('top-and-nested',('accept','accept')),
 ('missing-leaf',('reject','reject')),('nonregular-leaf',('reject','reject')),
 ('symlink-leaf',('reject','reject')),('symlink-directory',('reject','reject')),
 ('dangling-marker',('reject','reject')),('predicted',('accept','accept')),
 ('compiled',('accept','accept')),('empty-component',('reject','reject')),
 ('unicode',('accept','accept')),('duplicate-roots',('accept','accept')),
 ('overlapping-roots',('accept','accept')),('ordered-scaling',('accept','accept')),
 ('persistent-between-leaves',('reject','reject')),
 ('persistent-final-recheck',('accept','reject'))]

def prepare(root,case,target_name):
 """All adversarial paths/symlinks belong to this new owned scratch tree."""
 root.mkdir(mode=0o700);roots=[root/'r0',root/'r1']
 for r in roots:r.mkdir()
 target=roots[0]/Path(*target_name.split('.')).with_suffix('.olean')
 if case!='predicted':target.parent.mkdir(parents=True)
 modules={}
 def add(module,index=0):
  p=roots[index]/Path(*module.split('.')).with_suffix('.olean')
  p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'fixture bytes, never Lean objects\n')
  modules[module]=p;return p
 if case=='absent':modules['P.A']=roots[0]/'P/A.olean'
 elif case=='root-object':add('P')
 elif case in ['many-one-package','ordered-scaling']:
  for i in range(16 if case=='many-one-package' else 256):add('P.N'+str(i))
 elif case=='multiple-packages':add('P.A');add('Q.B',1)
 elif case=='top-and-nested':add('P');add('P.A')
 elif case=='unicode':add('P.A');add('ℙ.A',1)
 elif case=='empty-component':modules['P..A']=roots[0]/'P/A.olean'
 else:
  p=add('P.A',1 if case in ['missing-no-fallback','mask-later'] else 0)
  if case in ['missing-no-fallback','mask-later']:
   (roots[0]/'P').mkdir()
   if case=='mask-later':(roots[0]/'P/A.olean').write_bytes(b'earlier masking fixture\n')
  elif case=='missing-leaf':p.unlink()
  elif case=='nonregular-leaf':p.unlink();p.mkdir()
  elif case=='symlink-leaf':p.unlink();p.symlink_to(root/'absent')
  elif case=='symlink-directory':p.unlink();p.parent.rmdir();p.parent.symlink_to(root/'absent')
  elif case=='dangling-marker':(roots[0]/'P.olean').symlink_to(root/'absent')
  elif case=='duplicate-roots':roots.insert(1,roots[0])
  elif case=='overlapping-roots':roots.append(roots[0]/'P')
  elif case=='persistent-between-leaves':add('P.B')
 compiled=case=='compiled'
 if compiled:target.write_bytes(b'fixture target, never a Lean object\n')
 return roots,modules,target,compiled,case=='predicted'

def predicted_absent(roots,target_name):
 """lstat absence also excludes dangling physical marker/leaf symlinks."""
 package=target_name.split('.')[0]
 for r in roots:
  for p in [r/package,r/(package+'.olean'),r/Path(*target_name.split('.')).with_suffix('.olean')]:
   try:p.lstat()
   except FileNotFoundError:continue
   raise RuntimeError('Predicted overlay has a physical target marker/leaf: '+str(p))

def outcome(module,contracts,root,case,profiled):
 roots,physical,target,compiled,predicted=prepare(root,case,contracts.TARGET)
 if predicted:predicted_absent(roots,contracts.TARGET)
 original_require=module.require;drifted=False;leaf_checks=[]
 def require(ok,message):
  nonlocal drifted
  if message.startswith('Selected package leaf missing/nonregular: '):
   leaf_checks.append(message.split(': ',1)[1])
  original_require(ok,message)
  if (case.startswith('persistent-') and not drifted and ok and
      message=='Selected package leaf missing/nonregular: P.A'):
   (roots[0]/'P').rename(roots[0]/'P-moved');drifted=True
 module.require=require;profiler=Profile(module,contracts);started=time.perf_counter_ns()
 try:
  with profiler if profiled else contextlib.nullcontext():
   try:
    result=module.validate(roots,physical,target,compiled,predicted)
    answer=dict(status='accept',selected_exact=list(result['selected'].items()),scratch_root=str(root),
       selected=[(m,str(Path(p).relative_to(root))) for m,p in result['selected'].items()],
       model=result['model'],predicted=result['predicted'])
    if leaf_checks!=list(physical)+([contracts.TARGET] if compiled else []):
     raise RuntimeError('Missing/reordered per-module leaf checks')
   except contracts.Rejected as error:
    answer=dict(status='reject',exception_type=type(error).__name__,exception_module=type(error).__module__,
       message=str(error).replace(str(root),'<scratch>'),traceback=traceback.format_exc(limit=12))
 finally:
  module.require=original_require
  if predicted:predicted_absent(roots,contracts.TARGET)
 if predicted:answer['predicted_physical_absence_before_and_after']=True
 answer.update(elapsed_ns=time.perf_counter_ns()-started,profile=profiler.rows if profiled else None,
   leaf_checks=leaf_checks,
   classification='controlled persistent drift' if drifted else 'synthetic immutable')
 return answer

def semantic(answer):
 # Fresh owned roots differ by construction; exact raw maps remain in output.
 # Only the known fixture-root bijection is used for differential comparison.
 return {k:v for k,v in answer.items() if k not in ['elapsed_ns','profile','selected_exact','scratch_root','traceback']}

def main(work):
 bindings={r['path']:r for r in json.loads((HERE/'bindings.json').read_text())['files']}
 contracts=load_source('DiagnosticContracts',ENGINE/'contracts.py',bindings)
 old=sys.modules.get('contracts');sys.modules['contracts']=contracts
 result=dict(scope='NON_COMPILER_COMPONENT_DIAGNOSTIC',accepted=False,cases=[],
   hosted_full_job_savings_established=False,
   actual_populated_root_profile='UNAVAILABLE: no build/cache/compiler setup permitted',
   actual_receipt_IO_profile='Exact final production receipt-save shape only; no historical call-count or whole-job claim')
 try:
  modules=[load_source('Baseline',SOURCE/'BASELINE-package_selection.py',bindings),
           load_source('Proposal',SOURCE/'PROPOSED-package_selection.py',bindings)]
  for case,expected in CASES:
   for pair in range(3 if case=='ordered-scaling' else 1):
    row=dict(case=case,pair=pair,expected=list(expected),versions={});result['cases'].append(row)
    for version in ([0,1] if pair%2==0 else [1,0]):
     label=['baseline','proposal'][version];observations=[]
     for profiled in [False,True]:
      root=work/(case+'-'+str(pair)+'-'+label+'-'+str(int(profiled)))
      observations.append(outcome(modules[version],contracts,root,case,profiled))
     row['versions'][label]=observations
     if semantic(observations[0])!=semantic(observations[1]):raise RuntimeError('Profiler changed outcome: '+case)
     if observations[0]['status']!=expected[version]:raise RuntimeError('Unexpected outcome: '+case+'/'+label)
    left,right=(row['versions'][v][0] for v in ['baseline','proposal'])
    if not case.startswith('persistent-') and semantic(left)!=semantic(right):
     raise RuntimeError('Immutable outcome/map/exception differs: '+case)
  # Actual checkout source component only; no claim about original build roots.
  profiler=Profile(modules[0],contracts)
  paths=[REPO/p for p in sorted(bindings) if p.endswith('.py')][:16]
  with profiler:files=[contracts.regular(p)[0] for p in paths]
  result['actual_checkout_source_component']=dict(files=len(files),bytes=sum(r['bytes'] for r in files),
    profile=profiler.rows,qualification='Actual supplied source files, not hosted build inventory')
  # REPLACE the synthetic scope phase, never append another child/phase.
  receipt=load_source('ExactReceiptSave',HERE/'receipt_save.py',bindings)
  result['receipt_save']={}
  receipt.run(work/'receipt-save',work,HERE,ENGINE,REPO,bindings,contracts,result['receipt_save'])
  result['accepted']=True
 except BaseException as error:
  result['failure']=dict(type=type(error).__name__,message=str(error),traceback=traceback.format_exc(limit=12));raise
 finally:
  if old is None:sys.modules.pop('contracts',None)
  else:sys.modules['contracts']=old
  encoded=(json.dumps(result,separators=(',',':'),ensure_ascii=False)+'\n').encode()
  if len(encoded)>MAX_OUTPUT:raise RuntimeError('Diagnostic output bound exceeded; no success')
  fd=os.open(work/'result.json',os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
  with os.fdopen(fd,'wb') as f:f.write(encoded);f.flush();os.fsync(f.fileno())
 print('NONCOMPILER_DIFFERENTIAL_COMPONENTS_PASS')

if __name__=='__main__':
 if len(sys.argv)!=3 or sys.argv[1]!='--child' or not sys.flags.isolated or not sys.dont_write_bytecode:
  raise SystemExit('Reviewed isolated supervisor invocation required')
 fd=int(os.environ['LIGHTEFT_DIAGNOSTIC_LOCK_FD']);a=os.fstat(fd)
 b=Path(os.environ['LIGHTEFT_DIAGNOSTIC_LOCK_PATH']).lstat()
 if not stat.S_ISREG(a.st_mode) or (a.st_dev,a.st_ino)!=(b.st_dev,b.st_ino) or a.st_nlink!=1:
  raise SystemExit('Inherited diagnostic lease identity differs')
 if os.getsid(0)!=os.getpid() or os.getpgid(0)!=os.getpid():raise SystemExit('Isolated diagnostic session required')
 for name,value in [('RLIMIT_AS',12884901888),('RLIMIT_CPU',60),('RLIMIT_FSIZE',16*1024**2),('RLIMIT_CORE',0)]:
  if resource.getrlimit(getattr(resource,name))!=(value,value):raise SystemExit('Diagnostic kernel limit differs: '+name)
 main(Path(sys.argv[2]))
