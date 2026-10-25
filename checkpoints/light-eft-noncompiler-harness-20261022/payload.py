"""Finite non-compiler payload; no execution before independent review.

No subprocess, Lean/Lake/checker/audit, network or hosted-root reconstruction.
"""
from pathlib import Path
import contextlib, errno, hashlib, json, os, resource, stat, sys, time, traceback, types
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

def qualify_streaming_digest(work,bindings,contracts,result):
 """The exact production helper only; never its CI entry or producer route.

 Real-file hash checks are uninstrumented. Separate module-local reader probes
 observe one success and one synchronous read fault; they are not performance
 measurements or a proof about arbitrary faults, concurrent writers or schedules.
 """
 def need(ok,message):
  if not ok:raise RuntimeError('Streaming digest qualification: '+message)
 relative='checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci_gate.py'
 source=REPO/relative
 source_sha='72bb508e23dda4bf49cff9e06781ff1122adf299c0b68a50378499ee5ba154fe'
 compressed=HERE/'canonical-audit-ed86.receipt.json.gz'
 compressed_sha='acab398f6626ed13f0c3b3021fdf3e3d8e7e9b514e6e8a132985d6ea601e88db'
 sizes=(0,1,65535,65536,65537,131073)
 planned=sum(sizes)
 result.update(scope='EXACT_PRODUCTION_STREAMING_DIGEST_HELPER_ONLY',passed=False,
   qualification_acceptance=False,production_acceptance=False,
   whole_adapter_and_job_fit='UNMEASURED',phase='source and footprint admission',
   source=dict(path=relative,bytes=17927,sha256=source_sha),
   generated_sizes=list(sizes),generated_bytes=planned,cases=[],reader_probes=[])
 source_row,_=contracts.regular(source)
 need(source_row['bytes']==17927 and source_row['sha256']==source_sha and
   bindings[relative]==dict(path=relative,bytes=17927,sha256=source_sha),'production source pin')
 compressed_row,_=contracts.regular(compressed)
 need(compressed_row['bytes']==193510 and compressed_row['sha256']==compressed_sha and
   bindings[str(compressed.relative_to(REPO))]==dict(path=str(compressed.relative_to(REPO)),
     bytes=193510,sha256=compressed_sha),'existing compressed data pin')
 need(sys.getprofile() is None and planned==327682,'observer or fixed footprint differs')
 work=Path(work)
 need(work.is_absolute() and work.is_dir() and not work.is_symlink(),'owned work directory')
 for parent in work.parents:need(not parent.is_symlink(),'work parent symlink')
 existing=0
 for path in work.rglob('*'):
  info=path.lstat()
  if not stat.S_ISDIR(info.st_mode):
   need(stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode),'nonregular existing fixture')
   existing+=info.st_size
 # Use the same 32-MiB ceiling and 2-MiB metadata reserve as the unchanged
 # receipt phase. Its later, larger future-output reservation still runs too.
 need(existing+planned<=30*1024**2,'unchanged fixture allowance would overflow')
 root=work/'streaming-digest';root.mkdir(mode=0o700)
 result['fixture_budget']=dict(existing_bytes=existing,generated_bytes=planned,
   ceiling=32*1024**2,metadata_reserve=2*1024**2)
 module=load_source('FairBitDigestQualification_12892174',source,bindings)
 need(module.__name__=='FairBitDigestQualification_12892174' and
   module.__file__==str(source) and module.ROOT==REPO and
   module.digest.__code__.co_filename==str(source),'non-main production module identity')
 original_path=module.Path;original_digest=module.digest
 need(original_path is Path and module.hashlib is hashlib,'production helper globals')
 inputs=[];generated=0
 for size in sizes:
  path=root/('size-'+str(size)+'.bin')
  data=bytes(range(256))*(size//256)+bytes(range(size%256))
  need(len(data)==size,'fixed bytes length')
  fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
  with os.fdopen(fd,'wb') as output:output.write(data)
  generated+=size;inputs.append(('fixed-'+str(size),path,size,hashlib.sha256(data).hexdigest()))
 need(generated==planned,'generated footprint differs')
 inputs.extend([('bound-production-source',source,17927,source_sha),
   ('bound-existing-compressed-data',compressed,193510,compressed_sha)])
 result['phase']='uninstrumented fixed and bound-file cases'
 for name,path,size,expected in inputs:
  row,data=contracts.regular(path)
  baseline=hashlib.sha256(data).hexdigest()
  need(row['bytes']==size and baseline==expected,'baseline bytes/hash '+name)
  observed=module.digest(path)
  need(observed==expected,'production digest differs '+name)
  result['cases'].append(dict(case=name,bytes=size,expected_sha256=expected,
    actual_sha256=observed,plain_unobserved=True))
 large=root/'size-131073.bin';large_expected=next(x[3] for x in inputs if x[0]=='fixed-131073')
 def reader_probe(inject):
  opened=[];reads=[];exits=[];buffers=[];fault=OSError(errno.EIO,'bounded qualification read fault')
  class Reader:
   def __init__(self,raw):self.raw=raw
   def __enter__(self):self.raw.__enter__();return self
   def __exit__(self,kind,value,tb):
    try:return self.raw.__exit__(kind,value,tb)
    finally:exits.append(dict(exception=None if kind is None else kind.__name__,closed=self.raw.closed))
   def readinto(self,block):
    need(type(block) is bytearray and len(block)==65536,'readinto buffer type/size')
    if not buffers:buffers.append(block)
    need(block is buffers[0],'readinto did not reuse the same buffer')
    need(len(reads)<8,'finite read observation bound')
    entry=dict(buffer_bytes=len(block));reads.append(entry)
    if inject and len(reads)==2:
     entry['injected_errno']=errno.EIO;raise fault
    count=self.raw.readinto(block)
    need(type(count) is int and 0<=count<=len(block),'real readinto count')
    entry['returned']=count;return count
  class ProbePath:
   def __init__(self,path):
    self.path=Path(path);need(self.path==large,'probe escaped fixed owned case')
   def open(self,*args,**kwargs):
    need(not args and kwargs==dict(mode='rb') and not opened,'one exact binary open')
    raw=self.path.open(*args,**kwargs);opened.append(raw);return Reader(raw)
  caught=None;value=None
  # Only the newly loaded module's Path name is rebound, then restored even
  # on error. Shared pathlib/hashlib and production source bytes never change.
  try:
   module.Path=ProbePath
   try:value=module.digest(large)
   except OSError as error:
    if not inject:raise
    caught=error
  finally:module.Path=original_path
  need(len(opened)==1 and opened[0].closed and len(exits)==1 and exits[0]['closed'],
    'context manager did not close the real handle')
  if inject:
   need(caught is fault and len(reads)==2 and reads[0].get('returned',0)>0 and
     exits[0]['exception']=='OSError','read fault changed, retried or swallowed')
  else:
   need(value==large_expected and reads[-1].get('returned')==0 and
     sum(x['returned'] for x in reads)==131073 and exits[0]['exception'] is None,
     'observed success/EOF differs')
  return dict(case='read-error' if inject else 'successful-readinto',
    module_local_instrumentation=True,real_handle_closed=True,opens=len(opened),
    distinct_readinto_buffers=len(buffers),
    reads=reads,context_exit=exits[0],
    propagated_same_error=caught is fault if inject else None)
 result['phase']='finite handle and error observations'
 for inject in (False,True):result['reader_probes'].append(reader_probe(inject))
 missing=root/'never-created.bin'
 errors=[]
 for name,call in [('baseline',lambda:hashlib.sha256(missing.read_bytes()).hexdigest()),
                   ('production',lambda:module.digest(missing))]:
  try:call()
  except FileNotFoundError as error:
   need(error.errno==errno.ENOENT and error.filename==str(missing),'missing-file error differs')
   errors.append(dict(version=name,type=type(error).__name__,errno=error.errno))
  else:raise RuntimeError('Streaming digest qualification: missing file accepted')
 result['missing_file']=dict(observations=errors,matched=True)
 need(module.Path is original_path and module.digest is original_digest and
   module.hashlib is hashlib and sys.getprofile() is None,'helper binding/observer drift')
 need(contracts.bind(source)==source_row and contracts.bind(compressed)==compressed_row,
   'bound production/data input drift')
 result.update(phase='complete',limitations=[
   'Only the exact digest helper; no bound_spec, main, Lean or producer handoff executed',
   'Finite regular-file and synchronous error cases; not every read/error/concurrent schedule',
   'Module-local reader probes are instrumentation, not native performance measurements',
   'No total-RSS/pagecache benefit, actual populated roots, whole-adapter/job fit or final qualification'])
 need(len(json.dumps(result,separators=(',',':')).encode())<=64*1024,'helper result metadata cap')
 result['passed']=True

def main(work):
 bindings={r['path']:r for r in json.loads((HERE/'bindings.json').read_text())['files']}
 contracts=load_source('DiagnosticContracts',ENGINE/'contracts.py',bindings)
 old=sys.modules.get('contracts');sys.modules['contracts']=contracts
 result=dict(scope='NON_COMPILER_COMPONENT_DIAGNOSTIC',accepted=False,cases=[],
   hosted_full_job_savings_established=False,
   actual_populated_root_profile='UNAVAILABLE: no build/cache/compiler setup permitted',
   actual_receipt_IO_profile='Two exact isolated save bodies; one final shape and finite synchronous faults; no historical call-count or whole-job claim')
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
  result['streaming_digest']={}
  qualify_streaming_digest(work,bindings,contracts,result['streaming_digest'])
  # REPLACE the previous original-only receipt phase in the SAME guarded child.
  receipt=load_source('SaveDifferential',HERE/'save_differential.py',bindings)
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
