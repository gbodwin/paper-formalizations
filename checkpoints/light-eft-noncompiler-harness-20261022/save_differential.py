"""Frozen noncompiler differential of two isolated nested save definitions.
No production import, runner invocation, subprocess, historical-state reconstruction
or global json/os monkeypatch. Future execution requires independent admission.
"""
from pathlib import Path
import ast,errno,hashlib,io,json,os,stat,sys,time,traceback

BASE='c84a0cbb21a40edaa11c89e119ffad2a84321278537b7893465a796269c2dccb'
PROPOSED='9ac0305166036a1ccdbe8f0e21d47bc4f8461b47c93f7bc0bcefe0dec57d9c60'
PROPOSAL='checkpoints/light-eft-save-write-loop-proposal-20261023'
CASES=('success','encoder-type','encoder-circle','write-first','write-third','write-eintr','flush','file-fsync','rename','dir-open','dir-fsync','dir-close')
SEED=b'{"prior":true}\n'

def need(ok,why):
 if not ok:raise RuntimeError('Save differential: '+why)

def digest(data):return hashlib.sha256(data).hexdigest()

def load(name,path,bindings,repo,contracts):
 row,data=contracts.regular(path);bound=bindings[str(path.relative_to(repo))]
 need(row['bytes']==bound['bytes'] and row['sha256']==bound['sha256'],'unbound source '+name)
 namespace=dict(__name__=name,__file__=str(path));exec(compile(data,str(path),'exec'),namespace)
 return namespace

def definition(path,expected,bindings,repo,contracts):
 row,data=contracts.regular(path);bound=bindings[str(path.relative_to(repo))]
 need(row['sha256']==bound['sha256']==expected and row['bytes']==bound['bytes'],'runner snapshot differs')
 tree=ast.parse(data,filename=str(path))
 outer=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='run_child']
 need(len(outer)==1,'run_child count')
 saves=[x for x in outer[0].body if isinstance(x,ast.FunctionDef) and x.name=='save']
 need(len(saves)==1,'nested save count');node=saves[0]
 need(ast.dump(node.args)==ast.dump(ast.parse('def save(): pass').body[0].args) and not node.decorator_list,'save signature')
 factory=ast.parse('def factory(record,evidence):\n pass').body[0]
 factory.body=[node,ast.parse('return save').body[0]]
 code=compile(ast.fix_missing_locations(ast.Module(body=[factory],type_ignores=[])),str(path),'exec')
 lines={}
 for x in ast.walk(node):
  if isinstance(x,ast.Call) and isinstance(x.func,ast.Attribute) and x.func.attr=='write' and len(x.args)==1 and isinstance(x.args[0],ast.Constant) and x.args[0].value=='\n':lines['newline']=x.lineno
  if isinstance(x,ast.Call) and isinstance(x.func,ast.Name) and x.func.id=='write':lines['chunk']=x.lineno
 return code,lines,dict(path=str(path.relative_to(repo)),bytes=len(data),sha256=expected,save_AST_sha256=digest(ast.dump(node).encode()))

def instantiate(code,record,evidence,os_module=os):
 namespace=dict(json=json,os=os_module);exec(code,namespace)
 fn=namespace['factory'](record,evidence)
 need(fn.__code__.co_freevars==('evidence','record'),'closure authority differs')
 return fn

class Profile:
 """Candidate-aware bounded wall observer; chunks hashed at C write entry.
No full record/chunk list is buffered here. Python and C inclusive times overlap.
"""
 def __init__(self,save,lines,version):
  self.save=save;self.lines=lines;self.version=version;self.file=None
  # Reference iterator belongs ONLY to the observer. It directly checks every
  # chunk without materializing a record-sized encoding/chunk list. Its extra
  # encoding work is observer overhead, never plain timing or a saved state.
  setup=time.perf_counter_ns()
  record=dict(zip(save.__code__.co_freevars,(c.cell_contents for c in save.__closure__)))['record']
  self.expected=json.JSONEncoder(indent=2).iterencode(record);self.newline_checked=False
  self.reference_setup_ns=time.perf_counter_ns()-setup
  self.python={save.__code__:'save',json.dump.__code__:'dump',Path.open.__code__:'Path.open',
   json.JSONEncoder.__init__.__code__:'encoder.init',json.JSONEncoder.iterencode.__code__:'encoder.iterencode',
   json.encoder._make_iterencode.__code__:'encoder.make'}
  self.native={id(v):k for k,v in [('io.open',io.open),('os.open',os.open),('os.fsync',os.fsync),('os.replace',os.replace),('os.close',os.close)]}
  self.rows={};self.stack=[];self.fault=None;self.callback=self.event
  self.chunks=hashlib.sha256();self.count=0;self.bytes=0
 def event(self,frame,event,arg):
  try:self.observe(frame,event,arg)
  except BaseException as e:self.fault=repr(e)[:512];sys.setprofile(None)
 def observe(self,frame,event,arg):
  if event=='return' and frame.f_code is Path.open.__code__:
   need(type(arg) is io.TextIOWrapper and self.file is None,'ordinary text stream differs');self.file=arg
  if event in ('call','return'):
   label=self.python.get(frame.f_code);token=('py',id(frame))
  elif event in ('c_call','c_return','c_exception'):
   write=getattr(arg,'__self__',None) is self.file and self.file is not None and getattr(arg,'__name__',None)=='write'
   label='file.write' if write else self.native.get(id(arg));token=('write',id(frame)) if write else ('c',id(frame),id(arg))
   if write and event=='c_call':
    if frame.f_code is json.dump.__code__:
     need(self.version=='baseline' and frame.f_locals['fp'] is self.file,'dump write source');chunk=frame.f_locals['chunk']
    elif frame.f_code is self.save.__code__:
     if frame.f_lineno==self.lines['newline']:chunk='\n'
     else:
      need(self.version=='proposed' and frame.f_lineno==self.lines['chunk'],'candidate write source');chunk=frame.f_locals['chunk']
    else:raise RuntimeError('Unrecognized write caller')
    need(type(chunk) is str,'non-string chunk')
    try:expected=next(self.expected)
    except StopIteration:
     need(not self.newline_checked,'extra write after final newline');expected='\n';self.newline_checked=True
    need(chunk==expected,'direct ordered reference chunk differs')
    data=chunk.encode('utf-8')
    self.chunks.update(len(data).to_bytes(8,'big'));self.chunks.update(data);self.count+=1;self.bytes+=len(data)
  else:return
  if label is None:return
  now=time.perf_counter_ns()
  if event in ('call','c_call'):
   need(len(self.stack)<16,'observer depth');self.stack.append([token,label,now,0]);return
  need(self.stack and self.stack[-1][0]==token,'observer stack')
  _,label,start,nested=self.stack.pop();elapsed=now-start
  row=self.rows.setdefault(label,dict(calls=0,inclusive_ns=0,exclusive_ns=0));row['calls']+=1;row['inclusive_ns']+=elapsed;row['exclusive_ns']+=elapsed-nested
  if self.stack:self.stack[-1][3]+=elapsed
 def __enter__(self):
  need(sys.getprofile() is None,'profiler already active');self.start=time.perf_counter_ns();sys.setprofile(self.callback);return self
 def __exit__(self,kind,error,tb):
  if self.fault is None and sys.getprofile() is not self.callback:self.fault='observer replaced'
  sys.setprofile(None);self.end=time.perf_counter_ns()
  if kind is None:need(self.fault is None and not self.stack,'incomplete observer '+str(self.fault))
  return False
 def report(self):
  need(self.newline_checked,'missing final newline chunk')
  try:next(self.expected)
  except StopIteration:pass
  else:raise RuntimeError('Unconsumed reference chunks')
  expected={'save':1,'Path.open':1,'encoder.init':1,'encoder.iterencode':1,'encoder.make':1,
   'io.open':1,'os.open':1,'os.fsync':2,'os.replace':1,'os.close':1,'file.write':self.count}
  if self.version=='baseline':expected['dump']=1
  need(set(self.rows)==set(expected),'candidate-specific labels')
  for key,count in expected.items():need(self.rows[key]['calls']==count and 0<=self.rows[key]['exclusive_ns']<=self.rows[key]['inclusive_ns'],'observer counts '+key)
  return dict(elapsed_ns=self.end-self.start,rows=self.rows,ordered_chunk_sha256=self.chunks.hexdigest(),chunks=self.count,utf8_bytes=self.bytes,
   directly_compared_every_chunk=True,reference_encoder_setup_ns=self.reference_setup_ns,
   observer_overhead_included=True,attribution='Wall spans, not CPU/syscall timing; nested inclusive spans overlap; only selected exclusive times may be summed; plain timing has no observer')

class Injected(OSError):pass

class FaultIO:
 """Tiny fixtures only. Namespaces local to each extracted save, never globals.
Every injected failure is synchronous, before its specific delegated operation.
"""
 def __init__(self,path,case):
  self.path=path;self.case=case;self.events=[];self.writes=0;self.total=0;self.file=None;self.directory=None;self.directory_identity=None
  self.injected=InterruptedError(errno.EINTR,'bounded injected write') if case=='write-eintr' else Injected(errno.EIO,'bounded injected '+case)
  self.fired=0;self.facade=self.OS(self);self.evidence=self.Evidence(self)
 def event(self,*event):
  self.events.append(list(event));need(len(self.events)<=96 and len(json.dumps(self.events).encode())<=8192,'fault event cap')
 def hit(self,where):
  if self.case==where:
   self.fired+=1;need(self.fired==1,'fault retried');raise self.injected
 class Evidence:
  def __init__(self,c):self.c=c
  def __fspath__(self):return str(self.c.path)
  def __truediv__(self,name):
   need(name in ('receipt.tmp','receipt.json'),'unowned fault path')
   return FaultIO.Temp(self.c) if name=='receipt.tmp' else self.c.path/name
 class Temp:
  def __init__(self,c):self.c=c
  def __fspath__(self):return str(self.c.path/'receipt.tmp')
  def open(self,mode):
   need(mode=='w','fault open mode');self.c.event('open','receipt.tmp',mode)
   self.c.file=(self.c.path/'receipt.tmp').open(mode);return FaultIO.File(self.c)
 class File:
  def __init__(self,c):self.c=c
  def __enter__(self):self.c.file.__enter__();return self
  def __exit__(self,*args):self.c.event('file-exit',None if args[0] is None else args[0].__name__);return self.c.file.__exit__(*args)
  def fileno(self):return self.c.file.fileno()
  def write(self,chunk):
   c=self.c;need(type(chunk) is str,'fault chunk type');c.writes+=1;c.total+=len(chunk.encode())
   need(c.total<=4096,'tiny fault chunk budget');c.event('write',chunk)
   if c.writes==1:c.hit('write-first')
   if c.writes==3:c.hit('write-third');c.hit('write-eintr')
   return c.file.write(chunk)
  def flush(self):self.c.event('flush');self.c.hit('flush');return self.c.file.flush()
 class OS:
  O_RDONLY=os.O_RDONLY;O_DIRECTORY=os.O_DIRECTORY
  def __init__(self,c):self.c=c
  def fsync(self,fd):
   c=self.c;role='dir-fsync' if fd==c.directory else 'file-fsync'
   need(fd==c.directory or (c.file is not None and not c.file.closed and fd==c.file.fileno()),'unowned fsync')
   c.event(role);c.hit(role);return os.fsync(fd)
  def replace(self,src,dst):
   c=self.c;need(os.fspath(src)==str(c.path/'receipt.tmp') and dst==c.path/'receipt.json','rename authority')
   c.event('rename');c.hit('rename');return os.replace(src,dst)
  def open(self,path,flags):
   c=self.c;need(path is c.evidence and flags==os.O_RDONLY|os.O_DIRECTORY,'directory authority')
   c.event('dir-open');c.hit('dir-open');c.directory=os.open(c.path,flags)
   s=os.fstat(c.directory);c.directory_identity=(s.st_dev,s.st_ino);return c.directory
  def close(self,fd):
   c=self.c;need(fd==c.directory,'unowned directory close');c.event('dir-close');c.hit('dir-close')
   os.close(fd);c.directory=None
 def cleanup_owned(self):
  if self.file is not None and not self.file.closed:self.file.close()
  if self.directory is not None:
   s=os.fstat(self.directory);need((s.st_dev,s.st_ino)==self.directory_identity,'owned fixture FD changed')
   os.close(self.directory);self.directory=None

def sticky_function(repo,bindings,contracts):
 path=repo/'scripts/LightEFTProcessLifecycle.py';row,data=contracts.regular(path)
 need(row['sha256']==bindings[str(path.relative_to(repo))]['sha256']=='c77d6e9bd48de674aaa50852451627d09693fec7bdcca903a015fdab96f99fdd','sticky source')
 nodes=[x for x in ast.parse(data).body if isinstance(x,ast.FunctionDef) and x.name=='cleanup_error'];need(len(nodes)==1,'sticky definition')
 namespace=dict(os=os,time=time);exec(compile(ast.fix_missing_locations(ast.Module(body=nodes,type_ignores=[])),str(path),'exec'),namespace)
 return namespace['cleanup_error']

def fault_trial(code,path,case,sticky,owned_write):
 path.mkdir(mode=0o700);owned_write(path/'receipt.json',SEED)
 record={'first':'ok','next':[0,1,2]}
 if case=='encoder-type':record['bad']=object()
 if case=='encoder-circle':
  circular=[];circular.append(circular);record['bad']=circular
 controller=FaultIO(path,case);save=instantiate(code,record,controller.evidence,controller.facade);caught=None;trace=None
 try:
  try:save()
  except BaseException as e:
   caught=e;trace=''.join(traceback.format_exception(e)).encode();need(len(trace)<=8192,'fault traceback cap');owned_write(path/'traceback.txt',trace)
  if case=='success':need(caught is None and controller.fired==0,'tiny success failed')
  elif case in ('encoder-type','encoder-circle'):
   expected=TypeError if case=='encoder-type' else ValueError
   need(type(caught) is expected and controller.fired==0,'encoder failure differs')
   need(str(caught)==('Object of type object is not JSON serializable' if case=='encoder-type' else 'Circular reference detected'),'encoder error message')
  else:need(caught is controller.injected and controller.fired==1,'injected failure not propagated exactly once')
  snapshots={}
  for name in ('receipt.tmp','receipt.json'):
   p=path/name
   if p.exists():
    need(p.is_file() and not p.is_symlink(),'fault output type');data=p.read_bytes();need(len(data)<=4096,'fault output cap');snapshots[name]=dict(hex=data.hex(),sha256=digest(data))
   else:snapshots[name]=None
  after_rename=case in ('success','dir-open','dir-fsync','dir-close')
  need((snapshots['receipt.tmp'] is None)==after_rename,'failure atomic prefix')
  final=bytes.fromhex(snapshots['receipt.json']['hex'])
  need(final==(b'{\n  "first": "ok",\n  "next": [\n    0,\n    1,\n    2\n  ]\n}\n' if after_rename else SEED),'failure durable target bytes')
  sticky_rows=[]
  if caught is not None:
   for prior in (False,True):
    state={'failure':'earlier sticky failure'} if prior else {};persist=[]
    sticky('bounded-save-fixture',caught,state,lambda:persist.append(True))
    need(state['state']=='cleanup-error-lock-held' and len(state['cleanup_errors'])==1 and persist==[True],'sticky cleanup semantics')
    need(state['failure']==('earlier sticky failure' if prior else 'Cleanup/finalization failed; exclusion retained until recovery'),'sticky failure overwritten')
    state['cleanup_errors'][0].pop('monotonic_ns');sticky_rows.append(state)
  events=json.dumps(controller.events,separators=(',',':')).encode();owned_write(path/'events.json',events)
  return dict(case=case,exception=None if caught is None else dict(type=type(caught).__name__,message=str(caught),args=list(caught.args)),
   events=controller.events,outputs=snapshots,sticky=sticky_rows,traceback_sha256=None if trace is None else digest(trace),
   output_directory=path.name)
 finally:controller.cleanup_owned()

def run(root,work,here,engine,repo,bindings,contracts,result):
 need(sys.getprofile() is None,'unexpected observer')
 old=load('ReceiptDecode',here/'receipt_save.py',bindings,repo,contracts)
 runtime=load('SaveRuntimeContract',here/'save_runtime_contract.py',bindings,repo,contracts)
 pins_path=here/'save_runtime_contract.json';r,p=contracts.regular(pins_path);b=bindings[str(pins_path.relative_to(repo))]
 need(r['bytes']==b['bytes'] and r['sha256']==b['sha256'],'contract pin input')
 root=Path(root);work=Path(work)
 need(root.parent==work and work.is_dir() and not work.is_symlink(),'scratch ownership')
 for parent in work.absolute().parents:need(not parent.is_symlink(),'scratch symlink')
 existing=sum(p.lstat().st_size for p in work.rglob('*') if not stat.S_ISDIR(p.lstat().st_mode))
 reserved=existing+old['COMPRESSED_BYTES']+old['RAW_BYTES']+8*old['RAW_BYTES']+768*1024+256*1024
 need(reserved<=30*1024**2,'fixture+metadata reserve exceeds unchanged 32MiB')
 root.mkdir(mode=0o700);(root/'runtime-source').mkdir(mode=0o700)
 result.update(scope='FINAL_RECORD_TWO_SAVE_BODIES_AND_FINITE_SYNCHRONOUS_FAULTS',qualification_acceptance=False,
  fixture_reserved_bytes=reserved,metadata_reserve=2*1024**2,trials=[],faults=[],whole_job_fit='UNMEASURED')
 def progress(state):
  brief={k:v for k,v in result.items() if k not in ('faults','runtime')};brief['faults_completed']=len(result['faults'])
  data=(json.dumps(dict(state=state,result=brief),separators=(',',':'))+'\n').encode();need(len(data)<=64*1024,'progress cap')
  old['owned_write'](root/'progress.tmp',data);os.replace(root/'progress.tmp',root/'progress.json')
 progress('runtime contract before trials')
 contract=runtime['Contract'](json.loads(p),root/'runtime-source',contracts,sum(x['bytes'] for x in bindings.values()))
 data_path=here/old['INPUT_NAME'];row,data=contracts.regular(data_path);bound=bindings[str(data_path.relative_to(repo))]
 need(row['bytes']==bound['bytes']==old['COMPRESSED_BYTES'] and row['sha256']==bound['sha256']==old['COMPRESSED_SHA'],'compressed fixture pin')
 raw=old['decode'](data);old['owned_write'](root/'original-receipt.json',raw)
 parsed=json.loads(raw);need(type(parsed) is dict and parsed.get('source_commit')==old['HISTORICAL_SOURCE'] and parsed.get('stage')=='audit' and parsed.get('attempt_id')==old['HISTORICAL_ATTEMPT'] and parsed.get('state')=='finished' and parsed.get('exit')==0,'inert receipt provenance')
 definitions={}
 for version,filename,pin in [('baseline','BASELINE-child_runner.py',BASE),('proposed','PROPOSED-child_runner.py',PROPOSED)]:
  code,lines,binding=definition(repo/PROPOSAL/filename,pin,bindings,repo,contracts);definitions[version]=(code,lines);result.setdefault('sources',{})[version]=binding
 for kind in ('plain','profiled'):
  for version in ('baseline','proposed'):
   evidence=root/(kind+'-'+version);evidence.mkdir(mode=0o700);code,lines=definitions[version]
   save=instantiate(code,json.loads(raw),evidence);progress('before '+kind+' '+version)
   need(sys.getprofile() is None,'ordinary trial observer')
   observer=Profile(save,lines,version) if kind=='profiled' else None
   start=time.perf_counter_ns()
   if observer is None:save()
   else:
    with observer:save()
   elapsed=time.perf_counter_ns()-start
   output_row,output=contracts.regular(evidence/'receipt.json')
   need(output==raw and output_row['sha256']==old['RAW_SHA'],'complete output bytes differ')
   need(not (evidence/'receipt.tmp').exists() and not (evidence/'receipt.tmp').is_symlink(),'ordinary temporary remains')
   trial=dict(kind=kind,version=version,elapsed_ns=elapsed,bytes=len(output),sha256=digest(output),output=str(evidence.relative_to(work)),plain_unobserved=observer is None)
   if observer:
    trial['profile']=observer.report();need(trial['profile']['utf8_bytes']==len(raw),'ordered chunks byte coverage')
   result['trials'].append(trial);progress('verified '+kind+' '+version)
 profiled=[x['profile'] for x in result['trials'] if x['kind']=='profiled']
 need([(x['ordered_chunk_sha256'],x['chunks'],x['utf8_bytes']) for x in profiled][0]==[(x['ordered_chunk_sha256'],x['chunks'],x['utf8_bytes']) for x in profiled][1],'full ordered chunk stream differs')
 sticky=sticky_function(repo,bindings,contracts)
 for case in CASES:
  paired=[]
  for version in ('baseline','proposed'):
   progress('before fault '+case+' '+version)
   paired.append(fault_trial(definitions[version][0],root/('fault-'+case+'-'+version),case,sticky,old['owned_write']))
  # Traceback/source/output-directory identities legitimately differ; all bytes,
  # chunk order, fault prefix, exception and sticky semantic state must agree.
  comparable=lambda x:{k:v for k,v in x.items() if k not in ('traceback_sha256','output_directory')}
  need(comparable(paired[0])==comparable(paired[1]),'fault differential '+case)
  result['faults'].append(dict(case=case,paired=paired,semantic_equal=True));progress('verified fault '+case)
 result['runtime']=contract.finish()
 result.update(completed=True,limitations=['One final historical shape, not save frequency or historical total persistence cost','Bounded synchronous pre-operation faults only; no arbitrary asynchronous/allocation schedule equivalence','Sticky cleanup_error with successful synthetic persistence only; no real cleanup, lease mutation or persistence-failure stderr branch','No actual production context, 567 native replays, 36 proofs, whole-job fit or acceptance established'])
 progress('complete');return result
