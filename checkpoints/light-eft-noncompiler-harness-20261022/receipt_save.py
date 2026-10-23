"""Bounded inert receipt expansion and exact final-record persistence cost.

SOURCE PROPOSAL ONLY. Never authenticates a native stage or historical lease.
No compiler, runner import, subprocess, network, toolchain or object loading.
"""
from pathlib import Path
import ast,hashlib,io,json,os,stat,sys,time,zlib

COMPRESSED_BYTES=193510
COMPRESSED_SHA='acab398f6626ed13f0c3b3021fdf3e3d8e7e9b514e6e8a132985d6ea601e88db'
RAW_BYTES=2585054
RAW_SHA='3d5bdae23f840b8e840f7a763b06572b996f9965e8dc172ba7dfa5ed6ba9d555'
SOURCE_SHA='c84a0cbb21a40edaa11c89e119ffad2a84321278537b7893465a796269c2dccb'
HISTORICAL_SOURCE='ed86a6e8a5fc62e7d807b10dca43669f3cd848a6'
HISTORICAL_ATTEMPT='70abff84960944f49cae97c845c69810'
INPUT_NAME='canonical-audit-ed86.receipt.json.gz'
FIXTURE_CEILING=32*1024**2
METADATA_RESERVE=2*1024**2
PROGRESS_CEILING=64*1024

def require(ok,message):
 if not ok:raise RuntimeError(message)

def digest(data):return hashlib.sha256(data).hexdigest()

def owned_write(path,data):
 fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
 with os.fdopen(fd,'wb') as f:f.write(data);f.flush();os.fsync(f.fileno())

def decode(data):
 """One complete gzip member only, bounded BEFORE parsing JSON or writing raw."""
 require(len(data)==COMPRESSED_BYTES and digest(data)==COMPRESSED_SHA,'Compressed receipt bytes/hash differ')
 decoder=zlib.decompressobj(16+zlib.MAX_WBITS)
 raw=decoder.decompress(data,RAW_BYTES+1)
 require(len(raw)==RAW_BYTES,'Exact bounded decompressed length differs')
 # No flush(), unbounded expansion, second member, suffix, padding or truncation.
 # With one extra output byte of capacity, eof confirms the trailer was consumed
 # and zlib already checked CRC/ISIZE. Any buffered input or suffix rejects.
 require(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail,
         'Incomplete/concatenated/trailing gzip stream')
 require(digest(raw)==RAW_SHA,'Decompressed receipt hash differs')
 return raw

class ReceiptProfile:
 """Selected Python-frame and builtin C-call WALL times, not CPU/syscall time.

 Unregistered native work, including writes/buffering/flush/stream close, stays
 inside its selected Python caller's exclusive time. It is NOT native-free
 Python CPU. Nested inclusive durations must never be added to their parents.
 """
 def __init__(self,save):
  self.python={save.__code__:'python.runner.save',json.dump.__code__:'python.json.dump',
               Path.open.__code__:'python.Path.open'}
  self.native={id(fn):label for label,fn in [
   ('c.io.open',io.open),('c.os.open',os.open),('c.os.fsync',os.fsync),
   ('c.os.replace',os.replace),('c.os.close',os.close)]}
  self.stack=[];self.rows={};self.fault=None;self.callback=self.event
  self.started=None;self.finished=None
 def event(self,frame,event,arg):
  try:self.observe(frame,event,arg)
  except BaseException as error:
   self.fault=type(error).__name__+': '+str(error)[:512];sys.setprofile(None)
 def observe(self,frame,event,arg):
  if event in ['call','return']:
   label=self.python.get(frame.f_code);token=('python',id(frame))
  elif event in ['c_call','c_return','c_exception']:
   label=self.native.get(id(arg));token=('c',id(frame),id(arg))
  else:return
  if label is None:return
  now=time.perf_counter_ns()
  if event in ['call','c_call']:
   require(len(self.stack)<16,'Receipt profile nesting bound')
   self.stack.append([token,label,now,0]);return
  require(self.stack and self.stack[-1][0]==token,'Receipt profile stack mismatch')
  _,label,start,nested=self.stack.pop();elapsed=now-start
  row=self.rows.setdefault(label,dict(calls=0,inclusive_ns=0,exclusive_ns=0))
  row['calls']+=1;row['inclusive_ns']+=elapsed;row['exclusive_ns']+=elapsed-nested
  if self.stack:self.stack[-1][3]+=elapsed
 def __enter__(self):
  require(sys.getprofile() is None,'Existing profiler; refuse replacement')
  self.started=time.perf_counter_ns();sys.setprofile(self.callback);return self
 def __exit__(self,kind,error,tb):
  if self.fault is None and sys.getprofile() is not self.callback:self.fault='Profile callback replaced'
  sys.setprofile(None);self.finished=time.perf_counter_ns()
  if self.stack:self.fault=self.fault or 'Unclosed receipt profile frames'
  if kind is None:require(self.fault is None,'Incomplete receipt profile: '+str(self.fault))
  return False
 def snapshot(self):
  require(self.fault is None and self.finished is not None,'No complete receipt profile')
  expected={'python.runner.save':1,'python.json.dump':1,'python.Path.open':1,
            'c.io.open':1,'c.os.open':1,'c.os.fsync':2,'c.os.replace':1,'c.os.close':1}
  require(set(self.rows)==set(expected),'Missing/extra selected receipt profile labels')
  for label,count in expected.items():
   row=self.rows[label]
   require(row['calls']==count and 0<=row['exclusive_ns']<=row['inclusive_ns'],
           'Incomplete receipt profile counts/time: '+label)
  return dict(elapsed_ns=self.finished-self.started,rows=self.rows,
   observer_overhead_included=True,unit='wall-clock nanoseconds',
   attribution='Selected Python spans include unregistered native work; C-call spans include call latency, not isolated kernel/syscall CPU; exclusive selected spans only are additive')

def save_code(source,bindings,repo,contracts):
 row,data=contracts.regular(source);expected=bindings[str(source.relative_to(repo))]
 require(row['bytes']==expected['bytes'] and row['sha256']==expected['sha256']==SOURCE_SHA,
         'Unbound original runner source')
 tree=ast.parse(data,filename=str(source))
 outer=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='run_child']
 require(len(outer)==1,'Original run_child definition differs')
 nested=[n for n in outer[0].body if isinstance(n,ast.FunctionDef) and n.name=='save']
 require(len(nested)==1,'Original receipt save definition differs')
 node=nested[0];args=node.args
 require(not node.decorator_list and not args.args and not args.posonlyargs and
         not args.kwonlyargs and not args.vararg and not args.kwarg and
         not args.defaults and not args.kw_defaults,'Original receipt save signature differs')
 # Retain record/evidence as closure cells, as in the original nested save.
 # The tiny factory only binds data/owned output and returns the unchanged AST
 # body. Never import/execute run_child, its module or any launcher.
 factory=ast.parse('def _exact_receipt_save_factory(record,evidence):\n pass\n').body[0]
 returned=ast.parse('return save').body[0]
 factory.body=[node,returned]
 module=ast.fix_missing_locations(ast.Module(body=[factory],type_ignores=[]))
 return compile(module,str(source),'exec')

def run(root,work,here,engine,repo,bindings,contracts,result):
 require(sys.getprofile() is None,'Receipt plain path requires no profiler')
 root=Path(root);work=Path(work)
 require(root.parent==work and work.is_dir() and not work.is_symlink(),'Unowned receipt scratch parent')
 for p in work.absolute().parents:require(not p.is_symlink(),'Receipt scratch ancestor symlink')
 # Count pre-existing package fixtures (including inert owned links) without
 # following links or any historical receipt path. Count compressed input too.
 existing=0
 for p in work.rglob('*'):
  st=p.lstat()
  if not stat.S_ISDIR(st.st_mode):existing+=st.st_size
 planned=existing+COMPRESSED_BYTES+RAW_BYTES+4*RAW_BYTES
 require(planned<=FIXTURE_CEILING-METADATA_RESERVE,'Existing receipt fixture budget exceeded')
 root.mkdir(mode=0o700)
 result.update(scope='EXACT_FINAL_PRODUCTION_RECEIPT_SAVE_SHAPE',production_acceptance=False,
  fixture_budget=dict(existing_bytes=existing,conservative_reserved_bytes=planned,
   ceiling=FIXTURE_CEILING,metadata_reserve=METADATA_RESERVE,outputs_charged_tmp_plus_final_per_trial=True),
  actual_context_and_whole_job_savings='UNMEASURED',trials=[])
 def progress(state):
  data=(json.dumps(dict(state=state,result=result),separators=(',',':'))+'\n').encode()
  require(len(data)<=PROGRESS_CEILING,'Receipt progress bound')
  temp=root/'progress.tmp'
  owned_write(temp,data);os.replace(temp,root/'progress.json')
 progress('before exact bounded decode')
 compressed=here/INPUT_NAME;row,data=contracts.regular(compressed)
 bound=bindings[str(compressed.relative_to(repo))]
 require(row['bytes']==bound['bytes']==COMPRESSED_BYTES and
         row['sha256']==bound['sha256']==COMPRESSED_SHA,'Unbound compressed receipt input')
 raw=decode(data)  # Exact length/hash/EOF validation completes BEFORE JSON.
 owned_write(root/'original-receipt.json',raw)
 parsed=json.loads(raw)
 require(type(parsed) is dict and parsed.get('source_commit')==HISTORICAL_SOURCE and
         parsed.get('stage')=='audit' and parsed.get('attempt_id')==HISTORICAL_ATTEMPT and
         parsed.get('state')=='finished' and parsed.get('exit')==0,
         'Final production receipt provenance differs')
 result['input']=dict(compressed_bytes=COMPRESSED_BYTES,compressed_sha256=COMPRESSED_SHA,
  raw_bytes=RAW_BYTES,raw_sha256=RAW_SHA,historical_source=HISTORICAL_SOURCE,
  historical_child_attempt=HISTORICAL_ATTEMPT,historical_paths_and_environment='INERT DATA; never current authority or I/O paths')
 code=save_code(engine/'child_runner.py',bindings,repo,contracts)
 for label in ['plain','profiled']:
  evidence=root/label;evidence.mkdir(mode=0o700)
  # Fresh parsed data and globals for EACH invocation; only original save runs.
  namespace=dict(json=json,os=os)
  exec(code,namespace)
  save=namespace['_exact_receipt_save_factory'](json.loads(raw),evidence)
  require(save.__code__.co_freevars==('evidence','record'),'Original receipt closure cells differ')
  progress('before '+label+' original save')
  require(sys.getprofile() is None,'Unexpected profiler before receipt invocation')
  collector=ReceiptProfile(save) if label=='profiled' else None
  started=time.perf_counter_ns()
  if collector is None:save()
  else:
   with collector:save()
  elapsed=time.perf_counter_ns()-started
  require(sys.getprofile() is None,'Unexpected profiler after receipt invocation')
  observed,output=contracts.regular(evidence/'receipt.json')
  require(output==raw and observed['bytes']==RAW_BYTES and observed['sha256']==RAW_SHA,
          'Original save did not reproduce complete exact receipt bytes')
  require(not (evidence/'receipt.tmp').exists() and not (evidence/'receipt.tmp').is_symlink(),
          'Receipt save temp output remains')
  trial=dict(kind=label,elapsed_ns=elapsed,complete_bytes_equal=True,bytes=observed['bytes'],
   sha256=observed['sha256'],output=str((evidence/'receipt.json').relative_to(work)),
   profiling_enabled=collector is not None)
  if collector is not None:trial['profile']=collector.snapshot()
  result['trials'].append(trial);progress(label+' exact bytes verified')
 require([x['kind'] for x in result['trials']]==['plain','profiled'],'Incomplete receipt trials')
 result.update(completed=True,qualification='One final-record save per fresh output directory; not historical call count/intermediate states/total persistence cost or full-job fit')
 progress('complete');return result
