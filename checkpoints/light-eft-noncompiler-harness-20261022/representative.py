"""Real metadata verification on explicitly synthetic bounded input families.

No Lean objects are parsed, compiled, resolved, replayed or audited. No runtime
toolchain/cache is installed. This is never a reconstructed historical context.
"""
from pathlib import Path
import ast, hashlib, json, os, sys, time, types

SCALES=(16,256,1024)
FAMILIES=('.olean','.ilean','.ir','.ir.sig')
FILE_BYTES=4096

class BorrowedLeaseView:
 """Read-only view of the SAME verified inherited lease; never unlocks it.

 Calls the unchanged CILease.check_filesystem implementation. Parent runner
 continues all original identity/resource/ownership checks independently.
 """
 def __init__(self,lease_type):
  self.path=Path(os.environ['LIGHTEFT_DIAGNOSTIC_LOCK_PATH'])
  self.file=os.fdopen(os.dup(int(os.environ['LIGHTEFT_DIAGNOSTIC_LOCK_FD'])),'r+')
  try:self.dirfd=os.open(self.path.parent,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
  except BaseException:self.file.close();raise
  try:s=os.fstat(self.file.fileno());d=os.fstat(self.dirfd)
  except BaseException:self.file.close();os.close(self.dirfd);raise
  self.identity=[s.st_dev,s.st_ino];self.directory=[d.st_dev,d.st_ino]
  self.parent=os.getppid();self.check_filesystem=lease_type.check_filesystem
 def check(self):
  if os.getppid()!=self.parent:raise RuntimeError('Diagnostic supervisor parent changed')
  self.check_filesystem(self)
 def close(self):self.file.close();os.close(self.dirfd)

def run(work,contracts,baseline,load_source,bindings,engine,profiler,result):
 # Sources must already be authenticated by the unchanged isolated supervisor.
 work.mkdir(mode=0o700)
 inventory=load_source('ProfileInventory',engine/'ci_inventory.py',bindings)
 lease_module=load_source('ProfileLease',engine/'ci_lease.py',bindings)
 focused=load_source('focused_audit',engine/'focused_audit.py',bindings)
 previous={k:sys.modules.get(k) for k in ['focused_audit','package_selection']}
 sys.modules['focused_audit']=focused;sys.modules['package_selection']=baseline
 lease=None
 try:
  scope=load_source('ProfileScope',engine/'scope.py',bindings)
  lease=BorrowedLeaseView(lease_module.CILease);lease.check()
  result.update(scope='CONTROLLED_SYNTHETIC_METADATA_CONTEXT',production_context=False,
   original_populated_roots='UNAVAILABLE: inherited production inputs not supplied',
   toolchain_shared_runtime_branch='UNAVAILABLE: no toolchain root is fabricated',
   actual_receipt_persistence='UNAVAILABLE: bound raw receipt input is not supplied',scales=[])
  def progress():
   # Retain completed phase data even on later timeout; no full map duplication.
   rows=[{k:v for k,v in r.items() if k!='ordered_selected'} for r in result['scales']]
   data=(json.dumps(dict(scope=result['scope'],scales=rows),separators=(',',':'))+'\n').encode()
   if len(data)>65536:raise RuntimeError('Bounded profile progress output exceeded')
   temp=work/'progress.tmp';dest=work/'progress.json'
   fd=os.open(temp,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
   with os.fdopen(fd,'wb') as f:f.write(data);f.flush();os.fsync(f.fileno())
   os.replace(temp,dest)
  functions={'scope.Context.verify':scope.Context.verify,'CIInventory.scan':inventory.CIInventory.scan,
   'contracts.unchanged':contracts.unchanged,'contracts.effective':contracts.effective,
   'contracts.regular':contracts.regular,'contracts.bind':contracts.bind,
   'package.validate':baseline.validate,'package.selected_path':baseline.selected_path}
  assert sum(SCALES)*len(FAMILIES)*FILE_BYTES<=32*1024**2
  for count in SCALES:
   report=dict(modules=count,state='setup');result['scales'].append(report);progress()
   folder=work/str(count);folder.mkdir();inputs=folder/'synthetic-inputs';inputs.mkdir()
   objects=folder/'empty-generated';objects.mkdir()
   target=objects/Path(*contracts.TARGET.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True)
   dependencies={}
   for i in range(count):
    module=('SyntheticA' if i%2==0 else 'SyntheticB')+'.M'+str(i)
    stem=inputs/Path(*module.split('.'));stem.parent.mkdir(exist_ok=True)
    for suffix in FAMILIES:
     with Path(str(stem)+suffix).open('xb') as f:f.write(b'NOT A LEAN OBJECT\n'.ljust(FILE_BYTES,b'x'))
    dependencies[module]=dict(contracts.bind(Path(str(stem)+'.olean')),module=module)
   inv=inventory.CIInventory([inputs],folder/'not-a-toolchain',contracts.bind)
   classified=inv.scan()
   journal=folder/'inputs.jsonl';excluded=folder/'excluded.jsonl'
   scope.Context.write_metadata(None,journal,classified['semantic'])
   scope.Context.write_metadata(None,excluded,classified['excluded'])
   ctx=scope.Context();ctx.lease=lease;ctx.inputs=classified['semantic'];ctx.new={};ctx.resolved={}
   ctx.input_ref=contracts.bind(journal);ctx.excluded_ref=contracts.bind(excluded)
   ctx.inventory_policy=inv;ctx.members=classified['members'];ctx.roots=[objects,inputs]
   ctx.dependencies=dependencies;ctx.target=target
   # Exact original method, once plain and once observed, on one immutable set.
   started=time.perf_counter_ns();plain=ctx.verify(False);plain_ns=time.perf_counter_ns()-started
   plain_map=list(ctx.package_selection['selected'].items())
   report.update(state='plain complete',plain_verify_ns=plain_ns);progress()
   collector=profiler.Collector(functions)
   try:
    with collector:observed=ctx.verify(False)
   except BaseException as error:
    report.update(state='component failed',exception_type=type(error).__name__,message=str(error),observer_fault=collector.fault)
    progress();raise
   observed_map=list(ctx.package_selection['selected'].items())
   if plain is not None or observed is not None or plain_map!=observed_map:
    raise RuntimeError('Original Context.verify outcome/ordered selection changed')
   report.update(state='complete',semantic_files=count*len(FAMILIES),
    fixture_bytes=count*len(FAMILIES)*FILE_BYTES,profile=collector.snapshot(),
    fixture_root=str(folder),ordered_selected=[(m,str(Path(p).relative_to(folder))) for m,p in plain_map],
    ordered_maps_equal=True,
    ordered_map_sha256=hashlib.sha256(json.dumps(plain_map,separators=(',',':')).encode()).hexdigest(),
    qualification='Actual original verify/scan/bind/effective methods; synthetic filesystem bytes and membership only')
   progress()
  return result
 finally:
  if lease is not None:lease.close()
  for key,value in previous.items():
   if value is None:sys.modules.pop(key,None)
   else:sys.modules[key]=value

def receipt_save_component(source,source_sha,receipt,receipt_sha,evidence,contracts,profiler):
 """Optional read-only supplied receipt shape; not wired without bound input.

 Extracts the EXACT nested run_child.save AST body. Historical path/identity
 fields remain uninterpreted data. Only evidence (new owned scratch) is written.
 """
 _,raw=contracts.regular(source)
 if hashlib.sha256(raw).hexdigest()!=source_sha:raise RuntimeError('Unbound runner source')
 row,data=contracts.regular(receipt)
 if row['sha256']!=receipt_sha or len(data)>16*1024**2:raise RuntimeError('Unavailable/unbounded exact receipt input')
 parsed=json.loads(data);tree=ast.parse(raw,filename=str(source))
 outer=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='run_child')
 save=next(n for n in outer.body if isinstance(n,ast.FunctionDef) and n.name=='save')
 if save.decorator_list or save.args.args or save.args.posonlyargs or save.args.kwonlyargs or save.args.vararg or save.args.kwarg:
  raise RuntimeError('Unexpected actual save signature')
 if any(p.is_symlink() for p in evidence.absolute().parents):raise RuntimeError('Symlink receipt-output ancestor')
 evidence.mkdir(mode=0o700)
 ns=dict(record=parsed,evidence=evidence,json=json,os=os)
 exec(compile(ast.Module(body=[save],type_ignores=[]),str(source),'exec'),ns)
 functions={'runner.save':ns['save'],'json.dump':json.dump,'contracts.regular':contracts.regular}
 collector=profiler.Collector(functions)
 with collector:ns['save']()
 output=(evidence/'receipt.json').read_bytes()
 if output!=data:raise RuntimeError('Re-encoded actual receipt differs; not a faithful save-shape measurement')
 return dict(bytes=len(output),profile=collector.snapshot(),exact_bytes_equal=True,
  qualification='One exact final-record save shape only; not historical call count, intermediate states or full receipt-work cost')
