"""Bounded source-proposal diagnostic, never a native production plan.

Actual initialized constructors and verification methods run only on inert
owned fixture bytes. No process launch, toolchain/cache or kernel/audit work.
"""
from pathlib import Path
import hashlib,json,os,sys,time,traceback

SCALES=(256,1024)
FILE_BYTES=2048
FAMILIES=('.olean','.ilean','.ir','.ir.sig')
PROPOSAL='checkpoints/light-eft-semantic-reuse-proposal-20261023'

class FatalLeaseFault(BaseException):pass
class ControlledFault(RuntimeError):pass

class Budget:
 def __init__(self,existing):
  self.bytes=sum(p.lstat().st_size for p in existing.rglob('*') if p.is_file() and not p.is_symlink())
  self.check()
 def check(self):
  # Reserve 2 MiB for bounded final/progress/receipt metadata. No larger budget.
  if self.bytes>30*1024**2:raise RuntimeError('Prior 32-MiB fixture envelope exceeded')
 def write(self,path,data):
  self.bytes+=len(data);self.check();path.parent.mkdir(parents=True,exist_ok=True)
  fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_TRUNC|os.O_NOFOLLOW,0o600)
  with os.fdopen(fd,'wb') as f:f.write(data)
 def journal(self,path):self.bytes+=path.stat().st_size;self.check()

class CheckedLease:
 """Real inherited checks first; simulated failures never mask real failures."""
 def __init__(self,view,packet):
  self.view=view;self.file=view.file;self.acquired_ns=packet['acquired_ns'];self.record=packet
  self.calls=0;self.fail_after=None
 def check(self):
  try:self.view.check()
  except BaseException as error:raise FatalLeaseFault('Actual inherited lease failed') from error
  self.calls+=1
  if self.fail_after is not None and self.calls>=self.fail_after:
   raise ControlledFault('Injected final lease failure after real check')

CASES=[
 'valid','semantic-input-digest','semantic-input-missing','semantic-original-digest',
 'critical-extra','runtime-shape-valid','excluded-metadata','unknown-family','orphan-family','missing-runtime',
 'input-journal','excluded-journal','compiled-new','new-object-drift','resolved','resolved-drift','members-authority',
 'root-shadow','package-mask','target-prefix','dependency-leaf','physical-leaf-missing','inventory-none',
 'persistent-content','persistent-member','final-seal','final-lease',
 'admission-0','admission-1','admission-2']
STRENGTHENED={'persistent-content','persistent-member','final-seal','final-lease'}
VALID={'valid','runtime-shape-valid','compiled-new','resolved','inventory-none','admission-0','admission-1','admission-2'}

def run(root,contracts,baseline_package,load_source,bindings,repo,engine,profiler,representative,result):
 root.mkdir(mode=0o700);budget=Budget(root.parent)
 # Module registry changes are private to this child and restored on every exit.
 names=['focused_audit','package_selection','ci_inventory','ci_policy','ci_handoff_contract','output_guards']
 previous={n:sys.modules.get(n) for n in names};view=None
 try:
  for n in ['focused_audit','ci_inventory','ci_policy','ci_handoff_contract','output_guards']:
   sys.modules[n]=load_source(n,engine/(n+'.py'),bindings)
  sys.modules['package_selection']=baseline_package
  inventory=sys.modules['ci_inventory'];gate=load_source('DiagnosticFactory',engine/'ci_gate.py',bindings)
  admission=load_source('DiagnosticAdmissions',engine/'ci_admission.py',bindings)
  lease_module=load_source('DiagnosticLease',engine/'ci_lease.py',bindings)
  scopes=[load_source('BaselineScope',repo/PROPOSAL/'BASELINE-scope.py',bindings),
          load_source('ProposedScope',repo/PROPOSAL/'PROPOSED-scope.py',bindings)]
  identity=json.loads(os.environ['LIGHTEFT_DIAGNOSTIC_IDENTITY'])
  packet=json.loads(os.environ['LIGHTEFT_DIAGNOSTIC_LEASE'])
  view=representative.BorrowedLeaseView(lease_module.CILease);view.check()
  if (packet['path']!=str(view.path) or [packet['device'],packet['inode']]!=view.identity or
      packet['supervisor_pid']!=os.getppid() or packet['state']!='held'):
   raise FatalLeaseFault('Transported actual lease authority differs')
  result.update(scope='SEMANTIC_REUSE_DIFFERENTIAL',production_acceptance=False,
   actual_populated_roots='UNAVAILABLE',native_authentication_and_kernel_paths='NOT EXECUTED',
   package_prefix_optimization='NOT INTEGRATED; original package implementation used',cases=[],scales=[])

  def persist():
   # Full maps/tracebacks stay in final result. Bounded partial progress retains
   # outcomes, map hashes, counts and profiles, not per-event logs.
   def small(v):
    if isinstance(v,dict):return {k:small(x) for k,x in v.items() if k not in ['ordered','traceback']}
    if isinstance(v,list):return [small(x) for x in v]
    return v
   data=(json.dumps(small(result),separators=(',',':'))+'\n').encode()
   if len(data)>65536:raise RuntimeError('64-KiB differential progress bound')
   temp=root/'progress.tmp';fd=os.open(temp,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
   with os.fdopen(fd,'wb') as f:f.write(data);f.flush();os.fsync(f.fileno())
   os.replace(temp,root/'progress.json')

  def prepare(scope,folder,count,case):
   folder.mkdir();work=folder/'work';work.mkdir();evidence=folder/'runtime';evidence.mkdir()
   objects=work/'objects';objects.mkdir();inputs=folder/'inputs';inputs.mkdir()
   runtime_shape=case in ['runtime-shape-valid','excluded-metadata','missing-runtime','orphan-family']
   tool=folder/'inert-runtime-shape' if runtime_shape else folder/'not-a-toolchain'
   if runtime_shape:inputs=tool/'lib/lean';inputs.mkdir(parents=True)
   modules=[('SyntheticA' if i%2==0 else 'SyntheticB')+'.M'+str(i) for i in range(count)]
   if case.startswith('admission-'):modules.append(admission.CONTRACT['replay_order'][int(case[-1])])
   deps={}
   for m in modules:
    stem=inputs/Path(*m.split('.'))
    for suffix in FAMILIES:budget.write(Path(str(stem)+suffix),b'INERT NOT LEAN\n'.ljust(FILE_BYTES,b'x'))
    deps[m]=dict(contracts.bind(Path(str(stem)+'.olean')),module=m)
   if runtime_shape:
    for n in sorted(inventory.RUNTIME_SHARED):budget.write(inputs/n,b'INERT NOT A SHARED LIBRARY\n')
    budget.write(inputs/'libLean.a',b'INERT NOT AN ARCHIVE\n')
    budget.write(inputs/Path(*modules[0].split('.')).with_suffix('.olean.hash'),b'fixture metadata\n')
   if case=='orphan-family':budget.write(inputs/'Orphan.ir',b'inert orphan\n')
   if case=='missing-runtime':(inputs/sorted(inventory.RUNTIME_SHARED)[0]).unlink()
   inv=inventory.CIInventory([inputs],tool,contracts.bind)
   # These two classifier cases intentionally reject before any context exists.
   classified=inv.scan()
   critical=work/'critical.json';budget.write(critical,b'{"fixture":true}\n')
   bound={**classified['semantic'],str(critical):contracts.bind(critical)}
   roots=[objects,inputs];target=objects/Path(*contracts.TARGET.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True)
   is_admission=case.startswith('admission-');module=admission.CONTRACT['replay_order'][int(case[-1])] if is_admission else contracts.TARGET
   stages=['replay'] if is_admission else list(contracts.STAGES)
   # Constructor-shape witnesses only: no stage/preexec/runner is called.
   commands=[dict(stage=s,module=module,argv=[str(work/'NEVER_EXECUTED'/'leanchecker'),'-v',module]
     if is_admission else ['NONLAUNCHABLE_DIAGNOSTIC_METADATA',s],env={},sources=[],source_bindings=[],cwd=str(work)) for s in stages]
   owner=CheckedLease(view,packet)
   typ=gate.context_type(scope.Context,work,evidence,commands,roots,deps,identity,bound,
     None if case=='inventory-none' else inv,classified,contracts.bind,
     **({'admission_module':module} if is_admission else {}))
   if is_admission:typ=admission.context_type(typ,module,Path(deps[module]['path']))
   ctx=typ(owner)
   budget.journal(ctx.input_ref['path'] if isinstance(ctx.input_ref['path'],Path) else Path(ctx.input_ref['path']))
   budget.journal(Path(ctx.excluded_ref['path']))
   primary=Path(deps[modules[0]]['path']);side=primary.with_suffix('.ir')
   compiled=case in ['compiled-new','new-object-drift','resolved','resolved-drift']
   if compiled:
    budget.write(target,b'INERT COMPILED-OUTPUT SHAPE\n');ctx.new[str(target)]=contracts.bind(target)
   if case in ['resolved','resolved-drift']:
    budget.write(ctx.resolution,(json.dumps(dict(target=contracts.TARGET,count=1,resolved=[dict(module=contracts.TARGET,object=str(target))],search_path=list(map(str,roots))))+'\n').encode())
    ctx.resolved[str(ctx.resolution)]=contracts.bind(ctx.resolution)
   if case=='semantic-input-digest':ctx.inputs[str(side)]=dict(ctx.inputs[str(side)],sha256='0'*64)
   elif case=='semantic-input-missing':ctx.inputs.pop(str(side))
   elif case=='semantic-original-digest':inv.original['semantic'][str(side)]=dict(inv.original['semantic'][str(side)],sha256='0'*64)
   elif case=='critical-extra':budget.write(critical,b'changed critical\n')
   elif case=='excluded-metadata':budget.write(inputs/'libLean.a',b'changed excluded metadata\n')
   elif case=='unknown-family':budget.write(inputs/'Unknown.bin',b'unknown\n')
   elif case=='input-journal':budget.write(Path(ctx.input_ref['path']),b'changed journal\n')
   elif case=='excluded-journal':budget.write(Path(ctx.excluded_ref['path']),b'changed excluded journal\n')
   elif case=='new-object-drift':budget.write(target,b'changed generated shape\n')
   elif case=='resolved-drift':budget.write(ctx.resolution,b'changed resolution\n')
   elif case=='members-authority':ctx.members={k:set(v)-{str(side)} for k,v in ctx.members.items()}
   elif case=='root-shadow':budget.write(objects/Path(*modules[0].split('.')).with_suffix('.olean'),b'shadow\n')
   elif case=='package-mask':(objects/modules[0].split('.')[0]).mkdir()
   elif case=='target-prefix':budget.write(objects/Path(*contracts.TARGET.split('.'))/'Child.olean',b'prefix\n')
   elif case=='dependency-leaf':ctx.dependencies[modules[0]]=dict(deps[modules[0]],path=str(work/'missing.olean'))
   elif case=='physical-leaf-missing':primary.unlink()
   enumeration=[str(p.relative_to(folder)) for r in roots for p in r.rglob('*.olean')]
   return dict(ctx=ctx,owner=owner,compiled=compiled,folder=folder,primary=primary,side=side,inputs=inputs,
     enumeration=enumeration,semantic=len(classified['semantic']),critical=1,new=len(ctx.new),resolved=len(ctx.resolved))

  def invoke(scope,f,case,expected,profile=False):
   original_effective=scope.effective;original_seal=inventory.CIIdentityGuard.verify
   ctx=f['ctx'];owner=f['owner'];owner.calls=0;mutation_done=False
   if case=='final-lease':owner.fail_after=2
   def effective(*args,**kwargs):
    nonlocal mutation_done
    value=original_effective(*args,**kwargs)
    if case=='persistent-content':budget.write(f['side'],b'persistent changed bytes\n')
    elif case=='persistent-member':budget.write(f['inputs']/'Added.ir',b'late member\n')
    mutation_done=True
    return value
   def seal(self):original_seal(self);raise ControlledFault('Injected final seal failure after real check')
   if case in ['persistent-content','persistent-member']:scope.effective=effective
   if case=='final-seal':inventory.CIIdentityGuard.verify=seal
   functions={'scope.Context.verify':scope.Context.verify,'CIInventory.scan':inventory.CIInventory.scan,
    'contracts.unchanged':contracts.unchanged,'contracts.effective':contracts.effective,
    'contracts.regular':contracts.regular,'contracts.bind':contracts.bind,
    'seal.entry':inventory.CIIdentityGuard.__init__,'seal.snapshot':inventory.CIIdentityGuard.snapshot,
    'seal.final':inventory.CIIdentityGuard.verify}
   collector=profiler.Collector(functions);start=time.perf_counter_ns()
   try:
    try:
     if profile:
      with collector:value=ctx.verify(f['compiled'])
     else:value=ctx.verify(f['compiled'])
     ended=time.perf_counter_ns()
    except (contracts.Rejected,ValueError,FileNotFoundError,ControlledFault) as error:
     ended=time.perf_counter_ns()
     if isinstance(error,FileNotFoundError) and (case!='physical-leaf-missing' or error.errno!=2 or error.filename!=str(f['primary'])):raise
     if case in ['final-seal','final-lease'] and not isinstance(error,ControlledFault):raise
     if case in ['persistent-content','persistent-member'] and not mutation_done:raise
     trace=traceback.format_exc().encode()
     if len(trace)>16384:raise RuntimeError('Expected-rejection traceback bound; no truncation')
     trace_path=root/'traces'/(f['folder'].name+'.txt');budget.write(trace_path,trace)
     answer=dict(status='reject',type=type(error).__name__,module=type(error).__module__,
       message=str(error),traceback_file=str(trace_path.relative_to(root)),
       traceback_sha256=hashlib.sha256(trace).hexdigest(),traceback_bytes=len(trace))
    else:
     if value is not None:raise RuntimeError('Unexpected verification return')
     ordered=list(ctx.package_selection['selected'].items())
     answer=dict(status='accept',ordered=[(m,str(Path(p).relative_to(f['folder']))) for m,p in ordered],
       raw_ordered_sha256=hashlib.sha256(json.dumps(ordered,separators=(',',':')).encode()).hexdigest())
    answer.update(elapsed_ns=ended-start,real_lease_checks=owner.calls)
    if profile:answer['profile']=collector.snapshot()
    if answer['status']!=expected:raise RuntimeError('Unexpected '+case+' outcome: '+answer['status'])
    return answer
   finally:
    scope.effective=original_effective;inventory.CIIdentityGuard.verify=original_seal

  for case in CASES:
   row=dict(case=case,kind='separate controlled drift/fault' if case in STRENGTHENED else 'immutable validation',versions={})
   result['cases'].append(row);persist()
   for version,scope in enumerate(scopes):
    expected='accept' if case in VALID or (case in STRENGTHENED and version==0) else 'reject'
    folder=root/(case+'-'+str(version))
    try:f=prepare(scope,folder,2,case)
    except ValueError as error:
     if case not in ['orphan-family','missing-runtime']:raise
     row['versions'][str(version)]=dict(status='reject',phase='initial scanner invariant, before factory',type=type(error).__name__,message=str(error),traceback=traceback.format_exc())
     continue
    answer=invoke(scope,f,case,expected);row['versions'][str(version)]=answer;persist()
   left,right=(row['versions'][str(v)] for v in [0,1])
   if case not in STRENGTHENED and (left['status']!=right['status'] or
       (left['status']=='accept' and left['ordered']!=right['ordered'])):
    raise RuntimeError('Immutable semantic/ordered-map difference: '+case)

  for count in SCALES:
   row=dict(modules=count,versions={});result['scales'].append(row);persist()
   fixtures=[prepare(scope,root/('scale-'+str(count)+'-'+str(v)),count,'valid') for v,scope in enumerate(scopes)]
   if fixtures[0]['enumeration']!=fixtures[1]['enumeration']:raise RuntimeError('Fresh fixture enumeration differs; no equivalence claim')
   for v in ([0,1] if count==SCALES[0] else [1,0]):
    f=fixtures[v];scope=scopes[v];data=dict(folder=str(f['folder']),calls=[]);row['versions'][str(v)]=data
    plain=invoke(scope,f,'valid','accept');data['ordered']=plain.pop('ordered');data['calls'].append(plain)
    for repeat in range(2):
     observed=invoke(scope,f,'valid','accept',True)
     if observed.pop('ordered')!=data['ordered']:raise RuntimeError('Repeat/profile changed exact ordered map')
     p=observed['profile'];scan=p['counters'].get('CIInventory.scan',{}).get('calls',0)
     if scan!=1 or p['regular_reads'].get('CIInventory.scan',{}).get('completed')!=f['semantic']:
      raise RuntimeError('Each invocation must scan/bind semantic inputs freshly')
     expected=f['critical']+f['new']+f['resolved']+(f['semantic'] if v==0 else 0)
     if p['regular_reads'].get('contracts.unchanged',{}).get('completed',0)!=expected:
      raise RuntimeError('Critical/content pass coverage differs')
     if repeat and p['path_read_multiset_sha256']!=data['calls'][1]['profile']['path_read_multiset_sha256']:
      raise RuntimeError('Repeated invocation did not redo the same complete read multiset')
     data['calls'].append(observed);persist()
   if row['versions']['0']['ordered']!=row['versions']['1']['ordered']:raise RuntimeError('Scale ordered maps differ')
  result.update(fixture_bytes_conservative=budget.bytes,fixture_byte_ceiling=32*1024**2,
    unsupported_uninitialized_or_custom_inventory='NOT TESTED; outside factory-equivalence premise',
    native_stage_command_authentication='NOT EXECUTED; constructor witnesses are deliberately nonlaunchable',
    full_production_roots_receipts_and_full_job_savings='UNAVAILABLE/UNPROVED')
  persist();return result
 finally:
  if view is not None:view.close()
  for name,value in previous.items():
   if value is None:sys.modules.pop(name,None)
   else:sys.modules[name]=value
