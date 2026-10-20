"""Nine finite focused children after ordinary CI build; no retry or local mode."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time,traceback
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
ENGINE=ROOT/'checkpoints/light-eft-canonical-output-adapter-20261020'
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
def require(ok,message):
 if not ok:raise ValueError(message)
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def save(p,d):
 p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2)+'\n')
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def bound_spec():
 path=HERE/'ci-spec.json';raw=subprocess.check_output(['git','show','HEAD:'+str(path.relative_to(ROOT))],cwd=ROOT)
 require(path.read_bytes()==raw,'Focused spec differs from exact checkout');s=json.loads(raw)
 for row in [*s['sources'],*s['dependencies'],*s['engine_files']]:
  rel=Path(row['path']);require(not rel.is_absolute() and '..' not in rel.parts,'Unsafe bound path')
  p=ROOT/rel
  require(not any(x.is_symlink() for x in [p,*p.parents]),'Symlink bound source')
  require(p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'Focused byte binding changed: '+str(rel))
  require(subprocess.check_output(['git','show','HEAD:'+str(rel)],cwd=ROOT)==p.read_bytes(),'Bound source differs from Git HEAD')
 return s
def build_plans(tool,work,spec,roots,head,bind):
 from finite_contract import CONTRACT
 staged=ROOT/spec['staged_root'];source={r['role']:ROOT/r['path'] for r in spec['sources']}
 env=dict(LANG='C.UTF-8',LC_ALL='C.UTF-8',LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(tool),
  LEAN_PATH=':'.join(map(str,roots)),LEAN_SRC_PATH=':'.join(map(str,[staged,ROOT/'Light Edge Fault Tolerant Graph Spanners',ROOT/'An Alternate Proof of Near-Optimal Light Spanners',tool/'src/lean'])),
  MIMALLOC_ARENA_RESERVE='128MiB',MIMALLOC_VERBOSE='1',LIGHTEFT_SOURCE_COMMIT=head,LIGHTEFT_HARNESS_COMMIT=head,
  LIGHTEFT_FROZEN_SOURCE_COMMIT='78cb40c7837db049d645d73696f2e0b724ce8a3b')
 result=[]
 for i,module in enumerate(CONTRACT['modules']):
  case=module.rsplit('.',1)[-1];target=work/'objects'/Path(*module.split('.')).with_suffix('.olean')
  roles=['serialization','composition'];proof=source[roles[i]];audit=source[roles[i]+'_audit'];resolver=source['resolver']
  commands=[[str(tool/'bin/lean'),*FLAGS,'--root='+str(staged),'-o',str(target),str(proof)],
   [str(tool/'bin/lean'),*FLAGS,str(resolver)],[str(tool/'bin/leanchecker'),'-v',module],
   [str(tool/'bin/lean'),*FLAGS,str(audit)]]
  for kind,argv,submitted in zip(['compile','resolve','replay','audit'],commands,[[proof],[resolver,proof],[proof],[audit,proof]],strict=True):
   e=env.copy()
   if kind=='resolve':e.update(LIGHTEFT_CHECKER_TARGET=module,LIGHTEFT_CHECKER_RESOLUTION_FILE=str(work/'resolution'/(case+'.json')))
   if kind=='replay':e.pop('MIMALLOC_VERBOSE');e['LEAN_STACK_SIZE_KB']='65536'
   p=dict(stage=kind,module=module,case=case,argv=argv,env=e,sources=list(map(str,submitted)),
    cwd=str(work/'audit'/case if kind=='audit' else work))
   p['source_bindings']=[bind(x) for x in p['sources']];result.append(p)
 proof=source['fixtures'];result.append(dict(stage='compile',module='PaidFlagFixtures',case='PaidFlagFixtures',
  argv=[str(tool/'bin/lean'),*FLAGS,'--root='+str(staged),str(proof)],env=env.copy(),sources=[str(proof)],
  source_bindings=[bind(proof)],cwd=str(work)))
 return result
def execute_sequence(plans,child,finish):
 from finite_contract import CONTRACT
 expected=[(m,s) for m in CONTRACT['modules'] for s in ['compile','resolve','replay','audit']]+[('PaidFlagFixtures','compile')]
 require([(p['module'],p['stage']) for p in plans]==expected,'Missing/extra/reordered focused schedule')
 completed=[]
 for p in plans:
  r=child(p);completed.append(dict(module=p['module'],stage=p['stage'],attempt_id=r['attempt_id']))
 return dict(stages=completed,result=finish())
def run_stage(root,env,spec):
 # Every imported local runtime source was authenticated by bound_spec first.
 sys.path.insert(0,str(ENGINE));sys.path.insert(0,str(HERE));sys.path.insert(0,str(ROOT/'scripts'))
 from ci_policy import ci_identity
 from finite_contract import CONTRACT
 from contracts import bind,save as durable_save
 from ci_inventory import CIInventory
 from ci_lease import CILease
 from ci_accounting import CIAccounting
 from LightEFTCgroup import memory_snapshot
 from ci_receipts import verify_receipts
 from ci_admission_receipts import verify_singleton_receipt
 from focused_context import FocusedContext
 import child_runner,audit_check
 head=git('rev-parse','HEAD');identity=ci_identity(env,head)
 def identity_check():require(ci_identity(dict(os.environ),head)==identity,'Focused CI identity drift')
 candidates=[p for p in (Path(env['HOME'])/'.elan/toolchains').iterdir() if (p/'bin/lean').is_file() and digest(p/'bin/lean')==spec['tool_hashes']['lean']]
 require(len(candidates)==1,'Exactly one hash-pinned official toolchain required');tool=candidates[0]
 require(digest(tool/'bin/leanchecker')==spec['tool_hashes']['leanchecker'],'Official checker hash differs')
 for name,rev in spec['pins'].items():
  folder=ROOT/'.lake/packages'/name
  require(git('-C',str(folder),'rev-parse','HEAD')==rev and not git('-C',str(folder),'status','--porcelain','--untracked-files=no'),'Locked dependency checkout differs')
 names={r['module'] for r in spec['dependencies']}
 require(len(names)==16 and len(CONTRACT['imports'][CONTRACT['modules'][0]])==13 and len(CONTRACT['imports'][CONTRACT['modules'][1]])==17 and set(CONTRACT['imports'][CONTRACT['modules'][0]])<names and
  set(CONTRACT['imports'][CONTRACT['modules'][1]])==names|{CONTRACT['modules'][0]},'Finite per-module source scope differs')
 work=root/'work';objects=work/'objects';evidence=root/'runtime'
 require(not work.exists() and not evidence.exists(),'Fresh focused roots required')
 packages=ROOT/'.lake/packages';roots=[objects,ROOT/'.lake/build/lib/lean',*[packages/n/'.lake/build/lib/lean' for n in spec['pins'] if (packages/n/'.lake/build/lib/lean').is_dir()],tool/'lib/lean']
 deps={m:dict(bind(roots[1]/Path(*m.split('.')).with_suffix('.olean')),module=m) for m in sorted(names)}
 # Ordinary CI freshly built these inputs. Preserved source-review carriers are
 # never searched, imported, copied or used as production manifests here.
 inventory=CIInventory(roots[1:],tool,bind);classified=inventory.scan();inputs=dict(classified['semantic'])
 for row in [*spec['sources'],*spec['dependencies'],*spec['engine_files']]:inputs[str(ROOT/row['path'])]=bind(ROOT/row['path'])
 for p in [HERE/'ci-spec.json',ROOT/'lake-manifest.json',ROOT/'lean-toolchain',tool/'bin/lean',tool/'bin/leanchecker']:inputs[str(p)]=bind(p)
 plans=build_plans(tool,work,spec,roots,head,bind)
 save(root/'plans.json',plans);identity_check();child_runner.assert_idle('focused-before-claim',{})
 (root/'production-claim.json').open('x').write(json.dumps(identity)+'\n')
 objects.mkdir(parents=True);(objects/'LightEFTPaidSamplingStage').mkdir();(work/'resolution').mkdir();evidence.mkdir()
 state=dict(accepted=False,independent_review='pending',CI_identity=identity,source_commit=head,harness_commit=head,
  dependency_qualification='Fresh ordinary-CI build objects; no historical preservation or authenticated clean cache provenance')
 try:
  with CILease(root,durable_save,identity_check) as lease:
   ctx=FocusedContext(lease,work,evidence,plans,roots,deps,identity,inputs,inventory,classified);accounting=CIAccounting(memory_snapshot)
   def child(p):
    r=child_runner.run_child(p,Path(p['cwd']),evidence/p['case']/p['stage'],ctx,accounting=accounting)
    path=evidence/p['case']/p['stage']/'receipt.json';ctx.evidence_files[str(path)]=bind(path)
    return r
   state.update(execute_sequence(plans,child,ctx.finish))
  # Reuse the complete accepted verifiers: four receipts for each module,
  # singleton verifier for fixtures. Then reconcile the global nine-child order.
  for case,part in [('PaidFlagSerialization',plans[:4]),('PaidFlagSampleComposition',plans[4:8])]:
   ds=ctx.dependencies(part[0]);verify_receipts(evidence/case,lease.record,part,ds,head,expected_source=head)
  verify_singleton_receipt(evidence/'PaidFlagFixtures',lease.record,plans[8:],ctx.dependencies(plans[8]),head,expected_source=head)
  ids=set();previous=0
  for p in plans:
   r=load(evidence/p['case']/p['stage']/'receipt.json')
   require(r['focused_module']==p['module'] and r['CI_identity']==identity,'Focused receipt identity/module differs')
   require(r['attempt_id'] not in ids and previous<r['started_ns'],'Duplicate/overlapping focused child');ids.add(r['attempt_id']);previous=r['ended_ns']
  require(len(ids)==9 and lease.record['state']=='released' and lease.record['kernel_echild'] and not lease.record.get('release_errors'),'Incomplete focused schedule/release')
  state['accepted']=True
 except BaseException as error:state['failure']=repr(error);traceback.print_exc()
 finally:
  save(root/'result.json',state);exports=[]
  for p in sorted(evidence.rglob('*')):
   if p.is_file() and p.name in ['raw.log','receipt.json','samples.jsonl','inputs.jsonl','excluded-metadata-initial.jsonl']:
    directory=root/'available-exports'/p.relative_to(evidence);m=audit_check.chunk(p,directory)
    exports.append(dict(source=str(p),manifest=str(directory/'manifest.json'),bytes=m['bytes'],sha256=m['sha256']))
  save(root/'available-export-index.json',exports)
 return state
def main():
 env=dict(os.environ);require(env.get('GITHUB_RUN_ID','').isdecimal() and env.get('GITHUB_RUN_ATTEMPT','').isdecimal(),'Ordinary CI identity required')
 temp=Path(env['RUNNER_TEMP']);require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(),'Invalid runner temp')
 suffix=env['GITHUB_RUN_ID']+'-'+env['GITHUB_RUN_ATTEMPT'];cache=temp/('light-eft-paid-focused-python-'+suffix)
 require(sys.dont_write_bytecode and sys.pycache_prefix==str(cache) and not cache.exists(),'Fresh absent Python cache prefix and -B required')
 root=temp/('light-eft-paid-focused-'+suffix);root.mkdir(mode=0o700,exist_ok=False)
 try:require(run_stage(root,env,bound_spec())['accepted'],'Focused gate failed')
 except BaseException as error:
  save(root/'stage-failure.json',dict(error=repr(error)));(root/'stage-raw.log').write_text(traceback.format_exc());traceback.print_exc();return 1
 finally:
  rows=[]
  for p in sorted(root.rglob('*')):
   if p.is_file() and p.name!='evidence-sha256.json':rows.append(dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=digest(p)))
  save(root/'evidence-sha256.json',rows)
 return 0
if __name__=='__main__':sys.exit(main())
