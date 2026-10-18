"""Exercise the complete real plan builder, never its production entry.

Run only after committing this implementation, supplying that exact commit.
Reads/hashes semantic inputs; excluded paths get metadata enumeration only.
Writes evidence under this checkpoint. Git show/ls-tree are the only children.
"""
from pathlib import Path
import collections,contextlib,datetime,fcntl,json,os,resource,shutil,sys,time,traceback,uuid
from unittest.mock import patch
import contracts as c
import driver
import lease
import scope
import semantic_inventory as inventory
import focused_audit

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def main(commit):
 c.require(len(commit)==40 and all(ch in '0123456789abcdef' for ch in commit),'Exact implementation commit required')
 out=HERE/'plan-evidence'/uuid.uuid4().hex;out.mkdir(parents=True)
 proposal=json.loads((driver.DRAFT/'execution-proposal.json').read_text())
 work=Path(proposal['future_work_root'])
 policy=json.loads((HERE/'inventory-policy.json').read_text())
 prior,prior_ref=inventory.load_prior()
 diagnosis=[json.loads(line) for line in (ROOT/policy['diagnosis']['path']).read_text().splitlines()]
 excluded={r['path'] for r in diagnosis if r['path'] not in prior and not r['path'].endswith('.ir.sig')}
 c.require(len(excluded)==62420,'Unexpected diagnosed metadata-only membership')
 c.require(not work.exists() and not work.is_symlink(),'Future work root already exists')
 start=time.monotonic_ns();git_calls=[];denied=[];opened=set();metadata=set()
 def forbidden(*args,**kwargs):
  denied.append({'api':'forbidden API','arguments':repr(args)})
  raise AssertionError('No production, children, locking or resource probes in plan validation')
 def audit(event,args):
  if event=='subprocess.Popen':
   executable,argv,cwd,env=args
   if executable!='git' or not isinstance(argv,list) or len(argv)<3 or argv[0]!='git' or argv[1] not in ['show','ls-tree'] or str(cwd)!=str(ROOT):
    denied.append({'event':event,'argv':repr(argv)});raise AssertionError('Only read-only Git show/ls-tree allowed')
   git_calls.append({'argv':argv,'cwd':str(cwd)})
  elif event in ['os.fork','os.forkpty','os.posix_spawn','os.posix_spawnp','os.system','fcntl.flock','fcntl.lockf']:
   denied.append({'event':event});raise AssertionError('Forbidden process/lock API')
  elif event=='open':
   path,mode,flags=args
   if not isinstance(path,(str,bytes,os.PathLike)):return
   path=str(Path(os.fsdecode(path)).absolute())
   if path==str(lease.COMMON) or Path(path).is_relative_to(work) or path.startswith(('/proc/','/sys/')):
    denied.append({'event':event,'path':path});raise AssertionError('Forbidden lock/work/resource path')
   if path in excluded:
    denied.append({'event':event,'path':path});raise AssertionError('Excluded content was opened')
   if flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):
    c.require(Path(path).is_relative_to(out),'Write outside plan evidence: '+path)
   else:opened.add(path)
  elif event in ['os.mkdir','os.remove','os.rmdir','os.rename','os.link','os.symlink','os.truncate']:
   # The builder must not mutate anything. Only our row-aligned evidence
   # exporter creates directories/files after the builder returns.
   allowed=(event=='os.mkdir' and Path(os.fsdecode(args[0])).absolute().is_relative_to(out)) or (event=='os.rename' and all(Path(os.fsdecode(p)).absolute().is_relative_to(out) for p in args[:2]))
   if not allowed:
    denied.append({'event':event,'arguments':repr(args)});raise AssertionError('Unexpected filesystem mutation')
 sys.addaudithook(audit)
 original_metadata=inventory.inspect_metadata
 def observe_metadata(path):
  row=original_metadata(path);metadata.add(str(path));return row
 result={'implementation_commit':commit,'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'kind':'complete real plan construction only; no production/Lean/lock/resource probes','future_work_root':str(work),'prior_inventory':prior_ref}
 try:
  with contextlib.ExitStack() as stack:
   for obj,name in [(driver,'execute_production'),(driver,'run_fixture'),(driver,'_run_batch'),(lease.Lease,'__init__'),(scope.Context,'__init__'),(driver.child_runner,'run_child'),(driver.child_runner,'assert_idle'),(driver.child_runner,'VisibleAccounting'),(fcntl,'flock'),(os,'statvfs'),(os,'sysconf'),(shutil,'disk_usage'),(resource,'getrlimit'),(resource,'setrlimit'),(resource,'getrusage')]:
    stack.enter_context(patch.object(obj,name,forbidden))
   stack.enter_context(patch.object(inventory,'inspect_metadata',observe_metadata))
   # This is the actual complete public builder, with real reviewed_inputs,
   # reviewed_wrapper, Git self-binding and inventory scan left intact.
   bound=driver.make_production_plan(work,commit)
   c.require(bound['plans']==inventory.build_expected(proposal,work,commit),'Complete plan differs')
   c.require(bound['classification']=={'old_semantic_count':57661,'signature_count':11426,'excluded_count':62420},'Unexpected full classification')
   c.require(set(bound['excluded_metadata'])==excluded,'Excluded membership differs from diagnosis')
   c.require(excluded<=metadata and not excluded&opened,'Excluded paths not metadata-only')
   roots=bound['roots'][1:]
   old_paths={p for p in prior if any(Path(p).is_relative_to(r) for r in roots)}
   c.require(old_paths<=set(bound['inputs']),'Old input coverage lost')
   for p in old_paths:
    row=bound['inputs'][p]
    c.require(row['sha256']==prior[p]['sha256'] and row['bytes']==prior[p]['bytes'],'Old binding changed')
   supplements=[json.loads(line) for line in (HERE/'signature-supplement.jsonl').read_text().splitlines()]
   for row in supplements:c.require(bound['inputs'][row['path']]=={k:row[k] for k in ['path','bytes','sha256','identity']},'New-local signature differs')
   # The real builder does not itself enter the independent shadow check.
   # Exercise that existing read-only check separately on the full real roots.
   target=work/'objects'/Path(*c.TARGET.split('.')).with_suffix('.olean')
   # Future output root is absent by design; effective() requires extant roots.
   # Existing input roots suffice for precompile absence/dependency/shadows.
   c.effective(roots,bound['dependencies'],target,False)
   c.require(not work.exists(),'Builder created future work root')
   c.require(not denied,'Guarded forbidden operation occurred')
   def rows(path,values):
    with path.open('x') as f:
     for row in values:f.write(json.dumps(row,separators=(',',':'))+'\n')
   rows(out/'semantic-inputs.jsonl',[bound['inputs'][p] for p in sorted(bound['inputs'])])
   rows(out/'excluded-metadata.jsonl',[bound['excluded_metadata'][p] for p in sorted(bound['excluded_metadata'])])
   (out/'plans.json').write_text(json.dumps(bound['plans'],indent=2)+'\n')
   exports={name:focused_audit.chunk(out/(name+'.jsonl'),out/(name+'-export')) for name in ['semantic-inputs','excluded-metadata']}
   native=sorted(p for p in old_paths if p.endswith(('.so','.dll','.dylib','.a')))
   suffix_counts=collections.Counter('exact .a' if p in inventory.ARCHIVES else inventory.metadata_form(p) for p in excluded)
   result.update(successful=True,classification=bound['classification'],semantic_input_rows=len(bound['inputs']),
    retained_old_root_paths=len(old_paths),retained_old_native_paths=native,
    newly_observed_signatures=len(supplements),signature_payload_bytes=sum(r['bytes'] for r in supplements),
    signature_supplement=bound['signature_supplement'],excluded_metadata_forms=dict(suffix_counts),
    excluded_metadata_enumerated=len(excluded&metadata),excluded_content_open_attempts=0,
    project_dependencies=len(bound['dependencies']),independent_existing_root_shadow_check='passed',
    exact_argv_environment_and_LEAN_SYSROOT='passed',future_work_root_created=False,production_entry_calls=0,
    lease_or_lock_calls=0,compiler_checker_invocations=0,resource_probes=0,exports=exports)
 except BaseException as exc:
  result.update(successful=False,failure=repr(exc))
  (out/'failure.log').write_text(traceback.format_exc())
  raise
 finally:
  result.update(start_monotonic_ns=start,end_monotonic_ns=time.monotonic_ns(),git_metadata_calls=git_calls,denied_operations=denied)
  (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
  print('PLAN_EVIDENCE='+str(out),flush=True)
 print(json.dumps({k:result[k] for k in ['implementation_commit','successful','classification','semantic_input_rows','excluded_metadata_forms','compiler_checker_invocations','resource_probes']},indent=2))

if __name__=='__main__':
 c.require(len(sys.argv)==2,'Usage: python3 -B validate_real_plan.py EXACT_IMPLEMENTATION_COMMIT')
 main(sys.argv[1])
