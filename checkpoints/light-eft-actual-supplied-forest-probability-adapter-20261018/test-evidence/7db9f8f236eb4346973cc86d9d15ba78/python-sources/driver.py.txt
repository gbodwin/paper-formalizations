"""Preparation-only scoped engine; the real production entry remains disabled."""
from pathlib import Path
import json,os,subprocess,sys,time,traceback
from contracts import *
from lease import Lease,COMMON
from scope import Context,reviewed_inputs,reviewed_wrapper,verify_receipts,DRAFT,APPROVED
import child_runner
HERE=Path(__file__).resolve().parent
def execute_production(reviewed_commit=None,coordination=None,**unexpected):
 """Plan first; call the explicit coordinator once afterward for a fresh document.

 A preissued document is not an activation argument. No timestamp is refreshed
 here, and no claim/work/lock is created while read-only planning runs.
 """
 if unexpected or reviewed_commit is None or not callable(coordination):raise ProductionDisabled('Explicit reviewed implementation and post-planning coordination provider required')
 spec,_,_=reviewed_inputs(reviewed_commit);work=Path(spec['future_work_root'])
 require(not work.exists(),'Fresh planned work root already exists; no retry')
 bound=make_production_plan(work,reviewed_commit)
 planning_finished_ns=time.monotonic_ns()
 document=coordination()
 require(isinstance(document,dict) and type(document.get('issued_ns')) is int and document['issued_ns']>=planning_finished_ns,'Coordination must be issued after planning; no timestamp refresh')
 from authority import ReviewedAuthority
 authority=ReviewedAuthority(reviewed_commit,document)
 # All launch-relevant helper/source bytes are immutable inputs.
 require(all(bound['inputs'].get(k)==v for k,v in authority.bindings.items()),'Wrapper bindings missing')
 child_runner.assert_idle('fresh-ownership-before-creation',{})
 require(not work.exists(),'Fresh planned work root already exists; no retry')
 # Recheck current incarnation and the unchanged 60-second window immediately
 # before the first claim/directory write. Lease entry rechecks again.
 authority.check_live()
 # No wrapper action in this preparation turn calls this function.
 evidence=Path(spec['future_evidence_root'])
 evidence.mkdir(exist_ok=False)
 with (HERE/'production-invocation-claimed.json').open('x') as f:json.dump({'reviewed_commit':reviewed_commit,'coordination':document},f)
 work.mkdir();Path(bound['roots'][0]).mkdir()
 state=_run_batch(work,evidence,bound['plans'],bound['roots'],bound['dependencies'],bound['inputs'],
  Lease(COMMON,evidence/'lease.json',document,fixture=False,authority=authority),False,reviewed_commit)
 return state
def describe_production(reviewed_commit):
 spec,deps,protected=reviewed_inputs(reviewed_commit)
 return dict(status='NO_PRODUCTION_AUTHORITY_SUPPLIED',source_commit=APPROVED,source=spec['new_source'],audit=spec['audit_source'],
  dependency_count=len(deps['bindings']),dependency_namespaces={'LightEFTSpanners':286,'LightSpanners':56,'LightEFTSuppliedForestStage':1,'LightEFTSuppliedForestProbabilityStage':1},
  protected_checkpoint_entries=13,protected_supervisor_bindings=10,
  stage_order=list(STAGES),profile=spec['profile'],commands=spec['commands'],
  audit_cwd_delta='Fresh work/audit, containing only ci-evidence; object root and resolution are separately immutable after creation',
  activation='Explicit later reviewed wrapper commit and a coordinator callable issuing a document after read-only planning are required. Freshness/current facts are checked before claims and at lease entry. No authority is supplied in this preparation.')
def make_production_plan(work,wrapper_commit):
 """Exact plan construction for later review only; no filesystem mutation."""
 spec,deps,protected=reviewed_inputs(wrapper_commit);protected.update(reviewed_wrapper(wrapper_commit))
 from probability_plan import translate_commands
 work=Path(work);plans=translate_commands(spec,work,wrapper_commit)
 # Classify before content hashing. Old bindings are retained, signatures use
 # their separate new-local supplement, excluded paths receive metadata only.
 from semantic_inventory import load_inventory
 roots=list(map(Path,plans[0]['env']['LEAN_PATH'].split(':')))
 target=roots[0]/Path(*TARGET.split('.')).with_suffix('.olean')
 predicted_selection=effective(roots,{r['module']:r for r in deps['bindings']},target,False,predicted=True)
 inventory,data_bindings,signature_ref=load_inventory(wrapper_commit,plans,work,roots[1:])
 classified=inventory.scan()
 protected.update(data_bindings);protected.update(classified['semantic'])
 return dict(plans=plans,roots=roots,dependencies={r['module']:r for r in deps['bindings']},inputs=protected,
  classification={k:classified[k] for k in ['old_semantic_count','signature_count','excluded_count']},
  signature_supplement=signature_ref,excluded_metadata=classified['excluded'],predicted_package_selection=predicted_selection)

def run_fixture(root,plans,dependencies,inputs,roots):
 """Harmless Python-only integration fixture. Never opens the universal lock."""
 root=Path(root);require(root.is_dir() and root.absolute()!=COMMON.parent,'Invalid fixture root')
 for plan in plans:
  require(plan['argv'][:3]==[sys.executable,'-I',str(HERE/'fixture_worker.py')],'Only the fixed harmless fixture worker is allowed')
  require(plan['stage'] in STAGES and plan['argv'][3]==plan['stage'],'Fixture stage differs')
 evidence=root/'evidence';evidence.mkdir();work=root/'work';work.mkdir()
 Path(roots[0]).mkdir()
 return _run_batch(work,evidence,plans,roots,dependencies,inputs,
  Lease(root/'lock',evidence/'lease.json',dict(exclusive_worker=True,same_directory=str(root)),fixture=True),True,'SYNTHETIC_FIXTURE')
def _run_batch(work,evidence,plans,roots,dependencies,inputs,lease,fixture,wrapper_commit):
 state={'synthetic_fixture':fixture,'accepted':False,'stages':[],'started_ns':time.monotonic_ns()}
 context=None
 try:
  with lease:
   try:
    context=Context(work,evidence,lease,plans,roots,dependencies,inputs,fixture=fixture,wrapper_commit=wrapper_commit)
    context.target.parent.mkdir(parents=True)
    for plan in plans:
     cwd=work/'audit' if plan['stage']=='audit' else work
     require(str(cwd)==plan['cwd'],'Batch cwd differs from reviewed per-command binding')
     r=child_runner.run_child(plan,cwd,evidence/plan['stage'],context)
     state['stages'].append({'stage':plan['stage'],'attempt_id':r['attempt_id']})
    state['result']=context.finish()
   except BaseException as exc:
    state['failure']=repr(exc);traceback.print_exc()
   finally:
    state['preservation_failed']=bool(context and context.preservation_failed)
    save(evidence/'batch-under-lease.json',state)
  if 'failure' not in state:
   verify_receipts(evidence,lease.record,plans,dependencies,wrapper_commit)
   require(not state['preservation_failed'],'Preservation failed')
   state['accepted']=True
 except BaseException as exc:state['failure']=repr(exc);traceback.print_exc()
 state['ended_ns']=time.monotonic_ns();save(evidence/('fixture-result.json' if fixture else 'result.json'),state);return state
if __name__=='__main__':raise SystemExit('Preparation-only module; production entry disabled.')
