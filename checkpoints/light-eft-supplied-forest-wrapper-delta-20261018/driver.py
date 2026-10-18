"""Preparation-only scoped engine; the real production entry remains disabled."""
from pathlib import Path
import json,os,subprocess,sys,time,traceback
from contracts import *
from lease import Lease,COMMON
from scope import Context,reviewed_inputs,reviewed_wrapper,verify_receipts,DRAFT,APPROVED
import child_runner
HERE=Path(__file__).resolve().parent
def execute_production(reviewed_commit=None,coordination=None,**unexpected):
 """No CLI/autostart. A later explicit review plus fresh coordination is required."""
 if unexpected or reviewed_commit is None or coordination is None:raise ProductionDisabled('No explicit independently reviewed implementation/fresh coordination')
 from authority import ReviewedAuthority
 authority=ReviewedAuthority(reviewed_commit,coordination)
 spec,_,_=reviewed_inputs();work=Path(spec['future_work_root'])
 require(not work.exists(),'Fresh planned work root already exists; no retry')
 bound=make_production_plan(work,reviewed_commit)
 # All launch-relevant helper/source bytes are immutable inputs.
 require(all(bound['inputs'].get(k)==v for k,v in authority.bindings.items()),'Wrapper bindings missing')
 # No wrapper action in this preparation turn calls this function.
 evidence=HERE/'production-evidence'
 evidence.mkdir(exist_ok=False)
 with (HERE/'production-invocation-claimed.json').open('x') as f:json.dump({'reviewed_commit':reviewed_commit,'coordination':coordination},f)
 child_runner.assert_idle('fresh-ownership-before-creation',{})
 work.mkdir();Path(bound['roots'][0]).mkdir()
 state=_run_batch(work,evidence,bound['plans'],bound['roots'],bound['dependencies'],bound['inputs'],
  Lease(COMMON,evidence/'lease.json',coordination,fixture=False,authority=authority),False,reviewed_commit)
 return state
def describe_production():
 spec,deps,protected=reviewed_inputs()
 return dict(status='NO_PRODUCTION_AUTHORITY_SUPPLIED',source_commit=APPROVED,source=spec['new_source'],audit=spec['audit_source'],
  dependency_count=len(deps['bindings']),dependency_namespaces={'LightEFTSpanners':140,'LightSpanners':56},
  protected_checkpoint_entries=13,protected_supervisor_bindings=10,
  stage_order=list(STAGES),profile=spec['profile'],commands=spec['commands'],
  audit_cwd_delta='Fresh work/audit, containing only ci-evidence; object root and resolution are separately immutable after creation',
  activation='Explicit later reviewed wrapper commit and a fresh incarnation-bound coordinator document are required. No authority is supplied in this preparation.')
def make_production_plan(work,wrapper_commit):
 """Exact plan construction for later review only; no filesystem mutation."""
 spec,deps,protected=reviewed_inputs();protected.update(reviewed_wrapper(wrapper_commit))
 work=Path(work);old=spec['future_work_root'];plans=[]
 env=dict(spec['environment'])
 for k,v in env.items():env[k]=v.replace(old,str(work))
 env['LIGHTEFT_SOURCE_COMMIT']=APPROVED
 env['LIGHTEFT_HARNESS_COMMIT']=wrapper_commit
 for item in spec['commands']:
  e=dict(env);e.update({k:v.replace(old,str(work)) for k,v in item.get('environment_additions',{}).items()})
  for k in item.get('environment_remove',[]):e.pop(k,None)
  plans.append(dict(stage=item['stage'],module=TARGET,argv=[a.replace(old,str(work)) for a in item['argv']],env=e,sources=item['submitted_sources']))
 # Bind all search-root files that can affect imports, including library sidecars.
 inventory=json.loads((DRAFT/'accepted-imports.json').read_text())['accepted_full_input_inventory']
 authority={}
 with (DRAFT.parents[1]/inventory['path']).open() as f:
  for line in f:
   row=json.loads(line);authority[row['path']]=row
 roots=list(map(Path,plans[0]['env']['LEAN_PATH'].split(':')))
 for root in roots[1:]:
  for p,row in tree(root).items():
   require(p in authority,'Unlisted effective search input');protected[p]=bind(p,authority[p])
 return dict(plans=plans,roots=roots,dependencies={r['module']:r for r in deps['bindings']},inputs=protected)
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
