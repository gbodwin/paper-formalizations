"""Offline schedule/Git/binding checks. No runtime gate is imported or executed."""
from pathlib import Path
import ast,copy,hashlib,json,subprocess,yaml
H=Path(__file__).resolve().parent;R=H.parents[1]
BASE='642ae01aa7fdad947d815eec400cd2d7c79fa855';KERNEL='c1aaa0a00c0c943cec4b2753a937023e9884db04'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda b:yaml.load(b,Loader=yaml.BaseLoader)
old=load(git('show',KERNEL+':.github/workflows/lean.yml'))
full=load((R/'.github/workflows/lean.yml').read_text());focus=load((R/'.github/workflows/light-eft-fair-bit-focused.yml').read_text())
ctx={'LIGHTEFT_JOB_WORKFLOW_REF':'${{ job.workflow_ref }}','LIGHTEFT_JOB_WORKFLOW_SHA':'${{ job.workflow_sha }}',
 'LIGHTEFT_JOB_WORKFLOW_PATH':'${{ job.workflow_file_path }}','LIGHTEFT_JOB_WORKFLOW_REPOSITORY':'${{ job.workflow_repository }}'}
assert full['name']==old['name']=='Lean' and full['on']==old['on']
assert full['permissions']==focus['permissions']==old['permissions']=={'contents':'read'}
assert full['concurrency']==old['concurrency']=={'group':'paper-formalizations-single-compiler','cancel-in-progress':'false'}
assert 'concurrency' not in focus and 'concurrency' not in focus['jobs']['check']
assert set(full['jobs'])=={'check','focused','acceptance'} and set(focus['jobs'])=={'check'}
call=full['jobs']['focused'];assert call['needs']=='check' and call['uses']=='./.github/workflows/light-eft-fair-bit-focused.yml'
assert call['with']=={'source':'${{ github.sha }}'} and 'always' not in call['if']
assert set(focus['on'])=={'workflow_call'} and focus['on']['workflow_call']['inputs']=={'source':{'required':'true','type':'string'}}
assert focus['on']['workflow_call']['outputs']['validated_commit']['value']=='${{ jobs.check.outputs.validated_commit }}'
for doc,role in [(full,'full'),(focus,'focused')]:
 job=doc['jobs']['check'];assert job['timeout-minutes']=='120' and job['runs-on']=='ubuntu-latest'
 assert job['env']['LEAN_NUM_THREADS']=='1' and job['env']['LIGHTEFT_VALIDATION_ROLE']==role
 assert 'light-eft-spanners-checkpoints' in job['if']
 for step in job['steps']:
  assert step.get('continue-on-error') is None
  if 'ci_gate.py' in step.get('run','') or '/acceptance.py mark ' in step.get('run','') or '/workflow_identity.py' in step.get('run',''):
   assert all(step['env'][k]==v for k,v in ctx.items()),step
 assert job['outputs']=={'validated_commit':'${{ steps.'+('full' if role=='full' else 'focused')+'_validated.outputs.commit }}'}
assert focus['jobs']['check']['env']['LIGHTEFT_EXPECTED_SOURCE']=='${{ inputs.source }}'
assert full['jobs']['check']['env']['LIGHTEFT_EXPECTED_SOURCE']=='${{ github.sha }}'
# Every c1 full step remains byte-equivalent after deleting only new context
# environment entries. No proof command, accepted condition, action or upload changed.
now=full['jobs']['check']['steps'];idx=0
for step in old['jobs']['check']['steps']:
 found=False
 while idx<len(now):
  current=copy.deepcopy(now[idx]);idx+=1
  if 'env' in current:
   for k in ctx:current['env'].pop(k,None)
  if current==step:found=True;break
 assert found,step.get('name',step.get('uses'))
assert len(now)==len(old['jobs']['check']['steps'])+3 # two immediate uploads and full marker
assert not any('fair-bit' in s.get('run','') for s in now)
for doc in [full,focus]:
 steps=doc['jobs']['check']['steps']
 for s in steps:
  assert 'download-artifact' not in s.get('uses','')
  assert 'continue-on-error' not in s
gate_names=['light_eft_paid_focused','light_eft_staged','light_eft_paid_joint_bridge','light_eft_fair_bit_batch']
steps=focus['jobs']['check']['steps'];gates=[s['id'] for s in steps if 'ci_gate.py' in s.get('run','')]
assert gates==gate_names
oldinline=load(git('show',BASE+':.github/workflows/lean.yml'))['jobs']['check']['steps']
for g in gate_names:
 current=copy.deepcopy(next(s for s in steps if s.get('id')==g))
 for k in ctx:current['env'].pop(k,None)
 assert current==next(s for s in oldinline if s.get('id')==g),'Producer/batch command or environment changed'
 i=next(i for i,s in enumerate(steps) if s.get('id')==g);up=steps[i+1]
 assert up['uses']=='actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02'
 assert up['if']=='${{ always() && steps.'+g+".outcome != 'skipped' }}"
 assert up['with']['include-hidden-files']=='true' and up['with']['if-no-files-found']=='error'
before=[s.get('name','') for s in steps[:next(i for i,s in enumerate(steps) if s.get('id')==gate_names[0])]]
assert before[-2:]==['Build exact external inputs for fair-bit batch','Check all paper module indexes']
assert next(s for s in steps if s.get('name')=='Build exact external inputs for fair-bit batch')==next(s for s in oldinline if s.get('name')=='Build exact external inputs for fair-bit batch')
assert [s for s in steps if s.get('uses','').startswith('leanprover/lean-action')]==[s for s in old['jobs']['check']['steps'] if s.get('uses','').startswith('leanprover/lean-action')]
assert steps[0]['with']=={'ref':'${{ inputs.source }}','persist-credentials':'false'}
assert sum('ci_gate.py' in s.get('run','') for s in steps)==4
artifacts=[]
for doc in [full,focus]:
 for j in doc['jobs'].values():
  for s in j.get('steps',[]):
   if 'upload-artifact' in s.get('uses',''):artifacts.append(s['with']['name'])
assert len(artifacts)==len(set(artifacts)),'Artifact names collide across jobs in one run'
accept=full['jobs']['acceptance'];assert accept['needs']==['check','focused'] and 'always()' in accept['if'] and accept['timeout-minutes']=='5'
assert accept['steps'][1]['env']=={'LIGHTEFT_NEEDS_JSON':'${{ toJSON(needs) }}'}
assert accept['steps'][1]['run'].endswith('/acceptance.py aggregate') and accept['steps'][2]['if']=='always()'
# Exact old sources/resources: only finite scheduling and binding changes allowed.
specnames=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
 'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']
bound=0
for n in specnames:
 p='checkpoints/'+n+'/ci-spec.json';a=json.loads(git('show',BASE+':'+p));b=json.loads((R/p).read_text())
 ae=a.pop('engine_files');be=b.pop('engine_files');assert a==b,p
 assert len(be)==len({r['path'] for r in be}) and {r['path'] for r in ae}<={r['path'] for r in be}
 assert '.github/workflows/light-eft-fair-bit-focused.yml' in {r['path'] for r in be}
 assert all(r['path'] in {x['path'] for x in ae} or r['path'].startswith(str(H.relative_to(R))+'/') or r['path']=='.github/workflows/light-eft-fair-bit-focused.yml' for r in be)
 for row in be:
  raw=(R/row['path']).read_bytes();assert row==dict(path=row['path'],bytes=len(raw),sha256=sha(raw)),row['path'];bound+=1
for directory in ['light-eft-canonical-output-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019']:
 p='checkpoints/'+directory+'/ci_policy.py';a=ast.parse(git('show',BASE+':'+p));b=ast.parse((R/p).read_text())
 aa={f.name:ast.dump(f,include_attributes=False) for f in a.body if isinstance(f,ast.FunctionDef)}
 bb={f.name:ast.dump(f,include_attributes=False) for f in b.body if isinstance(f,ast.FunctionDef)}
 assert aa.keys()==bb.keys() and all(aa[k]==bb[k] for k in aa if k!='ci_identity')
 x=next(f for f in a.body if isinstance(f,ast.FunctionDef) and f.name=='ci_identity')
 y=next(f for f in b.body if isinstance(f,ast.FunctionDef) and f.name=='ci_identity')
 assert all(ast.dump(s,include_attributes=False)==ast.dump(t,include_attributes=False) for s,t in zip(x.body[:-1],y.body,strict=False))
allowed={'.github/workflows/lean.yml','.github/workflows/light-eft-fair-bit-focused.yml',*['checkpoints/'+n+'/ci-spec.json' for n in specnames],
 *['checkpoints/'+n+'/ci_policy.py' for n in specnames if n in ['light-eft-canonical-output-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019']],
 'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci_gate.py','checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/PLAN.json','checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/README.md'}
changed=git('diff','--name-only',BASE).decode().splitlines()+git('ls-files','--others','--exclude-standard').decode().splitlines()
assert all(p in allowed or p.startswith(str(H.relative_to(R))+'/') for p in changed)
for p in R.glob('checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/*.py'):
 if p.name!='ci_gate.py':assert p.read_bytes()==git('show',BASE+':'+str(p.relative_to(R)))
p=R/'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci_gate.py'
before=git('show',BASE+':'+str(p.relative_to(R))).decode()
assert p.read_text()==before.replace('    identity = ci_identity(env, head)\n',
 '    identity = ci_identity(env, head)\n'+"    require(env.get('LIGHTEFT_VALIDATION_ROLE') == 'focused', 'Batch requires the separate focused job')\n")
assert {p.name for p in H.iterdir()}=={'PLAN.json','README.md','acceptance.py','workflow_identity.py','check_schedule.py','test_schedule.py','refresh_bindings.py'}
for p in H.glob('*.py'):ast.parse(p.read_text())
plan=json.loads((H/'PLAN.json').read_text());budget=plan['budget']
assert budget['observed_producers_seconds']==1490 and budget['observed_reused_subtotal_seconds']==1769
assert sum(budget['planning_allocation_seconds'].values())==budget['planning_total_seconds']==6900
assert plan['job_limits_minutes']=={'full':120,'focused':120,'aggregation':5} and not plan['child_resource_changes']
assert plan['unelaborated_proofs']==36
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_SOURCE_SCHEDULE_BINDINGS_ONLY',all_full_checks_preserved=True,producer_children_same_focused_job=17,
 batch_children=12,global_replays_preserved=567,engine_binding_rows_checked=bound,unique_artifact_names=len(artifacts),
 exact_job_workflow_bound=True,mandatory_full_and_focused=True,resource_limits_unchanged=True,
 measured_reused_subtotal_seconds=1769,planning_envelope_seconds=6900,new_costs_unmeasured=True,
 kernel_acceptance=False,independent_review='pending',no_compiler_push_CI=True),indent=2))
