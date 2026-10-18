"""Exact reviewed-draft reader and explicit per-command schema translation.

No execution or locking API. Actual-output draft cde705e9 is distinct from the
adapter review and the accepted deterministic/probability source authorities.
"""
from pathlib import Path
import collections,copy,json,re,subprocess
from contracts import TARGET,THEOREM,STAGES,require,regular,bind
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
DRAFT_DIR=ROOT/'checkpoints/light-eft-actual-supplied-forest-probability-draft-20261018'
DRAFT_COMMIT='cde705e91972f00497cfd5fe1235f0eeb2448904'
OLD_SOURCE_COMMIT='40029953e9e53525f0f1f431d6d56333b05183a3'
SOURCE_SLOT='UNBOUND_REQUIRES_EXACT_REVIEWED_DRAFT_COMMIT'
ADAPTER_SLOT='UNBOUND_REQUIRES_EXACT_REVIEWED_ADAPTER_COMMIT'
ACCEPTED_MODULE='LightEFTSuppliedForestStage.SuppliedForestGoodEvent'
ACCEPTED_HASH='b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18'
PROBABILITY_MODULE='LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability'
PROBABILITY_HASH='0716fe2cc66dd6657243cfe6d5d34fb83722f59818d0cdb1838be0bf2d981eeb'
ACCEPTED_OBJECTS={ACCEPTED_MODULE:('accepted_deterministic_dependency',ACCEPTED_HASH,185576,'7eedd5b3c7860cf473f5deff3b4ed369f19e6e61'),
 PROBABILITY_MODULE:('accepted_probability_dependency',PROBABILITY_HASH,76720,'df18cdab7f15e5f377e6c72487e7beff6c5268e5')}
REVIEW_FILES=('released-lock.json','accepted-object-supplement.json')
PREFIXES=('LightEFTSpanners','LightSpanners','LightEFTSuppliedForestStage','LightEFTSuppliedForestProbabilityStage','LightEFTActualSuppliedForestProbabilityStage')
REQUIRED_INTERFACES=('LightEFTSpanners.StoredForestCandidates.assignment_failure_le',
 'LightEFTSpanners.SampledGreedy.polynomial_supplied_forest_package_failure_probability',
 'LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests',
 'LightEFTSpanners.SampledGreedy.polynomial_inaccurate_probability','LightEFTSpanners.FiniteProbability.Law.prob_mono')
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
def exact_adapter_commit(commit):
 require(isinstance(commit,str) and re.fullmatch('[0-9a-f]{40}',commit) is not None,'Exact adapter commit required; no placeholder')
 require(commit not in {DRAFT_COMMIT,OLD_SOURCE_COMMIT,'2d75404bfd140d0e8ecb13d3c2554b853b9a1640','78cb40c7837db049d645d73696f2e0b724ce8a3b',
  '88d297fa58a15406aac6e7c0ea3c85f65965d19a','b6483cccabdf4afdbb8004a768afe8ea9ed0ff32','df18cdab7f15e5f377e6c72487e7beff6c5268e5'},'Draft/origin/frozen/old implementation/evidence is not this adapter review')
 return commit
def source_binding(row):
 require(isinstance(row,dict) and set(row)=={'path','bytes','sha256','identity'},'Per-command source-binding schema differs')
 require(Path(row['path']).is_absolute() and type(row['bytes']) is int and row['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'Invalid source binding')
 require(isinstance(row['identity'],list) and len(row['identity'])==5 and all(type(v) is int for v in row['identity']),'Invalid source identity binding')
 return row
def normalize_plan(raw):
 require(raw['module']==TARGET and raw['theorem']==THEOREM,'Wrong draft target/theorem')
 require(raw['project_dependency_count']==344 and raw['expected_project_module_import_count_including_new_target']==345,'Wrong dependency/import scope')
 require(tuple(raw['project_namespace_prefixes'])==PREFIXES,'Wrong five project prefixes')
 require(raw['stage_order']==list(STAGES) and [c['stage'] for c in raw['commands']]==list(STAGES),'Wrong four-stage order')
 work=Path(raw['future_work_root']);require(work.is_absolute(),'Nonabsolute reviewed work root')
 require(raw['new_object']==str(work/'objects'/Path(*TARGET.split('.')).with_suffix('.olean')),'Wrong target object path')
 expected_sources={'source':DRAFT_DIR/'staged/LightEFTActualSuppliedForestProbabilityStage/PolynomialActualFailureProbability.lean','audit':DRAFT_DIR/'staged/PolynomialActualSuppliedForestProbabilityAudit.lean','resolver':DRAFT_DIR/'staged/ResolvePolynomialActualSuppliedForestTarget.lean'}
 for key,path in expected_sources.items():require(source_binding(raw[key])['path']==str(path),'Wrong reviewed staged-source path')
 roles={'compile':[raw['source']],'resolve':[raw['resolver'],raw['source']],'replay':[raw['source']],'audit':[raw['audit'],raw['source']]}
 sysroot='/workspace/toolchains/lean-4.34.0-linux';lean=sysroot+'/bin/lean'
 argv={'compile':[lean,*FLAGS,'--root='+str(DRAFT_DIR/'staged'),'-o',raw['new_object'],raw['source']['path']],
  'resolve':[lean,*FLAGS,raw['resolver']['path']],'replay':[sysroot+'/bin/leanchecker','-v',TARGET],'audit':[lean,*FLAGS,raw['audit']['path']]}
 for item in raw['commands']:
  stage=item['stage'];require(set(item)=={'stage','argv','environment','submitted_sources','cwd','visible_admission_bytes','executed','launcher_config_bytes_with_placeholders'},'Per-command schema differs')
  require(item['argv']==argv[stage],'Reviewed argv/options differ')
  require(item['submitted_sources']==roles[stage],'Wrong ordered per-command source bindings')
  for row in item['submitted_sources']:source_binding(row)
  require(item['cwd']==str(work/'audit' if stage=='audit' else work),'Wrong per-command cwd')
  require(item['visible_admission_bytes']==(4 if stage in ['replay','audit'] else 3)*1024**3 and item['executed'] is False,'Changed admission or execution marker')
  env=item['environment'];require(isinstance(env,dict) and all(isinstance(k,str) and isinstance(v,str) for k,v in env.items()),'Invalid per-command environment')
  require(env.get('LEAN_SYSROOT')==sysroot and env.get('LEAN_PATH','').split(':')[0]==str(work/'objects'),'Wrong pinned sysroot/output search root')
  require(env.get('LIGHTEFT_SOURCE_COMMIT')==SOURCE_SLOT and env.get('LIGHTEFT_HARNESS_COMMIT')==ADAPTER_SLOT,'Template commit slots differ; origin or arbitrary placeholders rejected')
  if stage=='resolve':require(env.get('LIGHTEFT_CHECKER_TARGET')==TARGET and env.get('LIGHTEFT_CHECKER_RESOLUTION_FILE')==str(work/'resolution.json'),'Wrong resolver environment')
  if stage=='replay':require('MIMALLOC_VERBOSE' not in env and env.get('LEAN_NUM_THREADS')=='1' and env.get('LEAN_STACK_SIZE_KB')=='65536','Changed singleton replay environment')
 spec=copy.deepcopy(raw)
 spec.update(draft_commit=DRAFT_COMMIT,new_source=copy.deepcopy(raw['source']),audit_source=copy.deepcopy(raw['audit']),resolver_source=copy.deepcopy(raw['resolver']),profile=copy.deepcopy(raw['resource_profile']))
 return spec
def translate_commands(spec,work,adapter_commit,source_commit=DRAFT_COMMIT):
 exact_adapter_commit(adapter_commit)
 require(source_commit==DRAFT_COMMIT and source_commit!=OLD_SOURCE_COMMIT,'Exact reviewed draft source commit required; no origin/placeholder')
 require(spec.get('draft_commit')==DRAFT_COMMIT,'Normalized reviewed draft commit missing')
 require(str(work)==spec['future_work_root'],'Work root differs from reviewed probability plan')
 # Revalidate the source schema before translating. No top-level environment,
 # environment_additions or path-only submitted_sources are silently guessed.
 checked=normalize_plan(spec)
 plans=[]
 for item in checked['commands']:
  env=copy.deepcopy(item['environment']);env['LIGHTEFT_SOURCE_COMMIT']=source_commit;env['LIGHTEFT_HARNESS_COMMIT']=adapter_commit
  require(all(not any(token in value for token in ['UNBOUND','PLACEHOLDER','MUST_BE_BOUND','REQUIRES_EXACT']) for value in env.values()),'Unresolved child environment placeholder')
  require(env['LIGHTEFT_SOURCE_COMMIT']==DRAFT_COMMIT and env['LIGHTEFT_HARNESS_COMMIT']==adapter_commit,'Child commits differ')
  plans.append(dict(stage=item['stage'],module=TARGET,argv=copy.deepcopy(item['argv']),env=env,
   sources=[r['path'] for r in item['submitted_sources']],source_bindings=copy.deepcopy(item['submitted_sources']),cwd=item['cwd']))
 return plans
def read_reviewed_draft():
 manifest_path=DRAFT_DIR/'manifest.json';blob=subprocess.check_output(['git','show',DRAFT_COMMIT+':'+str(manifest_path.relative_to(ROOT))],cwd=ROOT)
 require(manifest_path.read_bytes()==blob,'Reviewed draft manifest differs');manifest=json.loads(blob);rows=manifest['entries']
 require(manifest['entries_exclude_this_manifest'] is True and manifest['prior_accepted_probability_evidence_commit']=='df18cdab7f15e5f377e6c72487e7beff6c5268e5','Reviewed draft manifest authority/schema differs')
 require(len(rows)==27 and len({r['path'] for r in rows})==27,'Reviewed draft manifest membership differs')
 protected={str(manifest_path):bind(manifest_path)}
 for row in rows:
  name=Path(row['path']);require(not name.is_absolute() and '..' not in name.parts,'Unsafe reviewed draft path')
  p=DRAFT_DIR/name;expected=subprocess.check_output(['git','show',DRAFT_COMMIT+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  binding,actual=regular(p);require(actual==expected,'Reviewed draft artifact differs');bind(p,row);protected[str(p)]=binding
 raw=json.loads((DRAFT_DIR/'focused-validation-plan.json').read_text());spec=normalize_plan(raw)
 for key in ['source','audit','resolver']:require(bind(raw[key]['path'])==raw[key],'Reviewed staged source identity/content differs')
 require(spec['profile']==json.loads((ROOT/'checkpoints/light-eft-supplied-forest-package-20261018/execution-proposal.json').read_text())['profile'],'Resource profile differs from accepted bounded profile')
 return spec,json.loads((DRAFT_DIR/'project-dependency-bindings.json').read_text()),protected
def accepted_supplements(policy,spec):
 require(set(policy)=={'reviewed_draft_commit','objects','admission'} and policy['reviewed_draft_commit']==DRAFT_COMMIT,'Accepted-object supplement authority/schema differs')
 require(isinstance(policy['objects'],list) and len(policy['objects'])==2,'Exactly two accepted immutable objects required')
 require(all(isinstance(row,dict) and set(row)=={'module','accepted_evidence_commit','object'} for row in policy['objects']),'Accepted-object record schema differs')
 rows={row['module']:row for row in policy['objects']}
 require(len(rows)==2 and set(rows)==set(ACCEPTED_OBJECTS),'Accepted-object supplement membership/duplicates differ')
 result={}
 for module,(key,expected_hash,size,evidence_commit) in ACCEPTED_OBJECTS.items():
  row=rows[module];expected=source_binding(spec[key]['object'])
  require(row['accepted_evidence_commit']==evidence_commit,'Accepted-object evidence authority differs')
  require(row['object']==expected and expected['sha256']==expected_hash and expected['bytes']==size,'Accepted-object supplement is not the exact reviewed immutable object: '+module)
  require(expected['path'] not in result,'Accepted-object supplement path conflict')
  result[expected['path']]=copy.deepcopy(expected)
 return result
def reviewed_adapter_data(commit):
 exact_adapter_commit(commit);protected={};data={}
 for name in REVIEW_FILES:
  p=HERE/name;blob=subprocess.check_output(['git','show',commit+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  row,body=regular(p);require(body==blob,'Unreviewed adapter policy data');protected[str(p)]=row;data[name]=json.loads(body)
 return data,protected
