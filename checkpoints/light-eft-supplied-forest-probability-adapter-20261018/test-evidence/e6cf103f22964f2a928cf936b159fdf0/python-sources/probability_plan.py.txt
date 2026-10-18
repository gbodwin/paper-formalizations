"""Exact reviewed-draft reader and explicit per-command schema translation.

No execution or locking API. Draft source 88d297fa is distinct from the adapter
review commit and the older deterministic payload origin 40029953.
"""
from pathlib import Path
import collections,copy,json,re,subprocess
from contracts import TARGET,THEOREM,STAGES,require,regular,bind
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
DRAFT_DIR=ROOT/'checkpoints/light-eft-supplied-forest-probability-draft-20261018'
DRAFT_COMMIT='88d297fa58a15406aac6e7c0ea3c85f65965d19a'
OLD_SOURCE_COMMIT='40029953e9e53525f0f1f431d6d56333b05183a3'
SOURCE_SLOT='UNBOUND_REQUIRES_EXACT_REVIEWED_DRAFT_COMMIT'
ADAPTER_SLOT='UNBOUND_REQUIRES_EXACT_REVIEWED_ADAPTER_COMMIT'
ACCEPTED_MODULE='LightEFTSuppliedForestStage.SuppliedForestGoodEvent'
ACCEPTED_HASH='b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18'
REVIEW_FILES=('released-lock.json','accepted-object-supplement.json')
PREFIXES=('LightEFTSpanners','LightSpanners','LightEFTSuppliedForestStage','LightEFTSuppliedForestProbabilityStage')
REQUIRED_INTERFACES=('LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests','LightEFTSpanners.SampledGreedy.polynomial_inaccurate_probability','LightEFTSpanners.FiniteProbability.Law.prob_mono')
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
def exact_adapter_commit(commit):
 require(isinstance(commit,str) and re.fullmatch('[0-9a-f]{40}',commit) is not None,'Exact adapter commit required; no placeholder')
 require(commit not in {DRAFT_COMMIT,OLD_SOURCE_COMMIT,'2d75404bfd140d0e8ecb13d3c2554b853b9a1640','78cb40c7837db049d645d73696f2e0b724ce8a3b'},'Draft/origin/frozen/old implementation is not this adapter review')
 return commit
def source_binding(row):
 require(isinstance(row,dict) and set(row)=={'path','bytes','sha256','identity'},'Per-command source-binding schema differs')
 require(Path(row['path']).is_absolute() and type(row['bytes']) is int and row['bytes']>=0 and re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'Invalid source binding')
 require(isinstance(row['identity'],list) and len(row['identity'])==5 and all(type(v) is int for v in row['identity']),'Invalid source identity binding')
 return row
def normalize_plan(raw):
 require(raw['module']==TARGET and raw['theorem']==THEOREM,'Wrong draft target/theorem')
 require(raw['project_dependency_count']==213 and raw['expected_project_module_import_count_including_new_target']==214,'Wrong dependency/import scope')
 require(tuple(raw['project_namespace_prefixes'])==PREFIXES,'Wrong four project prefixes')
 require(raw['stage_order']==list(STAGES) and [c['stage'] for c in raw['commands']]==list(STAGES),'Wrong four-stage order')
 work=Path(raw['future_work_root']);require(work.is_absolute(),'Nonabsolute reviewed work root')
 require(raw['new_object']==str(work/'objects'/Path(*TARGET.split('.')).with_suffix('.olean')),'Wrong target object path')
 expected_sources={'source':DRAFT_DIR/'staged/LightEFTSuppliedForestProbabilityStage/PolynomialFailureProbability.lean','audit':DRAFT_DIR/'staged/PolynomialSuppliedForestProbabilityAudit.lean','resolver':DRAFT_DIR/'staged/ResolvePolynomialSuppliedForestTarget.lean'}
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
 require(manifest_path.read_bytes()==blob,'Reviewed draft manifest differs');rows=json.loads(blob)
 require(len(rows)==23 and len({r['path'] for r in rows})==23,'Reviewed draft manifest membership differs')
 protected={str(manifest_path):bind(manifest_path)}
 for row in rows:
  name=Path(row['path']);require(not name.is_absolute() and '..' not in name.parts,'Unsafe reviewed draft path')
  p=DRAFT_DIR/name;expected=subprocess.check_output(['git','show',DRAFT_COMMIT+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  binding,actual=regular(p);require(actual==expected,'Reviewed draft artifact differs');bind(p,row);protected[str(p)]=binding
 raw=json.loads((DRAFT_DIR/'focused-validation-plan.json').read_text());spec=normalize_plan(raw)
 for key in ['source','audit','resolver']:require(bind(raw[key]['path'])==raw[key],'Reviewed staged source identity/content differs')
 require(spec['profile']==json.loads((ROOT/'checkpoints/light-eft-supplied-forest-package-20261018/execution-proposal.json').read_text())['profile'],'Resource profile differs from accepted bounded profile')
 return spec,json.loads((DRAFT_DIR/'project-dependency-bindings.json').read_text()),protected
def accepted_supplement(policy,spec):
 expected=spec['accepted_deterministic_dependency']['object']
 require(policy['module']==ACCEPTED_MODULE and policy['reviewed_draft_commit']==DRAFT_COMMIT and policy['accepted_evidence_commit']=='7eedd5b3c7860cf473f5deff3b4ed369f19e6e61','Accepted-object supplement authority differs')
 require(policy['object']==expected and expected['sha256']==ACCEPTED_HASH and expected['bytes']==185576,'Accepted-object supplement is not the exact reviewed b5 object')
 return copy.deepcopy(expected)
def reviewed_adapter_data(commit):
 exact_adapter_commit(commit);protected={};data={}
 for name in REVIEW_FILES:
  p=HERE/name;blob=subprocess.check_output(['git','show',commit+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  row,body=regular(p);require(body==blob,'Unreviewed adapter policy data');protected[str(p)]=row;data[name]=json.loads(body)
 return data,protected
