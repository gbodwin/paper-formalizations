"""Exact source/effective-input scope and four-stage context. No launch on import."""
from pathlib import Path
import collections,json,os,shutil,subprocess
from contracts import *
from focused_audit import validate,export_all,verify_chunks,chunk
ROOT=Path(__file__).resolve().parents[2]
APPROVED='88d297fa58a15406aac6e7c0ea3c85f65965d19a'
LEGACY_APPROVED='40029953e9e53525f0f1f431d6d56333b05183a3'
FROZEN='78cb40c7837db049d645d73696f2e0b724ce8a3b'
DRAFT=ROOT/'checkpoints/light-eft-supplied-forest-draft-20261018'
def manifest_contract(rows,count):
 require(len(rows)==count and len({r['path'] for r in rows})==count,'Manifest count/uniqueness')
 for r in rows:
  p=Path(r['path'])
  require(not p.is_absolute() and '..' not in p.parts and str(p)==r['path'],'Unsafe manifest path')
def legacy_dependency_contract(rows):
 require(len(rows)==196 and len({r['module'] for r in rows})==196,'Expected 196 distinct project dependencies')
 require(collections.Counter(r['module'].split('.')[0] for r in rows)=={'LightEFTSpanners':140,'LightSpanners':56},'196-closure namespace counts')
 require(TARGET not in {r['module'] for r in rows},'New module cannot be an accepted input')
def dependency_contract(rows):
 require(len(rows)==213 and len({r['module'] for r in rows})==213,'Expected exactly 213 distinct dependencies')
 require(collections.Counter(r['module'].split('.')[0] for r in rows)=={'LightEFTSpanners':156,'LightSpanners':56,'LightEFTSuppliedForestStage':1},'213-dependency namespace scope differs')
 from probability_plan import ACCEPTED_MODULE,ACCEPTED_HASH
 accepted=[r for r in rows if r['module']==ACCEPTED_MODULE]
 require(len(accepted)==1 and accepted[0]['sha256']==ACCEPTED_HASH,'Exact accepted staged dependency missing/wrong')
 require(TARGET not in {r['module'] for r in rows},'Draft target cannot be a dependency')
def reviewed_base_inputs():
 """Read-only production binding; does not create a work root or lock."""
 anchor=DRAFT/'manifest.json'
 blob=subprocess.check_output(['git','show',LEGACY_APPROVED+':'+str(anchor.relative_to(ROOT))],cwd=ROOT)
 _,actual=regular(anchor);require(actual==blob,'Unreviewed checkpoint manifest')
 manifest=json.loads(actual);manifest_contract(manifest,13)
 protected={}
 for name in [r['path'] for r in manifest]+['manifest.json']:
  p=DRAFT/name
  blob=subprocess.check_output(['git','show',LEGACY_APPROVED+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  row,b=regular(p);require(b==blob,'Approved checkpoint bytes differ');protected[str(p)]=row
 for row in manifest:bind(DRAFT/row['path'],row)
 supervisors=json.loads((DRAFT/'supervisor-bindings.json').read_text());manifest_contract(supervisors,10)
 for row in supervisors:
  p=ROOT/row['path'];protected[str(p)]=bind(p,row)
 j=json.loads((DRAFT/'accepted-imports.json').read_text())
 legacy_dependency_contract(j['bindings'])
 for row in j['bindings']:bind(row['path'],row)
 spec=json.loads((DRAFT/'execution-proposal.json').read_text())
 for row in spec['tool_hash_bindings']:protected[row['path']]=bind(row['path'],row)
 for row in [spec['new_source'],spec['audit_source'],spec['resolver_source']]:protected[row['path']]=bind(row['path'],row)
 graph=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/frozen-graph.json'
 bind(graph,{'sha256':json.loads((DRAFT/'environment.json').read_text())['frozen_graph_sha256']})
 for row in json.loads(graph.read_text()):protected[str(ROOT/row['path'])]=bind(ROOT/row['path'],row)
 for pin in ['lean-toolchain','lake-manifest.json']:
  p=ROOT/pin;b=subprocess.check_output(['git','show',FROZEN+':'+pin],cwd=ROOT)
  row,actual=regular(p);require(actual==b,'Pin changed');protected[str(p)]=row
 inventory=ROOT/j['accepted_full_input_inventory']['path']
 protected[str(inventory)]=bind(inventory,j['accepted_full_input_inventory'])
 return spec,j,protected
def reviewed_inputs(commit):
 from probability_plan import read_reviewed_draft,reviewed_adapter_data,accepted_supplement,ACCEPTED_MODULE,exact_adapter_commit
 exact_adapter_commit(commit)
 base,_,protected=reviewed_base_inputs()
 spec,closure,extra=read_reviewed_draft();protected.update(extra)
 policy,extra=reviewed_adapter_data(commit);protected.update(extra)
 require(spec['profile']==base['profile'],'Changed resource profile')
 accepted=accepted_supplement(policy['accepted-object-supplement.json'],spec)
 rows=[]
 for record in closure['dependencies']:
  source=record['source'];protected[source['path']]=bind(source['path'],source)
  obj=bind(record['object']['path'],record['object'])
  if record['module']==ACCEPTED_MODULE:require(obj==accepted,'Accepted-object immutable identity/content differs')
  rows.append(dict(obj,module=record['module']));protected[obj['path']]=obj
 dependency_contract(rows)
 return spec,dict(bindings=rows),protected
def reviewed_wrapper(commit):
 require(isinstance(commit,str) and len(commit)==40 and all(c in '0123456789abcdef' for c in commit),'Exact reviewed wrapper commit required')
 here=Path(__file__).resolve().parent;files=sorted(here.glob('*.py'))
 prefix=str(here.relative_to(ROOT))
 tracked=subprocess.check_output(['git','ls-tree','-r','--name-only',commit,'--',prefix],cwd=ROOT,text=True).splitlines()
 require({p for p in tracked if Path(p).parent==here.relative_to(ROOT) and p.endswith('.py')}=={str(p.relative_to(ROOT)) for p in files},'Reviewed wrapper Python membership differs')
 for p in files:
  blob=subprocess.check_output(['git','show',commit+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  require(p.read_bytes()==blob,'Wrapper code differs from reviewed commit')
 from probability_plan import REVIEW_FILES,exact_adapter_commit
 exact_adapter_commit(commit)
 require(not any(p.startswith(prefix+'/staged/') for p in tracked),'Adapter must use only the original reviewed draft staged sources')
 for name in REVIEW_FILES:
  p=here/name;blob=subprocess.check_output(['git','show',commit+':'+str(p.relative_to(ROOT))],cwd=ROOT)
  require(p.read_bytes()==blob,'Package data/source differs from reviewed commit');files.append(p)
 return {str(p):bind(p) for p in files}
class Context:
 def __init__(self,work,evidence,lease,plans,roots,dependencies,inputs,fixture=False,source_commit=APPROVED,wrapper_commit=None):
  self.work=Path(work);self.evidence=Path(evidence);self.lease=lease;self.lock=lease.file
  self.acquired_ns=lease.acquired_ns;self.plans=json.loads(json.dumps(plans));self.roots=list(map(Path,roots));self.dependencies=json.loads(json.dumps(dependencies))
  self.fixture=fixture;self.source_commit=source_commit;self.wrapper_commit=wrapper_commit
  self.inputs={str(p):bind(p,row) for p,row in inputs.items()};self.new={};self.resolved={}
  self.objects=self.roots[0];self.target=self.objects/Path(*TARGET.split('.')).with_suffix('.olean')
  self.resolution=self.work/'resolution.json';self.audit=self.work/'audit/ci-evidence'
  for plan in self.plans:require(plan['env'].get('LEAN_PATH')==':'.join(map(str,self.roots)),'Environment/effective search roots differ')
  self.preservation_failed=False;self.seen=[];self.audit_result=None
  self.inventory_policy=None;self.signature_ref=None;self.excluded_ref=None
  if self.fixture:
   self.members={str(r):set(tree(r)) for r in self.roots[1:]}
  else:
   from semantic_inventory import load_inventory
   self.inventory_policy,_,self.signature_ref=load_inventory(wrapper_commit,plans,work,self.roots[1:])
   classified=self.inventory_policy.scan();self.members=classified['members']
   require(all(self.inputs.get(k)==v for k,v in classified['semantic'].items()),'Classified semantic input/journal mismatch')
   excluded=self.evidence/'excluded-metadata-initial.jsonl'
   self.write_metadata(excluded,classified['excluded']);self.excluded_ref=bind(excluded)
  inventory=self.evidence/'inputs.jsonl'
  with inventory.open('x') as f:
   for row in self.inputs.values():f.write(json.dumps(row,separators=(',',':'))+'\n')
  self.input_ref=bind(inventory)
  require(not list(self.objects.rglob('*')),'New output tree must be initially empty')
  self.audit.mkdir(parents=True,exist_ok=False)
 def visible_gate(self,plan):return (4 if plan['stage'] in ['replay','audit'] else 3)*1024**3
 def verify(self,compiled):
  self.lease.check();unchanged(self.inputs);unchanged(self.new);unchanged(self.resolved)
  require(bind(self.input_ref['path'])==self.input_ref,'Canonical input journal changed')
  if self.inventory_policy is None:
   for root,files in self.members.items():require(set(tree(root))==files,'Accepted search-tree membership drift')
  else:
   classified=self.inventory_policy.scan()
   require(classified['members']==self.members,'Classified search-tree membership drift')
   require(all(self.inputs.get(k)==v for k,v in classified['semantic'].items()),'Semantic input changed')
   require(bind(self.excluded_ref['path'])==self.excluded_ref,'Initial excluded metadata journal changed')
  self.package_selection=effective(self.roots,self.dependencies,self.target,compiled)
 def write_metadata(self,path,rows):
  with Path(path).open('x') as f:
   for p in sorted(rows):f.write(json.dumps(rows[p],separators=(',',':'))+'\n')
 def before_child(self,plan,record,save_receipt):
  require(plan==self.plans[len(self.seen)],'Out-of-order/mutated/extra stage')
  self.verify(bool(self.seen))
  require(plan['cwd']==str(self.work/'audit' if plan['stage']=='audit' else self.work),'Per-command cwd binding differs')
  require([r['path'] for r in plan['source_bindings']]==plan['sources'],'Translated source binding order differs')
  for expected in plan['source_bindings']:
   require(self.inputs.get(expected['path'])==expected,'Translated submitted source binding differs from frozen inputs')
  if plan['stage']=='audit':require(not list(self.audit.iterdir()),'Audit outputs not absent before exec')
  # Fixture entry points only run exact explicit Python fixture plans; never Lean.
  if self.fixture:
   import sys
   require(Path(plan['argv'][0]).resolve()==Path(sys.executable).resolve(),'Fixture would execute non-Python tool')
  self.stage_evidence=self.evidence/plan['stage'];record['submitted_sources']=[]
  for p in plan['sources']:
   row,b=regular(p);require(str(p) in self.inputs and row==self.inputs[str(p)],'Submitted source not in frozen input set')
   snapshot=self.stage_evidence/(row['sha256']+'.source')
   snapshot.write_bytes(b);record['submitted_sources'].append(dict(row,snapshot=snapshot.name))
  record.update(working_directory=plan['cwd'],planned_source_bindings=plan['source_bindings'],package_selection=self.package_selection,signature_supplement=self.signature_ref,excluded_initial_metadata=self.excluded_ref,
   stage_kind='supplied_forest_'+plan['stage'],output_guard_spec=dict(stage=plan['stage'],objects=str(self.objects),
   target=str(self.target),audit=str(self.audit),protected={**self.new,**self.resolved,self.input_ref['path']:self.input_ref}),
   effective_dependencies=self.dependencies,new_object_bindings=dict(self.new),resolution_bindings=dict(self.resolved),
   source_outputs_absent_before_exec=not list(self.audit.iterdir()),between_child_preservation_passed=False)
  save_receipt()
 def prepare_child(self,plan,record,save_receipt,accounting):
  import child_runner as child
  self.verify(bool(self.seen));child.assert_idle('fresh-'+plan['stage'],record)
  now=accounting.sample();child.check_memory(now,now,self.visible_gate(plan))
  require(now['system_available']>=3*1024**3,'Host admission below3GiB')
  record['disk_admission_bytes']=shutil.disk_usage(self.work).free
  require(record['disk_admission_bytes']>2*1024**3,'Disk admission not >2GiB')
  record['admission']=now;record['input_inventory_ref']=self.input_ref;save_receipt();return now
 def preexec(self,plan,record,save_receipt):
  self.verify(bool(self.seen));record['preexec_disk_bytes']=shutil.disk_usage(self.work).free
  require(record['preexec_disk_bytes']>2*1024**3,'Fresh preexec disk below boundary')
  record['preexec_binding_verified']=True;save_receipt()
 def after_child(self,plan,record,save_receipt):
  self.verify(self.target.exists())
  if record.get('exit')==0 and 'failure' not in record:
   stage=plan['stage']
   if stage=='compile':self.new=object_outputs(self.objects,self.target,True)
   if stage=='resolve':self.resolved={str(self.resolution):resolution(self.resolution,self.roots,self.target)}
   if stage=='replay':
    require((self.stage_evidence/'raw.log').read_text().strip()=='replaying '+TARGET,'Not exact singleton replay diagnostic')
   if stage=='audit':
    raw=(self.stage_evidence/'raw.log').read_text()
    self.audit_result=validate(self.audit,self.dependencies,raw)
    # Every actual imported object must be uniquely present and bound. New target
    # binds to the freshly compiled object; imported dependencies to accepted inputs.
    loaded=(self.audit/'import-closure-loaded.txt').read_text().splitlines()
    for module in loaded:
     suffix=Path(*module.split('.')).with_suffix('.olean')
     matches=[r/suffix for r in self.roots if (r/suffix).exists()]
     require(len(matches)==1,'Actual imported module missing/shadowed: '+module)
     p=str(matches[0]);require(p in self.inputs or p in self.new,'Unbound actual imported object')
     bind(p,self.inputs.get(p,self.new.get(p)))
   self.seen.append(plan)
  record['between_child_preservation_passed']=True;save_receipt()
 def complete_log(self,path,record,save_receipt):
  record.setdefault('completed_logs',{})[path.name]=bind(path);save_receipt()
 def output_summary(self):return dict(new_objects=list(self.new.values()),resolution=list(self.resolved.values()))
 def finish(self):
  require([p['stage'] for p in self.seen]==list(STAGES),'Incomplete/failed four-stage batch')
  self.verify(True);require(self.audit_result is not None,'No accepted focused audit')
  exports=export_all(self.audit,self.evidence/'audit/raw.log',self.evidence/'exports')
  self.verify(True)
  input_export=chunk(self.input_ref['path'],self.evidence/'input-export')
  excluded_exports={}
  if self.inventory_policy is not None:
   final=self.inventory_policy.scan()
   path=self.evidence/'excluded-metadata-final.jsonl';self.write_metadata(path,final['excluded'])
   excluded_exports['initial']=chunk(self.excluded_ref['path'],self.evidence/'excluded-initial-export')
   excluded_exports['final']=chunk(path,self.evidence/'excluded-final-export')
  return dict(audit=self.audit_result,exports=exports,input_export=input_export,
   signature_supplement=self.signature_ref,excluded_metadata_exports=excluded_exports,preserved=True)
def verify_receipts(evidence,lease_record,plans,dependencies=None,wrapper_commit=None):
 import child_runner as child
 import decision_telemetry as telemetry
 previous=0;ids=set()
 inventory=Path(evidence)/'inputs.jsonl';iref=bind(inventory)
 inputs={row['path']:row for row in map(json.loads,inventory.read_text().splitlines())}
 for p in plans:
  folder=Path(evidence)/p['stage'];r=json.loads((folder/'receipt.json').read_text())
  require(r.get('source_commit')==APPROVED and r.get('frozen_import_source')==FROZEN,'Receipt source commits differ')
  if wrapper_commit is not None:require(r.get('wrapper_commit')==wrapper_commit,'Receipt wrapper commit differs')
  if dependencies is not None:require(r.get('effective_dependencies')==dependencies,'Receipt effective dependency binding differs')
  require(r.get('input_inventory_ref')==iref,'Receipt input journal differs')
  require(r['stage']==p['stage'] and r['argv']==p['argv'] and r['environment']==p['env'],'Receipt command/environment differs')
  require(r.get('working_directory')==p['cwd'] and r.get('planned_source_bindings')==p['source_bindings'],'Receipt cwd/source-binding translation differs')
  require(r['attempt_id'] not in ids,'Duplicate UUID');ids.add(r['attempt_id'])
  require(r['state']=='finished' and r['exit']==0 and not r.get('failure') and not r.get('cleanup_errors'),'Failed child receipt')
  require(r.get('preexec_binding_verified') and r.get('between_child_preservation_passed') and r.get('waitid_wait4_status_match'),'Missing binding/terminal checks')
  require(r.get('direct_reaped') and r.get('kernel_no_children_verified') and r.get('all_descendants_gone'),'Unreaped children')
  require((r['lock']['device'],r['lock']['inode'])==(lease_record['device'],lease_record['inode']),'Different lease identity')
  require(lease_record['acquired_ns']<=r['started_ns']<r['ended_ns']<=lease_record['release_ns'] and previous<r['started_ns'],'Receipt overlap/timing')
  previous=r['ended_ns']
  require([row['path'] for row in r.get('submitted_sources',[])]==p['sources'],'Incomplete or different submitted sources')
  for row in r['submitted_sources']:require(row['path'] in inputs and all(row[k]==inputs[row['path']][k] for k in ['sha256','bytes','identity']),'Submitted source/journal mismatch')
  require(r.get('kernel_limits_verified'),'Kernel limits not verified')
  expected_limits={'RLIMIT_AS':[12*1024**3]*2,'RLIMIT_CPU':[60]*2,'RLIMIT_FSIZE':[(64 if p['stage']=='audit' else 16)*1024**2]*2,'RLIMIT_CORE':[0,0]}
  require(r.get('handshake',{}).get('limits')==expected_limits,'Receipt limits differ')
  require(r.get('disk_admission_bytes',0)>2*1024**3 and r.get('preexec_disk_bytes',0)>2*1024**3,'No fresh disk admission')
  gate=(4 if p['stage'] in ['replay','audit'] else 3)*1024**3
  for admission in ['admission','preexec_admission']:
   child.check_memory(r[admission],r['admission'],gate)
   require(r[admission]['system_available']>=3*1024**3,'Recorded host below admission')
  identity=r['child_identity'];require(identity['pid']==r['child_pid'] and identity['ppid']==r['supervisor_pid'] and identity['sid']==identity['pgid']==r['child_pid'],'Child incarnation/ownership differs')
  terminal=r['terminal_confirmation'];require(terminal['terminal'] and terminal['pid']==r['child_pid'] and terminal['status']==0,'Terminal confirmation differs')
  require(r['runtime_wall_started_ns']<=r['preexec_verified_ns']<=terminal['finished_ns']<r['runtime_wall_started_ns']+90*10**9,'Launched child exceeded90seconds or bad preexec ordering')
  for row in r['submitted_sources']:bind(folder/row['snapshot'],row)
  for path,row in r.get('completed_logs',{}).items():bind(folder/path,row)
  data=(folder/'samples.jsonl').read_bytes();require(data and data.endswith(b'\n'),'No complete live runtime samples')
  samples=[json.loads(line) for line in data.splitlines()]
  require(samples[-1].get('exit_lifecycle',{}).get('terminal_confirmed'),'No final owned terminal sample')
  last=r['runtime_wall_started_ns']
  for sample in samples:
   require(last<=sample['sample_started_ns']<=sample['sample_finished_ns']<=r['ended_ns'],'Sample timing differs')
   last=sample['sample_finished_ns']
   who=sample['child'];require(who.get('pid')==r['child_pid'] and who.get('start_ticks')==identity['start_ticks'],'Sample belongs to another child incarnation')
   anonymous=r['anonymous_preexec_baseline'] if sample['sample_started_ns']>=r['preexec_verified_ns'] else None
   errors=telemetry.policy_errors(sample,r['admission'],anonymous,1024**3,6*1024**3,3*1024**3,child.check_memory)
   require(not errors,'Persisted live sample failed reviewed policy')
   require(sample['sample_finished_ns']<r['runtime_wall_started_ns']+90*10**9,'Runtime sample after wall deadline')
 require(len(ids)==4 and lease_record['state']=='released' and lease_record.get('kernel_echild') and not lease_record.get('release_errors'),'No clean owned ECHILD release')
 return True
