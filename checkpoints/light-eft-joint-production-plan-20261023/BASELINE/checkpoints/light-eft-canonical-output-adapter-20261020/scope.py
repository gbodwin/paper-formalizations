"""Preserved Context methods; only new finite contracts/audit module data are used."""
from pathlib import Path
import collections,json,os,shutil,subprocess
from contracts import *
from focused_audit import validate,export_all,verify_chunks,chunk
class Context:
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
