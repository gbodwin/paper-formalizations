"""Finite two-module shared-package context; resource/lifecycle engine is reused."""
from pathlib import Path
import json,shutil,time
from contracts import bind,regular,require,unchanged,tree,outputs,SUFFIXES,EXPORTS,warning_lines
from ci_inventory import CIIdentityGuard
from package_selection import selected_path
from finite_contract import CONTRACT
from output_guards import focused_contract,live_objects,live_tree
from audit_check import validate,export_all,chunk

class FocusedContext:
 def __init__(self,lease,work,evidence,plans,roots,dependencies,identity,inputs,inventory,classified):
  self.lease=lease;self.lock=lease.file;self.acquired_ns=lease.acquired_ns
  self.work=Path(work);self.objects=self.work/'objects';self.evidence=Path(evidence)
  self.plans=plans;self.roots=roots;self.base_dependencies=dependencies;self.identity=identity
  self.source_commit=identity['GITHUB_SHA'];self.wrapper_commit=self.source_commit;self.fixture=False
  self.inputs=inputs;self.inv=inventory;self.classified=classified;self.new={};self.resolved={};self.audit_files={}
  self.evidence_files={}
  self.seen=[];self.audit_results={};self.preservation_failed=False;self.active=None
  self.journals={};self.excluded={}
  for case in ['PaidFlagSerialization','PaidFlagSampleComposition','PaidFlagFixtures']:
   folder=self.evidence/case;folder.mkdir(parents=True)
   for name,rows in [('inputs.jsonl',inputs),('excluded-metadata-initial.jsonl',classified['excluded'])]:
    path=folder/name
    with path.open('x') as f:
     for key in sorted(rows):f.write(json.dumps(rows[key],separators=(',',':'))+'\n')
    (self.journals if name=='inputs.jsonl' else self.excluded)[case]=bind(path)
   (self.work/'audit'/case/'ci-evidence').mkdir(parents=True)

 def visible_gate(self,p):return (4 if p['stage'] in ['replay','audit'] else 3)*1024**3
 def target(self,module):return self.objects/Path(*module.split('.')).with_suffix('.olean')
 def parts(self,module):return {str(self.target(module))[:-len('.olean')]+s for s in SUFFIXES}
 def dependencies(self,p):
  names=CONTRACT['imports'][p['module']] if p['module'] in CONTRACT['modules'] else sorted(set(self.base_dependencies)|set(CONTRACT['modules']))
  result={}
  for m in names:
   result[m]=dict(self.base_dependencies[m]) if m in self.base_dependencies else dict(self.new[str(self.target(m))],module=m)
  return result
 def protected(self):return {**self.new,**self.resolved,**self.audit_files,**self.evidence_files}
 def spec(self,p):
  module=p['module'];fixture=module=='PaidFlagFixtures';mods=CONTRACT['modules']
  old=mods if fixture else mods[:mods.index(module)]
  oldparts={k:v for k,v in self.new.items() if any(k in self.parts(m) for m in old)}
  case=p['case'];protected={**self.protected(),self.journals[case]['path']:self.journals[case],self.excluded[case]['path']:self.excluded[case]}
  return dict(stage=p['stage'],objects=str(self.objects),target=str(self.target(mods[-1] if fixture else module)),
   audit=str(self.work/'audit'/case/'ci-evidence'),protected=protected,
   focused=dict(mode='fixtures' if fixture else 'module',module=module,work=str(self.work),completed_modules=old,
    completed=sorted(oldparts),completed_resolution=sorted(self.resolved),completed_audit=sorted(self.audit_files)))
 def check_selection(self,p):
  deps=self.dependencies(p)
  for m,row in deps.items():
   expected=Path(row['path']);matches=[Path(r)/Path(*m.split('.')).with_suffix('.olean') for r in self.roots]
   require([x for x in matches if x.exists() or x.is_symlink()]==[expected],'Missing/shadowed dependency: '+m)
   require(selected_path(self.roots,m)==expected,'First-package selection masks dependency: '+m)
  if p['module'] in CONTRACT['modules']:
   m=p['module'];expected=self.target(m);matches=[]
   for root in self.roots:
    leaf=Path(root)/Path(*m.split('.')).with_suffix('.olean');prefix=Path(root)/Path(*m.split('.'))
    if leaf.exists() or leaf.is_symlink():matches.append((m,str(leaf)))
    if prefix.exists():matches.extend((m+'.'+'.'.join(q.relative_to(prefix).with_suffix('').parts),str(q)) for q in prefix.rglob('*.olean'))
   complete=p['stage']!='compile'
   require(matches==([(m,str(expected))] if complete or expected.exists() else []),'Missing/prefix-expanded/shadowed target')
   require(selected_path(self.roots,m)==expected,'Focused output package is masked')
  return dict(model='first top-level package marker; no missing-leaf fallback',selected={m:r['path'] for m,r in deps.items()})
 def verify(self,p,complete=False):
  self.lease.check()
  # Inventory scan hashes every semantic search input once; other critical inputs
  # are hashed separately. No redundant second semantic read is substituted.
  self.inv.scan()
  semantic=self.classified['semantic']
  unchanged({k:v for k,v in self.inputs.items() if k not in semantic});unchanged(self.protected())
  unchanged({r['path']:r for r in [*self.journals.values(),*self.excluded.values()]})
  spec=self.spec(p);dummy=dict(stage=p['stage'],argv=p['argv'],working_directory=p['cwd'],focused_module=p['module'])
  focused_contract(dummy,spec)
  if p['module']=='PaidFlagFixtures':files=live_tree(self.objects,set(self.new))
  else:files=live_objects(self.objects,self.target(p['module']),complete or p['stage']!='compile',completed=spec['focused']['completed'])
  if p['stage']!='compile' or p['module']=='PaidFlagFixtures':require(set(files)==set(self.new),'Completed object membership changed')
  self.check_selection(p)
 def before_child(self,p,r,save):
  require(p==self.plans[len(self.seen)],'Out-of-order/extra focused stage');self.active=p
  self.verify(p)
  if p['stage']=='compile' and p['module']!='PaidFlagFixtures':
   require(not any(Path(x).exists() or Path(x).is_symlink() for x in self.parts(p['module'])),'Current target outputs not absent before compile')
  if p['stage']=='resolve':
   path=self.work/'resolution'/(p['case']+'.json');require(not path.exists() and not path.is_symlink(),'Resolver output not absent before resolve')
  if p['stage']=='audit':require(not list((self.work/'audit'/p['case']/'ci-evidence').iterdir()),'Audit outputs not absent before audit')
  folder=self.evidence/p['case']/p['stage'];submitted=[]
  for path in p['sources']:
   row,data=regular(path);require(self.inputs.get(path)==row,'Submitted source not frozen')
   name=row['sha256']+'.source';snapshot=folder/name;snapshot.write_bytes(data);self.evidence_files[str(snapshot)]=bind(snapshot,row);submitted.append(dict(row,snapshot=name))
  r.update(CI_identity=self.identity,dependency_qualification='NEWLY_OBSERVED_ORDINARY_CI_DEPENDENCIES; no historical object/provenance continuity',
   focused_module=p['module'],focused_case=p['case'],working_directory=p['cwd'],planned_source_bindings=p['source_bindings'],submitted_sources=submitted,
   effective_dependencies=self.dependencies(p),input_inventory_ref=self.journals[p['case']],excluded_initial_metadata=self.excluded[p['case']],
   signature_supplement=dict(qualification='Fresh exact byte/identity binding; unauthenticated cache provenance'),
   package_selection=self.check_selection(p),output_guard_spec=self.spec(p),focused_stage_outputs_absent_before_exec=True,between_child_preservation_passed=False)
  save()
 def prepare_child(self,p,r,save,accounting):
  import child_runner as child
  self.verify(p);child.assert_idle('focused-fresh-'+p['stage'],r)
  now=accounting.sample();child.check_memory(now,now,self.visible_gate(p));require(now['system_available']>=3*1024**3,'Host below admission')
  free=shutil.disk_usage(self.work).free;require(free>2*1024**3,'Disk below boundary')
  critical={k:v for k,v in self.inputs.items() if k not in self.classified['semantic']}
  critical.update(self.protected());critical.update({x['path']:x for x in [self.journals[p['case']],self.excluded[p['case']]]})
  for row in r['submitted_sources']:
   path=self.evidence/p['case']/p['stage']/row['snapshot'];critical[str(path)]=bind(path,row)
  tracked={**self.inputs,**self.classified['excluded'],**critical}
  members={root:set(files)|{d for d in self.classified['directories'] if d!=root and Path(d).is_relative_to(root)} for root,files in self.classified['members'].items()}
  members[str(self.work)]={str(x) for x in self.work.rglob('*')}
  self.guard=CIIdentityGuard(tracked,members,self.classified['directories']);self.critical=critical;self.prepared=json.loads(json.dumps(p))
  r.update(admission=now,disk_admission_bytes=free);save();return now
 def preexec(self,p,r,save):
  began=time.monotonic_ns();self.lease.check();require(p==self.prepared==self.plans[len(self.seen)],'Unprepared/mutated focused plan')
  self.guard.verify();unchanged(self.critical);self.lease.check()
  free=shutil.disk_usage(self.work).free;require(free>2*1024**3,'Preexec disk below boundary')
  r.update(preexec_disk_bytes=free,preexec_binding_verified=True,preexec_binding_strategy='exact identity/membership plus critical hashes',
   preexec_identity_files=len(self.guard.bindings),preexec_critical_hashes=len(self.critical),
   preexec_validation_started_ns=began,preexec_validation_finished_ns=time.monotonic_ns());save()
 def after_child(self,p,r,save):
  success=r.get('exit')==0 and 'failure' not in r
  self.verify(p,complete=success and p['module']!='PaidFlagFixtures')
  if success:
   stage=p['stage'];module=p['module'];raw=(self.evidence/p['case']/stage/'raw.log').read_text()
   require(not warning_lines(raw),'Lean warning/error diagnostic')
   if stage=='compile' and module!='PaidFlagFixtures':
    observed=tree(self.objects);new={k:v for k,v in observed.items() if k in self.parts(module)}
    require(str(self.target(module)) in new,'Missing focused compiled object');self.new.update(new)
   if stage=='resolve':
    path=self.work/'resolution'/(p['case']+'.json');data=json.loads(path.read_text())
    require(data['target']==module and data['count']==1 and data['resolved']==[dict(module=module,object=str(self.target(module)))],'Official singleton resolution differs')
    require(list(dict.fromkeys(data['search_path']))==list(map(str,self.roots)),'Official search path differs');self.resolved[str(path)]=bind(path)
   if stage=='replay':require(raw.strip()=='replaying '+module,'Not exact singleton replay diagnostic')
   if stage=='audit':
    directory=self.work/'audit'/p['case']/'ci-evidence';self.audit_results[module]=validate(directory,self.dependencies(p),raw,module)
    # Bind every actually loaded primary object, including nonproject imports.
    for m in (directory/'import-closure-loaded.txt').read_text().splitlines():
     paths=[Path(root)/Path(*m.split('.')).with_suffix('.olean') for root in self.roots];matches=[x for x in paths if x.exists()]
     require(len(matches)==1,'Loaded object missing/shadowed: '+m);path=str(matches[0])
     require(path in self.inputs or path in self.new,'Unbound loaded object: '+m);bind(path,self.inputs.get(path,self.new.get(path)))
    self.audit_files.update(tree(directory))
    export_all(directory,self.evidence/p['case']/stage/'raw.log',self.evidence/p['case']/'exports')
   self.seen.append(p)
  r['between_child_preservation_passed']=True;save()
 def complete_log(self,path,r,save):
  row=bind(path);r.setdefault('completed_logs',{})[Path(path).name]=row;self.evidence_files[str(path)]=row;save()
 def output_summary(self):return dict(new_objects=list(self.new.values()),resolution=list(self.resolved.values()),audit=list(self.audit_files.values()),sealed_evidence=list(self.evidence_files.values()))
 def finish(self):
  require(self.seen==self.plans and set(self.audit_results)==set(CONTRACT['modules']),'Incomplete focused schedule')
  self.verify(self.plans[-1]);return dict(audits=self.audit_results,preserved=True,outputs=self.output_summary())
