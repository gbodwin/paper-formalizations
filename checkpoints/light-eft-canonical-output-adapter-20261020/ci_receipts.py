"""Reviewed complete receipt verifier plus canonical same-run fixture prerequisite."""
from pathlib import Path
import json
from contracts import bind,require,TARGET
FROZEN='78cb40c7837db049d645d73696f2e0b724ce8a3b'
def decision_log_contract(stage,record,data):
 import child_runner as child
 bound=child.decision_log_bound(stage)
 require(record.get('decision_log_bound_bytes')==bound,'Decision log allowance differs')
 require(data and data.endswith(b'\n') and len(data)<=bound,'Incomplete/oversize decision log')

def verify_receipts(evidence,lease_record,plans,dependencies=None,wrapper_commit=None,expected_source=None,expected_identity=None):
 import child_runner as child
 import decision_telemetry as telemetry
 previous=0;ids=set()
 inventory=Path(evidence)/'inputs.jsonl';iref=bind(inventory)
 inputs={row['path']:row for row in map(json.loads,inventory.read_text().splitlines())}
 for p in plans:
  folder=Path(evidence)/p['stage'];r=json.loads((folder/'receipt.json').read_text())
  require(r.get('source_commit')==expected_source and r.get('frozen_import_source')==FROZEN,'Receipt source commits differ')
  if wrapper_commit is not None:require(r.get('wrapper_commit')==wrapper_commit,'Receipt wrapper commit differs')
  if dependencies is not None:require(r.get('effective_dependencies')==dependencies,'Receipt effective dependency binding differs')
  require(r.get('input_inventory_ref')==iref,'Receipt input journal differs')
  require(r['stage']==p['stage'] and r['argv']==p['argv'] and r['environment']==p['env'],'Receipt command/environment differs')
  require(r.get('working_directory')==p['cwd'] and r.get('planned_source_bindings')==p['source_bindings'],'Receipt cwd/source-binding translation differs')
  require(r['attempt_id'] not in ids,'Duplicate UUID');ids.add(r['attempt_id'])
  require(r['state']=='finished' and r['exit']==0 and not r.get('failure') and not r.get('cleanup_errors'),'Failed child receipt')
  require(r.get('preexec_binding_verified') and r.get('between_child_preservation_passed') and r.get('waitid_wait4_status_match'),'Missing binding/terminal checks')
  require(r.get('preexec_binding_strategy')=='exact identity/membership plus critical hashes','CI preexec strategy differs')
  require(r.get('preexec_identity_files',0)>=len(inputs) and r.get('preexec_critical_hashes',0)>0,'CI preexec coverage missing')
  require(r['runtime_wall_started_ns']<=r['preexec_validation_started_ns']<=r['preexec_validation_finished_ns']<=r['preexec_verified_ns'],'CI preexec validation timing differs')
  require(r.get('direct_reaped') and r.get('kernel_no_children_verified') and r.get('all_descendants_gone'),'Unreaped children')
  require((r['lock']['device'],r['lock']['inode'])==(lease_record['device'],lease_record['inode']),'Different lease identity')
  require(lease_record['acquired_ns']<=r['started_ns']<r['ended_ns']<=lease_record['release_ns'] and previous<r['started_ns'],'Receipt overlap/timing')
  previous=r['ended_ns']
  require([row['path'] for row in r.get('submitted_sources',[])]==p['sources'],'Incomplete or different submitted sources')
  for row in r['submitted_sources']:require(row['path'] in inputs and all(row[k]==inputs[row['path']][k] for k in ['sha256','bytes','identity']),'Submitted source/journal mismatch')
  require(r.get('kernel_limits_verified'),'Kernel limits not verified')
  expected_limits={'RLIMIT_AS':[12*1024**3]*2,'RLIMIT_CPU':[(90 if p['stage']=='audit' else 60)]*2,'RLIMIT_FSIZE':[(64 if p['stage']=='audit' else 16)*1024**2]*2,'RLIMIT_CORE':[0,0]}
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
  data=(folder/'samples.jsonl').read_bytes();decision_log_contract(p['stage'],r,data)
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
 if plans[0].get('module')==TARGET:
  from canonical_fixture import verify_schedule
  require(expected_identity is not None and expected_identity.get('GITHUB_SHA')==expected_source,'Canonical current-run identity required')
  verify_schedule(evidence,lease_record,plans,expected_identity)
 return True
