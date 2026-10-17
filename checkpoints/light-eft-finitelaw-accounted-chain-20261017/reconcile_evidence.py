"""Offline reconciliation of the single admission refusal; never retries execution."""
from pathlib import Path
import json,hashlib,subprocess,fcntl,datetime
B=Path(__file__).resolve().parent;E=B/'evidence/compile';r=json.loads((E/'receipt.json').read_text());state=json.loads((B/'chain-result.json').read_text());assert state['status']=='stopped-first-failure' and r.get('child_pid') is None
before=(E/'inputs-before.json').read_bytes();assert before==(E/'inputs-after.json').read_bytes();tool=json.loads((B/'toolchain-object-advice.json').read_text())['files'];expected_tool={x['path']:x for x in tool};assert len(expected_tool)==12594 and sum(x['bytes'] for x in tool)==2212380925
phases={}
for phase in ['before','after']:
 seen={};errors=[]
 with (E/f'hash-advice-{phase}.jsonl').open() as f:
  for line in f:
   row=json.loads(line)
   if row.get('error'):errors.append(row)
   if row.get('advice_scope')=='toolchain_immutable_object' and row.get('advised'):
    assert row['path'] not in seen;seen[row['path']]=row
    wanted=expected_tool[row['path']];assert row['sha256']==wanted['sha256'] and row['bytes']==wanted['bytes'] and row['identity']==wanted['identity']
 assert not errors and set(seen)==set(expected_tool)
 phases[phase]={'distinct_advised_tool_objects':len(seen),'advised_bytes':sum(x['bytes'] for x in seen.values()),'hashes_identities_match_pinned_inventory':True,'advice_errors':0,'measurement':r['toolchain_verification_measurements'][phase]}
with (B/'toolchain-advice-reconciliation.json').open('w') as f:json.dump({'phases':phases,'total_successful_tool_object_advice_calls':25188,'qualification':'Exactly 12594 files in each existing idle before/after verification phase; no separate inventory hunt or extra advice pass. Return values do not imply reclamation.'},f,indent=2);f.write('\n')
history=[json.loads(x) for x in (B/'history-advice.jsonl').read_text().splitlines()];expected_history={x['path']:x for x in json.loads((B/'history-whitelist.json').read_text())['files']};assert len(history)==407 and len({x['path'] for x in history})==407 and sum(x['bytes'] for x in history)==183081165
for row in history:assert row['verified_sha256']==expected_history[row['path']]['sha256'] and row['identity']==row['identity_after_advice']
for filename,row in r['completed_file_housekeeping'].items():
 data=Path(filename).read_bytes();assert row['state']=='completed' and len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'] and row['identity']==row['identity_after_advice']
tests=json.loads((B/'harmless-tests.json').read_text());assert all(tests['checks'].values()) and len(tests['fixtures'])==7
for fixture in tests['fixtures']:
 folder=B/Path(fixture['receipt']).parent;receipt=json.loads((B/fixture['receipt']).read_text());sample=json.loads((folder/'samples.jsonl').read_text());assert receipt['stop_decision_sample']==sample and receipt['exact_sample_retained'] and receipt['child_reaped'] and receipt['collection_before_kill_before_persist']
chunks=B/'chunks';chunks.mkdir(exist_ok=False);manifest={'reconstruction':'Concatenate listed part bytes in order without separators. Input inventory before/after is byte-identical.','inventories':[]}
items=[(E/'inputs-before.json',['../evidence/compile/inputs-before.json','../evidence/compile/inputs-after.json']),(E/'hash-advice-before.jsonl',['../evidence/compile/hash-advice-before.jsonl']),(E/'hash-advice-after.jsonl',['../evidence/compile/hash-advice-after.jsonl']),(B/'history-advice.jsonl',['../history-advice.jsonl']),(B/'toolchain-object-advice.json',['../toolchain-object-advice.json'])]
for file,targets in items:
 folder=chunks/file.name.replace('.','-');folder.mkdir();parts=[];pending=bytearray();whole=hashlib.sha256();size=0
 def flush():
  if not pending:return
  path=folder/f'part-{len(parts):03d}.txt';path.write_bytes(pending);parts.append({'path':str(path.relative_to(chunks)),'bytes':len(pending),'sha256':hashlib.sha256(pending).hexdigest()});pending.clear()
 with file.open('rb') as f:
  for line in f:
   whole.update(line);size+=len(line)
   if len(pending)+len(line)>200000:flush()
   pending.extend(line)
 flush();check=hashlib.sha256()
 for row in parts:
  data=(chunks/row['path']).read_bytes();assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'];check.update(data)
 assert check.hexdigest()==whole.hexdigest();manifest['inventories'].append({'reconstructs':targets,'bytes':size,'sha256':whole.hexdigest(),'parts':parts})
with (chunks/'manifest.json').open('w') as f:json.dump(manifest,f,indent=2);f.write('\n')
active=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if x.split()[-1] in ('lean','lake','leanchecker','leantar','strace')];assert not active
with open('/tmp/distance-sparsification-single-compiler.lock') as f:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);assert Path(f.name).stat().st_ino==3849
z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attempt_id':r['attempt_id'],'result':'POST_VERIFICATION_ADMISSION_REFUSED_ZERO_CHILDREN','required_headroom_bytes':3758096384,'actual_headroom_bytes':r['admission']['headroom'],'shortfall_bytes':3758096384-r['admission']['headroom'],'host_available_bytes':r['admission']['system_available'],'compiler_children':0,'resolver_children':0,'checker_children':0,'fresh_objects':r['output_inventory_after'],'input_rows':len(json.loads(before)),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(before).hexdigest(),'toolchain_objects_per_existing_verification_phase':12594,'toolchain_bytes_per_phase':2212380925,'toolchain_advice_phases':2,'toolchain_advice_expected_hashes_identities_verified':True,'history_files':407,'history_bytes':183081165,'history_hashes_identities_verified':True,'completed_new_files':len(r['completed_file_housekeeping']),'completed_new_files_verified':True,'seven_exact_full_or_partial_sample_fixtures_verified':True,'actual_runtime_decision_sample_available':False,'kernel_no_children_verified':r['kernel_no_children_verified'],'preserved_inputs_verified':r['preserved_inputs_verified'],'common_lock_free':True,'active_compilers_tracers':active,'no_retry_or_post_attempt_configuration_change':True,'packaging_after_chain_end':True}
with (B/'result-reconciliation.json').open('w') as f:json.dump(z,f,indent=2);f.write('\n')
print('Verified',z['input_rows'],'inputs; 12594 tool objects in each of two idle phases; seven exact-sample fixtures;',sum(len(x['parts']) for x in manifest['inventories']),'chunks; no children, lock free.')
