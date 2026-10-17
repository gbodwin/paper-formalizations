"""Offline export and reconciliation after the one-shot traced diagnostic ended."""
from pathlib import Path
import json,hashlib,subprocess,fcntl,datetime,os
B=Path(__file__).resolve().parent;E=B/'evidence/compile';r=json.loads((E/'receipt.json').read_text());state=json.loads((B/'chain-result.json').read_text());assert state['status']=='stopped-first-failure'
before=(E/'inputs-before.json').read_bytes();assert before==(E/'inputs-after.json').read_bytes()
chunks=B/'chunks';chunks.mkdir(exist_ok=False);manifest={'reconstruction':'Concatenate listed part bytes in order without separators. The final raw trace line is intentionally truncated by its hard file bound and must be preserved byte-for-byte.','inventories':[]}
items=[(E/'inputs-before.json',['../evidence/compile/inputs-before.json','../evidence/compile/inputs-after.json']),(E/'hash-advice-before.jsonl',['../evidence/compile/hash-advice-before.jsonl']),(E/'hash-advice-after.jsonl',['../evidence/compile/hash-advice-after.jsonl']),(B/'history-advice.jsonl',['../history-advice.jsonl']),(E/'syscalls.trace',['../evidence/compile/syscalls.trace']),(E/'map-samples.jsonl',['../evidence/compile/map-samples.jsonl']),(B/'mapping-records.jsonl',['../mapping-records.jsonl']),(B/'history-whitelist.json',['../history-whitelist.json'])]
for path,targets in items:
 folder=chunks/path.name.replace('.','-');folder.mkdir();parts=[];pending=bytearray();whole=hashlib.sha256();size=0
 def flush():
  if not pending:return
  p=folder/f'part-{len(parts):03d}.txt';p.write_bytes(pending);parts.append({'path':str(p.relative_to(chunks)),'bytes':len(pending),'sha256':hashlib.sha256(pending).hexdigest()});pending.clear()
 with path.open('rb') as f:
  for line in f:
   whole.update(line);size+=len(line)
   if len(pending)+len(line)>200000:flush()
   pending.extend(line)
 flush();check=hashlib.sha256()
 for row in parts:
  data=(chunks/row['path']).read_bytes();assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'];check.update(data)
 assert check.hexdigest()==whole.hexdigest();manifest['inventories'].append({'reconstructs':targets,'bytes':size,'sha256':whole.hexdigest(),'parts':parts})
with (chunks/'manifest.json').open('w') as f:json.dump(manifest,f,indent=2);f.write('\n')
history=[json.loads(line) for line in (B/'history-advice.jsonl').read_text().splitlines()];expected={x['path']:x for x in json.loads((B/'history-whitelist.json').read_text())['files']};assert len(history)==1184 and len({x['path'] for x in history})==1184 and sum(x['bytes'] for x in history)==537041913
for row in history:assert row['verified_sha256']==expected[row['path']]['sha256'] and row['identity']==row['identity_after_advice']
for path,row in r['completed_file_housekeeping'].items():
 data=Path(path).read_bytes();assert row['state']=='completed' and len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'] and row['identity']==row['identity_after_advice']
readable=B/'maps-readable';readable.mkdir();map_rows=[]
for i,line in enumerate((E/'map-samples.jsonl').read_text().splitlines()):
 row=json.loads(line);path=readable/f'snapshot-{i:03d}.maps';data=row.get('maps','').encode();path.write_bytes(data);map_rows.append({'path':path.name,'pid':row['pid'],'monotonic_ns':row['monotonic_ns'],'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'truncated':row.get('truncated'),'read_error':row.get('read_error')})
with (readable/'manifest.json').open('w') as f:json.dump({'source':'../evidence/compile/map-samples.jsonl','samples':map_rows},f,indent=2);f.write('\n')
active=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if x.split()[-1] in ('lean','lake','leanchecker','leantar','strace')];assert not active
with open('/tmp/distance-sparsification-single-compiler.lock') as f:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);assert Path(f.name).stat().st_ino==3849
actual_wait=next(x['wait_status'] for x in r['adopted_descendants_reaped'] if x['pid']==r['actual_lean_pid'])
z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attempt_id':r['attempt_id'],'result':'TRACE_FILE_BOUND_SIGXFSZ_COMPILER_TERMINATED_NO_NORMAL_COMPLETION','tracer_pid':r['tracer_pid'],'actual_lean_pid':r['actual_lean_pid'],'tracer_exit':r['exit'],'actual_lean_wait_status':actual_wait,'actual_lean_exit_interpretation':os.waitstatus_to_exitcode(actual_wait),'trace_bound_bytes':16777216,'trace_bytes':(E/'syscalls.trace').stat().st_size,'prior_failure_errno_captured':False,'normal_compiler_completion_established':False,'resolve_executions':0,'replay_executions':0,'fresh_objects':r['output_inventory_after'],'actual_limit_readback_verified':r['handshake']['limits']['RLIMIT_AS']==[3221225472,3221225472],'tracer_postfork_readback_verified':r['tracer_postfork_kernel_limits']['RLIMIT_AS']==[268435456,268435456],'history_count':len(history),'history_bytes':537041913,'history_hashes_identities_verified':True,'input_rows':len(json.loads(before)),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(before).hexdigest(),'completed_new_files':len(r['completed_file_housekeeping']),'completed_new_files_verified':True,'tracer_direct_reaped':r['tracer_direct_reaped'],'all_descendants_gone':r['all_descendants_gone'],'kernel_no_children_verified':r['kernel_no_children_verified'],'preserved_inputs_verified':r['preserved_inputs_verified'],'common_lock_free':True,'active_compilers_tracers':active,'no_retry':True,'no_configuration_adjustment_after_attempt':True,'packaging_after_end':True}
with (B/'result-reconciliation.json').open('w') as f:json.dump(z,f,indent=2);f.write('\n')
print('Verified:',z['input_rows'],'inputs;',len(history),'history rows;',sum(len(x['parts']) for x in manifest['inventories']),'chunks;',len(map_rows),'map snapshots; pair reaped, common lock free.')
