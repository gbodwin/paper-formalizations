"""Offline preservation/export after the refused diagnostic; never starts a tracer/compiler."""
from pathlib import Path
import json,hashlib,fcntl,subprocess,datetime
B=Path(__file__).resolve().parent;E=B/'evidence/compile'
state=json.loads((B/'chain-result.json').read_text());assert state['status']=='stopped-first-failure'
r=json.loads((E/'receipt.json').read_text());assert r.get('tracer_pid') is None and r.get('actual_lean_pid') is None
before=(E/'inputs-before.json').read_bytes();assert before==(E/'inputs-after.json').read_bytes()
chunks=B/'chunks';chunks.mkdir(exist_ok=False);manifest={'reconstruction':'Concatenate part bytes in listed order without separators. Inventory before/after files are identical.','inventories':[]}
for path,targets in [(E/'inputs-before.json',['../evidence/compile/inputs-before.json','../evidence/compile/inputs-after.json']),(E/'hash-advice-before.jsonl',['../evidence/compile/hash-advice-before.jsonl']),(E/'hash-advice-after.jsonl',['../evidence/compile/hash-advice-after.jsonl']),(B/'history-advice.jsonl',['../history-advice.jsonl'])]:
 folder=chunks/path.name.replace('.','-');folder.mkdir();parts=[];pending=bytearray();whole=hashlib.sha256();size=0
 def flush():
  if not pending:return
  out=folder/f'part-{len(parts):03d}.txt';out.write_bytes(pending);parts.append({'path':str(out.relative_to(chunks)),'bytes':len(pending),'sha256':hashlib.sha256(pending).hexdigest()});pending.clear()
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
history=[json.loads(x) for x in (B/'history-advice.jsonl').read_text().splitlines()];expected={x['path']:x for x in json.loads((B/'history-whitelist.json').read_text())['files']};assert len(history)==1560 and len({x['path'] for x in history})==1560 and sum(x['bytes'] for x in history)==710100227
for row in history:assert row['verified_sha256']==expected[row['path']]['sha256'] and row['identity']==row['identity_after_advice']
for name,row in r['completed_file_housekeeping'].items():
 data=Path(name).read_bytes();assert row['state']=='completed' and hashlib.sha256(data).hexdigest()==row['sha256'] and len(data)==row['bytes'] and row['identity']==row['identity_after_advice']
active=[line for line in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if line.split()[-1] in ('lean','lake','leanchecker','leantar','strace')];assert not active
with open('/tmp/distance-sparsification-single-compiler.lock') as lock:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert Path(lock.name).stat().st_ino==3849
z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attempt_id':r['attempt_id'],'result':'DIAGNOSTIC_ADMISSION_REFUSED','diagnostic_tracer_processes':0,'diagnostic_lean_processes':0,'harmless_capability_probe_exit':0,'actual_errno_captured':False,'configured_as_bytes':3221225472,'required_headroom_bytes':3758096384,'observed_headroom_bytes':r['admission']['headroom'],'shortfall_bytes':3758096384-r['admission']['headroom'],'host_memavailable':r['admission']['system_available'],'history_files':len(history),'history_bytes':710100227,'history_verified':True,'input_rows':len(json.loads(before)),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(before).hexdigest(),'new_completed_files':len(r['completed_file_housekeeping']),'new_completed_files_verified':True,'preserved_inputs_verified':r['preserved_inputs_verified'],'kernel_no_children_verified':r['kernel_no_children_verified'],'common_lock_free':True,'active_compilers_tracers':active,'no_retry':True,'packaging_after_end':True}
with (B/'result-reconciliation.json').open('w') as f:json.dump(z,f,indent=2);f.write('\n')
print('Verified:',z['input_rows'],'inputs,',len(history),'history rows,',sum(len(x['parts']) for x in manifest['inventories']),'chunks; no compiler/tracer; lock free.')
