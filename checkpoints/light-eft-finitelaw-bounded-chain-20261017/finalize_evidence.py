"""Offline evidence export only; never invokes Lean or a checker."""
from pathlib import Path
import json,hashlib,fcntl,subprocess,datetime
b=Path(__file__).resolve().parent;e=b/'evidence/compile';r=json.loads((e/'receipt.json').read_text());data=(e/'inputs-before.json').read_bytes();assert data==(e/'inputs-after.json').read_bytes()
chunks=b/'chunks';chunks.mkdir(exist_ok=True);manifest={'reconstruction':'Concatenate listed part bytes in order without separators. Input inventories are byte-identical.','inventories':[]}
for name in ['inputs-before.json','hash-advice-before.jsonl','hash-advice-after.jsonl']:
 raw=(e/name).read_bytes();folder=chunks/name.replace('.','-');folder.mkdir(exist_ok=True);parts=[];pending=bytearray()
 def flush():
  if not pending:return
  p=folder/f'part-{len(parts):03d}.txt';p.write_bytes(pending);parts.append({'path':str(p.relative_to(chunks)),'bytes':len(pending),'sha256':hashlib.sha256(pending).hexdigest()});pending.clear()
 for line in raw.splitlines(keepends=True):
  if len(pending)+len(line)>200000:flush()
  pending.extend(line)
 flush();assert b''.join((chunks/x['path']).read_bytes() for x in parts)==raw
 manifest['inventories'].append({'reconstructs':['../evidence/compile/'+name]+(['../evidence/compile/inputs-after.json'] if name=='inputs-before.json' else []),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'parts':parts})
(chunks/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
active=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if x.split()[-1] in ('lean','lake','leanchecker','leantar')];assert not active
with open('/tmp/distance-sparsification-single-compiler.lock') as f:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);assert Path(f.name).stat().st_ino==3849
z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attempts':[{'stage':'compile','attempt_id':r['attempt_id'],'exit':r['exit']}],'resolve_attempts':0,'replay_attempts':0,'output_objects':[],'input_rows':len(json.loads(data)),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(data).hexdigest(),'common_lock_free':True,'active_compilers':active,'direct_reaped':r['direct_reaped'],'all_descendants_gone':r['all_descendants_gone'],'kernel_no_children_verified':r['kernel_no_children_verified'],'preserved_inputs_verified':r['preserved_inputs_verified'],'no_retry':True}
(b/'result-reconciliation.json').write_text(json.dumps(z,indent=2)+'\n')
print('Verified',z['input_rows'],'input rows;',sum(len(x['parts']) for x in manifest['inventories']),'chunks; idle and lock free.')
