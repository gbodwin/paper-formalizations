"""Offline packaging only, after the finite chain has ended."""
from pathlib import Path
import json,hashlib,fcntl,subprocess,datetime,re
B=Path(__file__).resolve().parent
state=json.loads((B/'chain-result.json').read_text())
if state['status'].startswith('running') or state['status']=='preparing':raise RuntimeError('Packaging forbidden before chain completion')
manifest={'reconstruction':'Concatenate listed part bytes in order without separators; paired inventories are byte-identical.','inventories':[]}
chunks=B/'chunks';chunks.mkdir(exist_ok=False)
def split_file(path,reconstructs):
    folder=chunks/path.name.replace('.','-');folder.mkdir();parts=[];pending=bytearray();whole=hashlib.sha256();size=0
    def flush():
        if not pending:return
        target=folder/f'part-{len(parts):03d}.txt';target.write_bytes(pending);parts.append({'path':str(target.relative_to(chunks)),'bytes':len(pending),'sha256':hashlib.sha256(pending).hexdigest()});pending.clear()
    with path.open('rb') as f:
        for line in f:
            whole.update(line);size+=len(line)
            if len(pending)+len(line)>200000:flush()
            pending.extend(line)
    flush();check=hashlib.sha256()
    for row in parts:
        content=(chunks/row['path']).read_bytes();assert len(content)==row['bytes'] and hashlib.sha256(content).hexdigest()==row['sha256'];check.update(content)
    assert check.hexdigest()==whole.hexdigest()
    manifest['inventories'].append({'reconstructs':reconstructs,'bytes':size,'sha256':whole.hexdigest(),'parts':parts})
e=B/'evidence/compile';before=(e/'inputs-before.json').read_bytes();assert before==(e/'inputs-after.json').read_bytes()
for name in ['inputs-before.json','hash-advice-before.jsonl','hash-advice-after.jsonl']:
    split_file(e/name,['../evidence/compile/'+name]+(['../evidence/compile/inputs-after.json'] if name=='inputs-before.json' else []))
split_file(B/'history-advice.jsonl',['../history-advice.jsonl'])
with (chunks/'manifest.json').open('w') as f:json.dump(manifest,f,indent=2);f.write('\n')
r=json.loads((e/'receipt.json').read_text());history=[json.loads(x) for x in (B/'history-advice.jsonl').read_text().splitlines()];plan=json.loads((B/'history-whitelist.json').read_text())['files'];expected={row['path']:row for row in plan}
assert len(history)==1560 and len({x['path'] for x in history})==1560 and sum(x['bytes'] for x in history)==710100227
for row in history:
    assert row['verified_sha256']==expected[row['path']]['sha256'] and row['bytes']==expected[row['path']]['bytes'] and row['identity']==row['identity_after_advice']
for path,row in r['completed_file_housekeeping'].items():
    data=Path(path).read_bytes();assert row['state']=='completed' and hashlib.sha256(data).hexdigest()==row['sha256'] and len(data)==row['bytes'] and row['identity']==row['identity_after_advice']
raw=(e/'raw.log').read_text();allocator={'parsed_arena_reserve_kib':re.findall(r"option 'arena_reserve': ([0-9]+) KiB",raw),'reservation_lines':[x for x in raw.splitlines() if 'mimalloc: reserved ' in x],'error_lines':[x for x in raw.splitlines() if 'error:' in x],'explicit_errno_lines':[x for x in raw.splitlines() if re.search(r'errno|ENOMEM|EACCES|Permission denied|Cannot allocate memory',x,re.I)],'errno_captured':False,'qualification':'No further compiler execution or instrumentation; absent errno must not be inferred.'}
with (B/'allocator-observation.json').open('w') as f:json.dump(allocator,f,indent=2);f.write('\n')
active=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if x.split()[-1] in ('lean','lake','leanchecker','leantar')];assert not active
with open('/tmp/distance-sparsification-single-compiler.lock') as lock:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);assert Path(lock.name).stat().st_ino==3849
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attempt_id':r['attempt_id'],'compile_exit':r['exit'],'lean_children':1,'resolve_executions':0,'replay_executions':0,'fresh_objects':[],'history_passes':1,'history_count':len(history),'history_bytes':sum(x['bytes'] for x in history),'history_hashes_and_identities_verified':True,'completed_new_files':len(r['completed_file_housekeeping']),'completed_new_file_hashes_and_identities_verified':True,'input_rows':len(json.loads(before)),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(before).hexdigest(),'direct_reaped':r['direct_reaped'],'all_descendants_gone':r['all_descendants_gone'],'kernel_no_children_verified':r['kernel_no_children_verified'],'preserved_inputs_verified':r['preserved_inputs_verified'],'common_lock_free':True,'active_compilers':active,'no_retry':True,'packaging_after_chain_end':True}
with (B/'result-reconciliation.json').open('w') as f:json.dump(result,f,indent=2);f.write('\n')
print('Export complete:',len(history),'history rows;',result['input_rows'],'inputs;',sum(len(x['parts']) for x in manifest['inventories']),'chunks; lock free and compilers idle.')
