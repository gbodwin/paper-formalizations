"""Offline concise errno/map reconciliation and byte-preserving exports; no execution retry."""
from pathlib import Path
import json,hashlib,re,collections,subprocess,fcntl,datetime
B=Path(__file__).resolve().parent;E=B/'evidence/compile';r=json.loads((E/'receipt.json').read_text());state=json.loads((B/'chain-result.json').read_text());assert state['status']=='stopped-first-failure'
raw=(E/'syscalls.trace').read_text();lines=raw.splitlines();counts=collections.Counter();errors=collections.Counter();read_strings=0;exits=[];critical=[]
for number,line in enumerate(lines,1):
 match=re.match(r'(\d+)\s+(\d+\.\d+)\s+(\w+)\(',line)
 if match:counts[match.group(3)]+=1
 error=re.search(r'= -1 ([A-Z][A-Z0-9]+)',line)
 if error:errors[error.group(1)]+=1
 if re.search(r'\b(read|pread64|readv|preadv|preadv2)\([^,]*,\s*"',line):read_strings+=1
 if '+++ exited with ' in line:exits.append(line)
 if 'HigherOrder.olean.private' in line or 'EFAULT' in line:critical.append({'source_line':number,'raw':line})
# Preserve only a short local context around the final named-file mmap/read failure.
context=[]
if critical:
 lo=max(1,critical[-1]['source_line']-7);hi=min(len(lines),critical[-1]['source_line'])
 context=[{'source_line':i,'raw':lines[i-1]} for i in range(lo,hi+1)]
maps=[];path=E/'map-samples.jsonl'
if path.exists():
 for line in path.read_text().splitlines():
  row=json.loads(line);total=0;vmas=0;categories=collections.Counter();text=row.get('maps','')
  for item in text.splitlines():
   fields=item.split(None,5);match=re.match(r'([0-9a-f]+)-([0-9a-f]+)$',fields[0]) if fields else None
   if not match:continue
   size=int(match.group(2),16)-int(match.group(1),16);total+=size;vmas+=1
   label=fields[5] if len(fields)>5 else ''
   categories['file_backed' if label.startswith('/') else 'anonymous_or_special']+=size
  maps.append({'pid':row['pid'],'monotonic_ns':row['monotonic_ns'],'parsed_vmas':vmas,'parsed_map_bytes':total,'categories_partial_bytes':dict(categories),'truncated':row.get('truncated'),'contains_lean_executable':'/workspace/toolchains/lean-4.34.0-linux/bin/lean' in text,'read_error':row.get('read_error'),'qualification':'Non-atomic /proc read. Truncated snapshots are lower bounds; an exit-racing snapshot may omit the executable and cannot represent peak VM.'})
before=(E/'inputs-before.json').read_bytes();after=(E/'inputs-after.json').read_bytes();assert before==after
source=json.loads(before);filename='/workspace/paper-formalizations/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/HigherOrder.olean.private';target=next(x for x in source if x['path']==filename)
assert target['bytes']==576104 and target['sha256']=='1dd5e6457e93a4a7c870e8d34dd5f79e5d72cd6a478115b7dd1f972ea77053a9'
summary={'attempt_id':r['attempt_id'],'tracer_pid':r['tracer_pid'],'actual_lean_pid':r['actual_lean_pid'],'trace_bytes':(E/'syscalls.trace').stat().st_size,'trace_sha256':hashlib.sha256((E/'syscalls.trace').read_bytes()).hexdigest(),'trace_has_final_newline':raw.endswith('\n'),'trace_bound_reached':(E/'syscalls.trace').stat().st_size>=r['trace_bound_bytes'],'status_filter':'failed','syscall_counts':dict(counts),'errno_counts':dict(errors),'read_buffer_strings':read_strings,'critical_records':critical,'final_failure_context':context,'exit_records':exits,'actual_lean_exit_one_recorded':any(re.match(str(r['actual_lean_pid'])+r'\s+.*\+\+\+ exited with 1 \+\+\+',x) for x in exits),'actual_filename_inventory':target,'read_fd_decimal':10,'read_buffer_address':0,'read_count_bytes':int('8ca68',16),'read_errno':'EFAULT','preceding_named_file_mmap_errno':'ENOMEM','sampled_peaks_bytes':r['sampled_peaks_bytes'],'maps_threshold_bytes':r['maps_threshold_bytes'],'near_cap_actual_lean_executable':r.get('near_cap_actual_lean_executable'),'maps_snapshots':maps,'interpretation':'The named fd-10 private-file mmap fails ENOMEM, allocation fallbacks fail ENOMEM, then the same worker reads fd 0xa into address zero for exactly 576104 bytes and gets EFAULT. This directly establishes allocation/read errno in this constrained run. It supports an allocation-failure/null-buffer fallback mechanism; it does not establish all causes of prior failures or unconstrained behavior.','coverage_limits':'Only failed selected syscalls are logged. Successful open/stat/header reads and mappings are excluded; positive short reads and brk returning the old break may be absent. No full syscall-derived virtual-budget reconstruction is possible. Map snapshots are non-atomic and partially truncated.'}
with (B/'diagnostic-summary.json').open('w') as f:json.dump(summary,f,indent=2);f.write('\n')
history=[json.loads(x) for x in (B/'history-advice.jsonl').read_text().splitlines()];expected={x['path']:x for x in json.loads((B/'history-whitelist.json').read_text())['files']};assert len(history)==504 and len({x['path'] for x in history})==504 and sum(x['bytes'] for x in history)==222716878
for row in history:assert row['verified_sha256']==expected[row['path']]['sha256'] and row['identity']==row['identity_after_advice']
for filename,row in r['completed_file_housekeeping'].items():
 data=Path(filename).read_bytes();assert row['state']=='completed' and len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'] and row['identity']==row['identity_after_advice']
# Retain familiar reconstruction exports for raw verification files, not decoded trace collections.
chunks=B/'chunks';chunks.mkdir(exist_ok=False);manifest={'reconstruction':'Concatenate listed part bytes in order, without added separators. Maps are split as raw byte blocks; other logs are row-aligned.','inventories':[]}
items=[(E/'inputs-before.json',['../evidence/compile/inputs-before.json','../evidence/compile/inputs-after.json']),(E/'hash-advice-before.jsonl',['../evidence/compile/hash-advice-before.jsonl']),(E/'hash-advice-after.jsonl',['../evidence/compile/hash-advice-after.jsonl']),(B/'history-advice.jsonl',['../history-advice.jsonl'])]
if path.exists():items.append((path,['../evidence/compile/map-samples.jsonl']))
for file,targets in items:
 folder=chunks/file.name.replace('.','-');folder.mkdir();parts=[];whole=hashlib.sha256();size=0;pending=bytearray()
 def flush():
  if not pending:return
  out=folder/f'part-{len(parts):03d}.txt';out.write_bytes(pending);parts.append({'path':str(out.relative_to(chunks)),'bytes':len(pending),'sha256':hashlib.sha256(pending).hexdigest()});pending.clear()
 with file.open('rb') as f:
  if file.name=='map-samples.jsonl':
   while True:
    block=f.read(200000)
    if not block:break
    whole.update(block);size+=len(block);pending.extend(block);flush()
  else:
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
z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'MMAP_ENOMEM_THEN_NULL_BUFFER_READ_EFAULT','attempt_id':r['attempt_id'],'tracer_exit':r['exit'],'actual_lean_exit_one_recorded':summary['actual_lean_exit_one_recorded'],'trace_bound_reached':False,'original_named_file_errno_sequence_captured':True,'history_files':504,'history_bytes':222716878,'history_hashes_and_identities_verified':True,'input_rows':len(source),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(before).hexdigest(),'completed_new_files':len(r['completed_file_housekeeping']),'completed_new_file_hashes_and_identities_verified':True,'tracer_direct_reaped':r['tracer_direct_reaped'],'all_descendants_gone':r['all_descendants_gone'],'kernel_no_children_verified':r['kernel_no_children_verified'],'preserved_inputs_verified':r['preserved_inputs_verified'],'fresh_objects':r['output_inventory_after'],'resolver_executions':0,'checker_executions':0,'common_lock_free':True,'active_compilers_tracers':active,'one_diagnostic_only':True,'no_retry_or_post_attempt_configuration_change':True,'no_duplicate_decoded_mapping_collection':True,'packaging_after_end':True}
with (B/'result-reconciliation.json').open('w') as f:json.dump(z,f,indent=2);f.write('\n')
print('Reconciled:',dict(errors),'; raw trace',summary['trace_bytes'],'bytes;',len(source),'inputs;',sum(len(x['parts']) for x in manifest['inventories']),'chunks; no active compiler/tracer; lock free.')
