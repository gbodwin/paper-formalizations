"""Offline preservation of the single RSS-stopped chain; no execution retry."""
from pathlib import Path
import json,hashlib,subprocess,fcntl,datetime
B=Path(__file__).resolve().parent;E=B/'evidence/compile';r=json.loads((E/'receipt.json').read_text());chain=json.loads((B/'chain-result.json').read_text());assert chain['status']=='stopped-first-failure'
before=(E/'inputs-before.json').read_bytes();assert before==(E/'inputs-after.json').read_bytes();samples=[json.loads(x) for x in (E/'samples.jsonl').read_text().splitlines()]
high=r['wait4_maxrss_kib']*1024
summary={'attempt_id':r['attempt_id'],'child_pid':r['child_pid'],'result':'EXTERNAL_OBSERVED_RSS_STOP_SIGKILL','exit':r['exit'],'memory_stop_reason':r['memory_stop_reason'],'signal_sent':r['memory_stop_signal_sent'],'signal':'SIGKILL','signal_started_ns':r['memory_stop_signal_started_ns'],'signal_finished_ns':r['memory_stop_signal_finished_ns'],'signal_call_interval_ns':r['memory_stop_signal_finished_ns']-r['memory_stop_signal_started_ns'],'kill_before_persistence':True,'policy':r['memory_policy'],'actual_kernel_limits':r['handshake']['limits'],'wait4_maxrss_kib':r['wait4_maxrss_kib'],'wait4_maxrss_bytes':high,'kernel_high_water_above_rss_threshold_bytes':high-r['memory_policy']['rss_observed_stop_bytes'],'last_accepted_sample':samples[-1] if samples else None,'logged_sample_count':len(samples),'last_accepted_sample_to_kill_started_ns':r['memory_stop_signal_started_ns']-samples[-1]['monotonic_ns'] if samples else None,'reported_logged_sampled_rss_peak_bytes':r.get('sampled_rss_peak_bytes'),'reported_logged_sampled_vm_peak_bytes':r.get('sampled_vm_peak_bytes'),'breach_sample_exact_rss_preserved':False,'breach_sample_exact_vm_preserved':False,'measurement_qualification':'runtime_sample checks RSS before returning a sample to the logger. The breaching sample triggered immediate SIGKILL and was not appended. Logged sampled peaks are prior accepted samples, not the trigger or lifetime maxima. wait4 supplies the actual lifetime RSS high-water (including launcher). 250 ms monitoring can overshoot; it is not a kernel hard RSS cap. -M1536 is an intermittent runtime RSS check, not a kernel heap cap.','fresh_objects':r['output_inventory_after'],'successful_compile':False,'resolver_executions':0,'checker_executions':0,'no_retry_or_configuration_change':True}
with (B/'resource-stop-summary.json').open('w') as f:json.dump(summary,f,indent=2);f.write('\n')
history=[json.loads(x) for x in (B/'history-advice.jsonl').read_text().splitlines()];plan={x['path']:x for x in json.loads((B/'history-whitelist.json').read_text())['files']};assert len(history)==407 and len({x['path'] for x in history})==407 and sum(x['bytes'] for x in history)==183081165
for row in history:assert row['verified_sha256']==plan[row['path']]['sha256'] and row['identity']==row['identity_after_advice']
for filename,row in r['completed_file_housekeeping'].items():
 data=Path(filename).read_bytes();assert row['state']=='completed' and len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'] and row['identity']==row['identity_after_advice']
chunks=B/'chunks';chunks.mkdir(exist_ok=False);manifest={'reconstruction':'Concatenate listed part bytes in order without separators. Input inventories before/after are identical.','inventories':[]}
for path,targets in [(E/'inputs-before.json',['../evidence/compile/inputs-before.json','../evidence/compile/inputs-after.json']),(E/'hash-advice-before.jsonl',['../evidence/compile/hash-advice-before.jsonl']),(E/'hash-advice-after.jsonl',['../evidence/compile/hash-advice-after.jsonl']),(B/'history-advice.jsonl',['../history-advice.jsonl'])]:
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
repair=json.loads((B/'trace-publication-repair.json').read_text());assert repair['remote_content_verified'] and repair['remote_content_bytes']==96504 and repair['remote_content_sha256']=='bdfea71a593885b885c87857c38db7f8bb5cdb364caf83df7aefa5c67cfbb37b'
active=[x for x in subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines() if x.split()[-1] in ('lean','lake','leanchecker','leantar','strace')];assert not active
with open('/tmp/distance-sparsification-single-compiler.lock') as f:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);assert Path(f.name).stat().st_ino==3849
z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'attempt_id':r['attempt_id'],'result':'COMPILE_STOPPED_BY_EXTERNAL_RSS_GUARD','source_commit':r['source_commit'],'compile_invocations':1,'compile_exit':r['exit'],'resolve_invocations':0,'replay_invocations':0,'kernel_as_readback_bytes':r['handshake']['limits']['RLIMIT_AS'],'memory_kill_sent':r['memory_stop_signal_sent'],'wait4_maxrss_kib':r['wait4_maxrss_kib'],'fresh_objects':r['output_inventory_after'],'input_rows':len(json.loads(before)),'inventories_byte_identical':True,'inventory_sha256':hashlib.sha256(before).hexdigest(),'history_files':len(history),'history_bytes':183081165,'history_hashes_identities_verified':True,'completed_new_files':len(r['completed_file_housekeeping']),'completed_new_file_hashes_identities_verified':True,'direct_reaped':r['direct_reaped'],'all_descendants_gone':r['all_descendants_gone'],'kernel_no_children_verified':r['kernel_no_children_verified'],'preserved_inputs_verified':r['preserved_inputs_verified'],'raw_trace_repair_remote_verified_before_chain':True,'common_lock_free':True,'active_compilers_tracers':active,'no_retry_or_post_attempt_configuration_change':True,'packaging_after_end':True}
with (B/'result-reconciliation.json').open('w') as f:json.dump(z,f,indent=2);f.write('\n')
print('Preserved',z['input_rows'],'inputs;',len(history),'history files;',sum(len(x['parts']) for x in manifest['inventories']),'chunks; RSS high-water',high,'bytes; clean stop, lock free.')
