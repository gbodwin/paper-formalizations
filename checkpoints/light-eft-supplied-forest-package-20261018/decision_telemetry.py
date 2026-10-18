"""Capture both complete and partial decision inputs before policy evaluation."""
from pathlib import Path
import os,time,datetime

def capture_child(pid,stat_text=None,status_text=None):
 row={'pid':pid,'rss':None,'vm':None,'collection_errors':[],'tid_read_started_ns':time.monotonic_ns()}
 if stat_text is None:
  try:stat_text=Path(f'/proc/{pid}/stat').read_text()
  except Exception as exc:row['collection_errors'].append({'operation':'child stat','error':repr(exc)})
 if status_text is None:
  try:status_text=Path(f'/proc/{pid}/status').read_text()
  except Exception as exc:row['collection_errors'].append({'operation':'child status','error':repr(exc)})
 try:
  fields=stat_text.rsplit(')',1)[1].split();row.update(stat_pid=int(stat_text.split(' ',1)[0]),ppid=int(fields[1]),pgid=int(fields[2]),sid=int(fields[3]),start_ticks=int(fields[19]),state=fields[0],stat_flags=int(fields[6]),stat_threads=int(fields[17]),stat_vsize_bytes=int(fields[20]),stat_rss_pages=int(fields[21]))
 except Exception as exc:row['collection_errors'].append({'operation':'parse child identity','error':repr(exc)})
 try:
  values={x.split(':',1)[0]:x.split(':',1)[1] for x in status_text.splitlines() if ':' in x}
  row['state']=values.get('State',row.get('state','?')).strip().split()[0]
  row.update(tgid=int(values['Tgid'].split()[0]),status_pid=int(values['Pid'].split()[0]))
  row['status_threads']=int(values['Threads'].split()[0])
  for field,key in [('VmRSS','rss'),('VmSize','vm')]:
   if field in values:row[key]=int(values[field].split()[0])*1024
   else:row['collection_errors'].append({'operation':field,'error':'Missing required live value'});row[key]=None
 except Exception as exc:row['collection_errors'].append({'operation':'parse child memory','error':repr(exc)})
 row.update(raw_stat=stat_text,raw_status=status_text,tid_read_finished_ns=time.monotonic_ns())
 if row['collection_errors']:row.update(partial_stat=stat_text,partial_status=status_text)
 return row

def collect(child,accounting):
 sample={'sample_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sample_started_ns':time.monotonic_ns(),'child':{},'accounting':{},'collection_errors':[]}
 try:sample['accounting']=accounting.sample()
 except Exception as exc:
  sample['accounting']=getattr(exc,'partial',getattr(accounting,'last_partial',None));sample['collection_errors'].append({'operation':'accounting','error':repr(exc)})
 try:
  sample['child']=capture_child(child.pid)
  sample['collection_errors']+=sample['child']['collection_errors']
 except Exception as exc:sample['collection_errors'].append({'operation':'child collection','error':repr(exc)})
 account=sample.get('accounting') or {}
 sample['collection_errors']+=account.get('collection_errors',[])
 for key in ['headroom','system_available','nodes','identities','namespace','membership']:
  if key not in account:sample['collection_errors'].append({'operation':'required accounting field','error':key})
 for node in account.get('nodes',[]):
  for key in ['path','limit','current','memory_stat','memory_events','oom','pids_current','pids_max','pids_events']:
   if key not in node:sample['collection_errors'].append({'operation':'required cgroup field','path':node.get('path'),'error':key})
  for key in ['anon','file','kernel']:
   if key not in node.get('memory_stat',{}):sample['collection_errors'].append({'operation':'required memory.stat','path':node.get('path'),'error':key})
 sample['sample_finished_ns']=time.monotonic_ns();return sample

def policy_errors(sample,baseline,anon_baseline,minimum_headroom,rss_stop,anon_stop,check_memory,minimum_host_headroom=None):
 superseded={item['index']:item['error'] for item in sample.get('exit_lifecycle',{}).get('superseded_original_leader_memory_errors',[])}
 errors=[repr(x) for index,x in enumerate(sample['collection_errors']) if not
  (superseded.get(index)==x and x.get('operation') in ('VmRSS','VmSize') and x.get('error')=='Missing required live value')]
 if errors:return errors
 now=sample['accounting'];current=sample.get('observed_process_memory',sample.get('process_memory',sample['child']))
 try:
  check_memory(now,baseline,minimum_headroom)
  if now['system_available']<(minimum_headroom if minimum_host_headroom is None else minimum_host_headroom):errors.append('Host MemAvailable below required floor')
  if isinstance(current.get('rss'),int) and current['rss']>=rss_stop:errors.append('Observed live RSS reached 6 GiB stop')
  if anon_baseline is not None:
   actual={node['path'] for node in now['nodes']}
   if actual!=set(anon_baseline):errors.append('Anonymous baseline cgroup identities differ')
   else:
    for node in now['nodes']:
     growth=node['memory_stat']['anon']-anon_baseline[node['path']]
     if growth>=anon_stop:errors.append('Anonymous growth reached 3 GiB in '+node['path']+'; growth='+str(growth))
 except Exception as exc:errors.append(repr(exc))
 return errors
