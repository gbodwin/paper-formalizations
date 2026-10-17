"""Offline analysis of the bounded partial trace; no compiler/tracer execution."""
from pathlib import Path
import json,re,collections,os,hashlib
B=Path(__file__).resolve().parent;E=B/'evidence/compile';receipt=json.loads((E/'receipt.json').read_text());actual=receipt['actual_lean_pid'];trace=E/'syscalls.trace'
line_re=re.compile(r'^(\d+)\s+(\d+\.\d+)\s+(.*)$');pending={};counts=collections.Counter();errnos=collections.Counter();mapping_failures=[];targets=[];threads={actual};execs=[];read_calls=0;read_strings=0;trailing=False;normalized=0;incomplete=[]
intervals=[];current=peak=0;lean_started=False;brk_base=None;brk_end=None;mapping_rows=0
page=os.sysconf('SC_PAGESIZE')
def rounded(n):return (n+page-1)//page*page
def remove(lo,hi):
 global intervals,current
 out=[]
 for a,b in intervals:
  if b<=lo or a>=hi:out.append((a,b))
  else:
   if a<lo:out.append((a,lo))
   if b>hi:out.append((hi,b))
 intervals=out;current=sum(b-a for a,b in intervals)
def add(lo,hi):
 global intervals,current,peak
 remove(lo,hi);intervals.append((lo,hi));intervals.sort();current+=hi-lo;peak=max(peak,current)
def event(pid,stamp,body,start_line,end_line,out):
 global normalized,read_calls,read_strings,lean_started,intervals,current,peak,brk_base,brk_end,mapping_rows
 m=re.match(r'(\w+)\(',body)
 if not m:return
 name=m.group(1)
 if ' = ' not in body:
  incomplete.append({'pid':pid,'source_line':start_line,'body':body});return
 counts[name]+=1;normalized+=1
 error=re.search(r'= -1 ([A-Z][A-Z0-9]+)',body)
 if error:errnos[error.group(1)]+=1
 if name=='execve':
  execs.append({'pid':pid,'time':stamp,'line':start_line,'body':body})
  if pid==actual and '/workspace/toolchains/lean-4.34.0-linux/bin/lean"' in body and re.search(r'\)\s*= 0\b',body):lean_started=True;intervals=[];current=peak=0;brk_base=brk_end=None
 if name in ('clone','clone3') and 'CLONE_THREAD' in body:
  tid=re.search(r'= (\d+)\b',body)
  if tid:threads.add(int(tid.group(1)))
 if name in ('read','pread64','readv','preadv','preadv2'):
  read_calls+=1
  if re.search(r'^\w+\([^,]*,\s*"',body):read_strings+=1
 if 'HigherOrder.olean.private' in body or 'Term.olean.private' in body:targets.append({'pid':pid,'line':start_line,'body':body})
 if name in ('mmap','mremap','munmap','mprotect','brk'):
  row={'pid':pid,'time':stamp,'source_start_line':start_line,'source_end_line':end_line,'call':name,'after_lean_exec':lean_started,'body':body}
  if error:row['errno']=error.group(1);mapping_failures.append(row)
  if lean_started and pid in threads:
   if name=='mmap':
    match=re.match(r'mmap\([^,]+,\s*(\d+),.*\)\s*= (0x[0-9a-f]+)\b',body)
    if match:add(int(match.group(2),16),int(match.group(2),16)+rounded(int(match.group(1))))
   elif name=='munmap':
    match=re.match(r'munmap\((0x[0-9a-f]+),\s*(\d+)\)\s*= 0\b',body)
    if match:remove(int(match.group(1),16),int(match.group(1),16)+rounded(int(match.group(2))))
   elif name=='brk':
    match=re.search(r'\)\s*= (0x[0-9a-f]+)\b',body)
    if match:
     value=int(match.group(1),16)
     if brk_base is None:brk_base=value
     brk_end=value
  row['tracked_postexec_mmap_union_bytes']=current;out.write(json.dumps(row)+'\n');mapping_rows+=1
with (B/'mapping-records.jsonl').open('w') as out,trace.open() as source:
 for lineno,line in enumerate(source,1):
  trailing=not line.endswith('\n');match=line_re.match(line.rstrip('\n'))
  if not match:continue
  pid=int(match.group(1));stamp=match.group(2);body=match.group(3)
  if '<unfinished ...>' in body:pending[pid]=(stamp,body.split('<unfinished ...>',1)[0],lineno);continue
  resume=re.match(r'<\.\.\. (\w+) resumed>(.*)',body)
  if resume:
   prior=pending.pop(pid,None)
   if prior:event(pid,prior[0],prior[1]+resume.group(2),prior[2],lineno,out)
   continue
  event(pid,stamp,body,lineno,lineno,out)
# Ordinary /proc maps snapshots are retained separately; their sums are samples, not exact syscall accounting.
map_samples=[];mapsfile=E/'map-samples.jsonl'
if mapsfile.exists():
 for line in mapsfile.read_text().splitlines():
  row=json.loads(line);text=row.get('maps','');total=0;entries=0
  for item in text.splitlines():
   match=re.match(r'([0-9a-f]+)-([0-9a-f]+) ',item)
   if match:total+=int(match.group(2),16)-int(match.group(1),16);entries+=1
  map_samples.append({'monotonic_ns':row['monotonic_ns'],'pid':row['pid'],'summed_map_bytes':total,'entries':entries,'truncated':row.get('truncated'),'contains_lean_executable':'/workspace/toolchains/lean-4.34.0-linux/bin/lean' in text,'read_error':row.get('read_error')})
summary={'trace_bytes':trace.stat().st_size,'trace_sha256':hashlib.sha256(trace.read_bytes()).hexdigest(),'trace_bound_reached':trace.stat().st_size==receipt['trace_bound_bytes'],'trailing_line_truncated':trailing,'normalized_completed_calls':normalized,'incomplete_syscall_starts':incomplete,'syscall_counts':dict(counts),'errno_counts':dict(errnos),'pending_unfinished_calls':{str(k):{'line':v[2],'prefix':v[1]} for k,v in pending.items()},'actual_lean_pid':actual,'tracer_pid':receipt['tracer_pid'],'observed_thread_ids':sorted(threads),'exec_records':execs,'read_family_calls':read_calls,'read_buffers_rendered_as_strings':read_strings,'mapping_records':mapping_rows,'mapping_failure_records':mapping_failures,'named_prior_failure_file_records':targets,'tracked_postexec_mmap_union_peak_bytes':peak,'tracked_postexec_mmap_union_final_bytes':current,'final_brk_growth_bytes':max(0,brk_end-brk_base) if brk_end is not None else None,'mapping_budget_qualification':'Partial syscall-derived mmap union after Lean exec. Excludes exec-created initial mappings and brk from union; missing/truncated events prevent whole-lifetime/exact budget claims. Raw successful mapping records and ordinary /proc map samples are preserved.','maps_samples':map_samples,'compiler_completion':'Not established; tracer died SIGXFSZ at trace bound; adopted actual Lean reaped with SIGTERM','prior_read_failure_errno_captured':False}
with (B/'trace-analysis.json').open('w') as f:json.dump(summary,f,indent=2);f.write('\n')
print(json.dumps({k:summary[k] for k in ['trace_bytes','trace_bound_reached','trailing_line_truncated','syscall_counts','errno_counts','read_buffers_rendered_as_strings','mapping_records','tracked_postexec_mmap_union_peak_bytes','observed_thread_ids','prior_read_failure_errno_captured']},indent=2))
