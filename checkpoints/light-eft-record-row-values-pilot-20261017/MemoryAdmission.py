"""Per-invocation observed memory admission, separate from supervisor disk gate.
This is a conservative headroom check, not a memory reservation or proof of peak usage.
The unchanged supervisor still owns locking, preflight, execution and reaping.
"""
from pathlib import Path
import json,time,datetime,uuid

def admit_memory(evidence,label):
 current=int(Path('/sys/fs/cgroup/memory.current').read_text())
 limit=int(Path('/sys/fs/cgroup/memory.max').read_text())
 available=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024
 required=4*1024**3
 admitted=limit-current>=required and available>=required
 row=dict(admission_id=uuid.uuid4().hex,label=label,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),monotonic_ns=time.monotonic_ns(),cgroup_current=current,cgroup_limit=limit,cgroup_headroom=limit-current,system_mem_available=available,required_available_bytes=required,admitted=admitted,qualification='Observed before invoking unchanged locked supervisor; no memory reservation claimed')
 with (evidence/'memory-admissions.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 if not admitted:raise RuntimeError('Insufficient observed memory headroom; no compiler admitted')
