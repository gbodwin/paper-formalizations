"""Harmless in-process tests; no tracer/Lean execution."""
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
import json
import trace_supervisor as t
import pilot_runner as p
actual=234;tracer=SimpleNamespace(pid=123);lockfd=5
identity={'pid':actual,'ppid':tracer.pid,'sid':actual,'pgid':actual,'start_ticks':999,'state':'S','rss':0,'vm':0}
packet={'pid':actual,'ppid':tracer.pid,'sid':actual,'pgid':actual,'limits':{k:[v,v] for k,v in p.LIMITS.items()},'lock_fd':lockfd,'lock_inheritable':True,'lock_device':33,'lock_inode':3849}
stat=SimpleNamespace(st_dev=33,st_ino=3849)
def limit(pid,key):
 assert pid==actual
 name=next(name for name in p.LIMITS if getattr(t.resource,name)==key)
 return (p.LIMITS[name],p.LIMITS[name])
checks={}
with patch.object(p,'child_status',return_value=identity),patch.object(t.os,'fstat',return_value=stat),patch.object(t.os,'stat',return_value=stat),patch.object(t.resource,'prlimit',side_effect=limit),patch.object(Path,'read_text',return_value='TracerPid:\t123\n'):
 checks['actual_pid_limits_and_parent_verified']=t.verify_actual(packet,tracer,lockfd,identity)==identity
 wrong={**packet,'limits':{**packet['limits'],'RLIMIT_AS':[1610612736,1610612736]}}
 try:t.verify_actual(wrong,tracer,lockfd,identity)
 except RuntimeError:checks['reject_wrong_actual_limit']=True
 else:checks['reject_wrong_actual_limit']=False
 wrong={**packet,'ppid':999}
 try:t.verify_actual(wrong,tracer,lockfd,identity)
 except RuntimeError:checks['reject_wrong_parent']=True
 else:checks['reject_wrong_parent']=False
argv=t.tracer_argv(Path('/fixed/trace'),10,11,12,5)
checks['address_only_all_read_families']='raw=read,pread64,readv,preadv,preadv2' in argv and not any(x.startswith('read=') or x.startswith('write=') for x in argv)
checks['follow_threads_successful_mappings']='-f' in argv and all(name in t.SYSCALLS.split(',') for name in ['mmap','munmap','mprotect','brk','clone','clone3','openat','fstat','lseek','read','close'])
checks['exact_frozen_compiler_command']=p.stage_argv('compile')==[str(p.LEAN),'-j1','-s65536','-M512','-DautoImplicit=false','-DwarningAsError=true','--root='+str(p.MODULE_ROOT),'-o',str(p.OBJECT),str(p.PROJECT_SOURCE)]
checks['fixed_bounds']=t.TRACER_AS==268435456 and t.TRACE_BOUND==16777216 and t.MAP_BOUND==4194304 and p.DEADLINE==90 and p.LIMITS['RLIMIT_AS']==3221225472
try:p.stage_argv('aggregate')
except ValueError:checks['no_aggregate_command']=True
assert all(checks.values()),checks
with (Path(__file__).parent/'harmless-tests.json').open('w') as f:json.dump({'checks':checks,'scope':'Mocked identity/limit/lock checks and argv inspection; no new child execution'},f,indent=2);f.write('\n')
print(json.dumps(checks,indent=2))
