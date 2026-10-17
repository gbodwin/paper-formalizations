"""Synthetic memory thresholds plus real owned-group SIGKILL fixtures; no Lean/checker."""
from pathlib import Path
from unittest.mock import patch
import copy,datetime,fcntl,hashlib,json,os,signal,subprocess,sys,time,uuid
import pilot_runner as p
BASE=Path(__file__).resolve().parent
baseline={'headroom':4*1024**3,'system_available':4*1024**3,'nodes':[{'path':'fixture','limit':str(16*1024**3),'current':0,'oom':{'oom':0,'oom_kill':0,'oom_group_kill':0},'pids_max':'max','pids_current':1,'pids_events':{'max':0}}]}
checks={}
for value,allowed in [(p.STOP_HEADROOM-1,False),(p.STOP_HEADROOM,True)]:
 now=copy.deepcopy(baseline);now['headroom']=value
 try:p.check_memory(now,baseline,p.STOP_HEADROOM);got=True
 except p.MemoryGuardError:got=False
 checks['visible_floor_'+str(value)]=got==allowed
for value,allowed in [(p.STOP_HEADROOM-1,False),(p.STOP_HEADROOM,True)]:
 now=copy.deepcopy(baseline);now['system_available']=value
 try:p.enforce_host_stop(now);got=True
 except p.MemoryGuardError:got=False
 checks['host_floor_'+str(value)]=got==allowed
for value,allowed in [(p.RSS_STOP-1,True),(p.RSS_STOP,False)]:
 try:p.enforce_rss_stop({'state':'S','rss':value});got=True
 except p.MemoryGuardError:got=False
 checks['rss_stop_'+str(value)]=got==allowed
fields=['S','1','2','3']+['0']*16;stat_text='123 (fixture) '+' '.join(fields)
try:p.parse_child_status(123,stat_text,'State:\tS (sleeping)\nVmSize:\t1 kB\n')
except p.MemoryGuardError:checks['missing_live_rss_rejected']=True
else:checks['missing_live_rss_rejected']=False
checks['zombie_missing_rss_allowed']=p.parse_child_status(123,stat_text,'State:\tZ (zombie)\n')['state']=='Z'
checks['actual_limits_and_admission']=p.LIMITS['RLIMIT_AS']==12884901888 and p.ADMISSION_HEADROOM==3758096384 and p.STOP_HEADROOM==1073741824 and p.RSS_STOP==2147483648
checks['compiler_resolver_M1536']=all('-M1536' in p.stage_argv(stage) for stage in ['compile','resolve'])
checks['checker_has_supported_env_only']=p.stage_argv('replay')==[str(p.CHECKER),'-v',p.MODULE] and p.environment('replay')['LEAN_NUM_THREADS']=='1' and p.environment('replay')['LEAN_STACK_SIZE_KB']=='65536'
assert all(checks.values()),checks
fixtures=[];root=BASE/'harmless-memory-fixtures';root.mkdir(exist_ok=False)
with p.LOCK.open('r+') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(lock.fileno());assert(st.st_dev,st.st_ino)==(33,3849)
 for case in ['visible','host','rss','missing-live-rss']:
  folder=root/uuid.uuid4().hex;folder.mkdir();record={'case':case,'fixture_only':True,'compiler_or_checker':False,'synthetic_memory_values':True,'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lock_device':st.st_dev,'lock_inode':st.st_ino};events=[];child=None;real_kill=os.killpg
  def save():
   events.append('persist')
   with (folder/'receipt.json').open('w') as f:json.dump({**record,'events':events},f,indent=2);f.write('\n')
  try:
   child=subprocess.Popen([sys.executable,'-I','-c','import time;time.sleep(60)'],env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},pass_fds=(lock.fileno(),),start_new_session=True)
   record['child_pid']=child.pid;assert os.getpgid(child.pid)==child.pid
   now=copy.deepcopy(baseline)
   if case=='visible':now['headroom']=p.STOP_HEADROOM-1
   if case=='host':now['system_available']=p.STOP_HEADROOM-1
   current={'state':'S','rss':p.RSS_STOP if case=='rss' else 1,'vm':1}
   class Accounting:
    def sample(self):return now
   def kill(group,sig):
    assert group==child.pid and sig==signal.SIGKILL
    events.append('SIGKILL');return real_kill(group,sig)
   effect=p.MemoryGuardError('Synthetic missing live RSS') if case=='missing-live-rss' else None
   with patch.object(p.os,'killpg',side_effect=kill),patch.object(p,'child_status',side_effect=effect,return_value=current):
    try:p.runtime_sample(child,baseline,Accounting(),record,save)
    except Exception as exc:record['observed_guard_exception']=repr(exc)
    else:raise AssertionError('Expected immediate memory guard failure')
   record['exit']=child.wait(timeout=2);assert record['exit']==-signal.SIGKILL
   assert events[0]=='SIGKILL' and 'persist' in events and events.count('SIGKILL')==1
   record['signal_before_persistence']=True;record['child_reaped']=True
  finally:
   if child is not None and child.poll() is None:real_kill(child.pid,signal.SIGKILL);child.wait(timeout=2)
   record['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();fixtures.append({'case':case,'receipt':str((folder/'receipt.json').relative_to(BASE)),'exit':record.get('exit'),'signal_before_persistence':record.get('signal_before_persistence')})
 try:os.waitpid(-1,os.WNOHANG)
 except ChildProcessError:checks['fixtures_kernel_no_children']=True
 else:raise AssertionError('Unexpected child remains')
with (BASE/'harmless-tests.json').open('w') as f:json.dump({'checks':checks,'fixtures':fixtures,'scope':'Synthetic memory data; four harmless sleeping Python child groups killed and reaped sequentially under common lock. No Lean/checker/tracer executed.'},f,indent=2);f.write('\n')
print('Memory checks passed;',len(fixtures),'owned-group SIGKILL fixtures verified; signal preceded persistence; all reaped.')
