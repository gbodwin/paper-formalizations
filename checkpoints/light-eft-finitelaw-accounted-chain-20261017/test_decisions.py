"""Harmless boundary/decision-retention fixtures; no Lean/checker/tracer."""
from pathlib import Path
from unittest.mock import patch
from types import SimpleNamespace
import copy,fcntl,json,os,signal,subprocess,sys,uuid,datetime
import pilot_runner as p
import decision_telemetry as t
from pilot_accounting import AccountingSampleError
B=Path(__file__).resolve().parent
paths=['/fixture/parent','/fixture/child']
def accounting():
 return {'namespace':'fixture','membership':'0::/\n','identities':[], 'headroom':8*1024**3,'system_available':8*1024**3,'nodes':[{'path':path,'limit':str(16*1024**3),'current':1,'memory_stat':{'anon':100,'file':200,'kernel':50},'memory_events':{'oom':0,'oom_kill':0,'oom_group_kill':0},'oom':{'oom':0,'oom_kill':0,'oom_group_kill':0},'pids_current':1,'pids_max':'max','pids_events':{'max':0}} for path in paths]}
baseline=accounting();anon={path:100 for path in paths}
def decision(now=None,rss=1):return {'sample_utc':'fixture','sample_started_ns':1,'sample_finished_ns':2,'accounting':now or accounting(),'child':{'pid':1,'ppid':1,'sid':1,'pgid':1,'start_ticks':1,'state':'S','rss':rss,'vm':1,'collection_errors':[]},'collection_errors':[]}
def errors(d,a=anon):return t.policy_errors(d,baseline,a,p.STOP_HEADROOM,p.RSS_STOP,p.ANON_GROWTH_STOP,p.check_memory)
checks={}
checks['rss_below_boundary_passes']=not errors(decision(rss=p.RSS_STOP-1))
checks['rss_boundary_stops']=bool(errors(decision(rss=p.RSS_STOP)))
for key in ['headroom','system_available']:
 n=accounting();n[key]=p.STOP_HEADROOM;checks[key+'_at_floor_passes']=not errors(decision(n))
 n[key]=p.STOP_HEADROOM-1;checks[key+'_below_floor_stops']=bool(errors(decision(n)))
n=accounting()
for row in n['nodes']:row['memory_stat']['anon']+=2*1024**3
checks['two_groups_not_summed']=not errors(decision(n))
for i,path in enumerate(paths):
 n=accounting();n['nodes'][i]['memory_stat']['anon']+=p.ANON_GROWTH_STOP
 checks['anon_boundary_'+str(i)+'_stops']=any(path in x for x in errors(decision(n)))
 n['nodes'][i]['memory_stat']['anon']-=1;checks['anon_below_'+str(i)+'_passes']=not errors(decision(n))
new=accounting()
for node in new['nodes']:node['memory_stat']['anon']+=4*1024**3
fresh={node['path']:node['memory_stat']['anon'] for node in new['nodes']};checks['fresh_stage_baselines_reset_growth']=not errors(decision(new),fresh)
checks['new_constants']=p.LIMITS['RLIMIT_AS']==12884901888 and p.RSS_STOP==6442450944 and p.ANON_GROWTH_STOP==3221225472 and p.INTERVAL==.1 and all('-M5120' in p.stage_argv(x) for x in ['compile','resolve'])
assert all(checks.values()),checks
root=B/'harmless-fixtures';root.mkdir(exist_ok=False);receipts=[]
with p.LOCK.open('r+') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(lock.fileno());assert(st.st_dev,st.st_ino)==(33,3849)
 for case in ['visible','host','rss','anon-parent','anon-child','missing-rss','collection-error']:
  folder=root/uuid.uuid4().hex;folder.mkdir();events=[];record={'fixture_only':True,'compiler_or_checker':False,'case':case,'lock_device':st.st_dev,'lock_inode':st.st_ino};child=None;real_kill=os.killpg
  def save():
   events.append('persist')
   with (folder/'receipt.json').open('w') as f:json.dump({**record,'events':events},f,indent=2);f.write('\n')
  try:
   child=subprocess.Popen([sys.executable,'-I','-c','import time;time.sleep(60)'],env={'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},pass_fds=(lock.fileno(),),start_new_session=True)
   record['child_pid']=child.pid;current=t.capture_child(child.pid);n=accounting()
   if case=='visible':n['headroom']=p.STOP_HEADROOM-1
   if case=='host':n['system_available']=p.STOP_HEADROOM-1
   if case=='rss':current['rss']=p.RSS_STOP
   if case.startswith('anon-'):n['nodes'][0 if case=='anon-parent' else 1]['memory_stat']['anon']+=p.ANON_GROWTH_STOP
   if case=='missing-rss':current['rss']=None;current['collection_errors']=[{'operation':'VmRSS','error':'Fixture missing live RSS'}]
   class Accounting:
    def sample(self):
     events.append('accounting-collected')
     if case=='collection-error':raise AccountingSampleError('fixture read error',{'nodes':[{'path':paths[0],'partial_raw':{'memory.stat':'fixture partial'}}],'collection_errors':[{'operation':'fixture','error':'fixture read error'}]})
     return copy.deepcopy(n)
   def capture(pid):events.append('child-collected');return copy.deepcopy(current)
   def kill(group,sig):
    assert group==child.pid and sig==signal.SIGKILL
    events.append('SIGKILL');return real_kill(group,sig)
   with (folder/'samples.jsonl').open('x') as samples,patch.object(t,'capture_child',side_effect=capture),patch.object(p.os,'killpg',side_effect=kill):
    try:p.runtime_sample(child,baseline,anon,Accounting(),record,save,samples)
    except p.MemoryGuardError:pass
    else:raise AssertionError('Expected stop')
   assert child.wait(timeout=2)==-9;record['child_reaped']=True
   d=record['stop_decision_sample'];saved=json.loads((folder/'receipt.json').read_text());logged=json.loads((folder/'samples.jsonl').read_text())
   assert d==saved['stop_decision_sample']==logged
   assert events.index('accounting-collected')<events.index('SIGKILL') and events.index('child-collected')<events.index('SIGKILL')<events.index('persist')
   if case=='collection-error':assert d['accounting']['nodes'][0]['partial_raw'] and d['child']['pid']==child.pid
   if case=='missing-rss':assert d['child']['rss'] is None and d['collection_errors']
   record['exact_sample_retained']=True;record['collection_before_kill_before_persist']=True
  finally:
   if child is not None and child.poll() is None:real_kill(child.pid,signal.SIGKILL);child.wait(timeout=2)
   save();receipts.append({'case':case,'receipt':str((folder/'receipt.json').relative_to(B)),'exact_sample_retained':record.get('exact_sample_retained')})
 try:os.waitpid(-1,os.WNOHANG)
 except ChildProcessError:checks['kernel_no_children']=True
 else:raise AssertionError('Fixture child remains')
with (B/'harmless-tests.json').open('w') as f:json.dump({'checks':checks,'fixtures':receipts,'scope':'Synthetic telemetry with seven sequential owned sleeping Python groups; no Lean/checker/tracer; exact full/partial samples preserved'},f,indent=2);f.write('\n')
print('Boundary checks and seven exact-sample SIGKILL fixtures passed; complete/partial collection preceded kill, kill preceded persistence, all reaped.')
