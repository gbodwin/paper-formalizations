"""One authorized entry call; reviewed wrapper bytes remain unchanged.

This outer directory records the invocation, including planning failures. It is
not the wrapper's production claim, work root, lock or admission authority.
"""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time,traceback
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
WRAPPER=ROOT/'checkpoints/light-eft-supplied-forest-activation-20261018'
REVIEWED='f49febff6967af577496e79b18e58899253d2fce'
sys.path.insert(0,str(WRAPPER))
from contracts import save,require
from authority import facts
import driver

def processes():
 entries={}
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   fields=(p/'stat').read_text().rsplit(')',1)[1].split()
   entries[int(p.name)]=dict(pid=int(p.name),ppid=int(fields[1]),state=fields[0],start_ticks=int(fields[19]),comm=(p/'comm').read_text().strip())
  except (OSError,IndexError,ValueError):pass
 ancestors=set();cursor=os.getpid()
 while cursor in entries and cursor not in ancestors:ancestors.add(cursor);cursor=entries[cursor]['ppid']
 active=[r for r in entries.values() if r['comm'] in {'lean','leanchecker','lake','leantar','strace'} and r['state']!='Z']
 other=[r for r in entries.values() if r['comm'] in {'codex','python','python3','python3.12'} and r['pid'] not in ancestors and r['state']!='Z']
 return dict(processes=list(entries.values()),ancestors=sorted(ancestors),active_compilers=active,other_worker_candidates=other)

def fresh_coordination():
 require(state['coordination_callback_calls']==0,'No second coordination call or refresh')
 state['coordination_callback_calls']=1
 observation=processes()
 observation.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),observed_monotonic_ns=time.monotonic_ns(),
  common_lock_exists=driver.COMMON.exists(),common_lock_is_symlink=driver.COMMON.is_symlink(),
  qualification='Current visible namespace only; sole-worker and idle-reviewer authorization is the explicit user/source-thread instruction for this one attempt.')
 save(HERE/'post-planning-ownership.json',observation)
 require(not observation['active_compilers'] and not observation['other_worker_candidates'],'Another worker/compiler is active')
 require(not observation['common_lock_exists'] and not observation['common_lock_is_symlink'],'Existing common lock; do not adopt, replace or remove')
 document=dict(approved_wrapper_commit=REVIEWED,exclusive_worker=True,reviewer_idle=True,allow_new_epoch=True,same_directory='/tmp',
  coordination_reference='User/source-thread 01a144fe-14cb-74aa-b32b-6d4b9b1060c1 independently approves exactly one four-stage attempt through f49febff6967af577496e79b18e58899253d2fce, with sole worker and idle reviewer; no automatic retry.',
  facts=facts(),issued_ns=time.monotonic_ns())
 save(HERE/'coordination.json',document)
 state.update(status='post-planning-coordination-issued',coordination_issued_ns=document['issued_ns'])
 save(HERE/'controller-result.json',state)
 return document

require(subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()==REVIEWED,'Unexpected HEAD')
state=dict(reviewed_wrapper=REVIEWED,staged_source_commit='40029953e9e53525f0f1f431d6d56333b05183a3',
 frozen_import_source='78cb40c7837db049d645d73696f2e0b724ce8a3b',status='entry-call-pending',entry_calls=0,coordination_callback_calls=0,
 automatic_retry=False,invoker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controller_pid=os.getpid(),
 started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),started_ns=time.monotonic_ns())
with (HERE/'controller-result.json').open('x') as f:json.dump(state,f,indent=2);f.write('\n')
try:
 state.update(status='calling-reviewed-entry-once',entry_calls=1);save(HERE/'controller-result.json',state)
 result=driver.execute_production(REVIEWED,fresh_coordination)
 state.update(status='reviewed-entry-returned',entry_result=result)
except BaseException as exc:
 state.update(status='stopped-first-failure',failure=repr(exc));traceback.print_exc()
finally:
 state.update(ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),ended_ns=time.monotonic_ns())
 save(HERE/'controller-result.json',state)
print(json.dumps({'status':state['status'],'entry_calls':state['entry_calls'],'coordination_callback_calls':state['coordination_callback_calls'],
 'entry_accepted':state.get('entry_result',{}).get('accepted'),'failure':state.get('failure',state.get('entry_result',{}).get('failure'))}),flush=True)
raise SystemExit(0 if state.get('entry_result',{}).get('accepted') else 1)
