"""Thin one-shot invocation of the independently approved, unchanged entry."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,sys,time,traceback
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
WRAPPER=ROOT/'checkpoints/light-eft-supplied-forest-wrapper-delta-20261018'
REVIEWED='2aa4e6f531b7968a1f3dd820aa856b73c628d161'
sys.path.insert(0,str(WRAPPER))
from contracts import save,require
from authority import facts
from pilot_accounting import VisibleAccounting
import driver
claim=HERE/'invocation-claimed.json'
with claim.open('x') as f:json.dump(dict(reviewed_wrapper=REVIEWED,started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),one_attempt_only=True),f)
state=dict(reviewed_wrapper=REVIEWED,staged_source_commit='40029953e9e53525f0f1f431d6d56333b05183a3',
 frozen_import_source='78cb40c7837db049d645d73696f2e0b724ce8a3b',status='fresh-preflight',automatic_retry=False,
 invoker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controller_pid=os.getpid())
save(HERE/'controller-result.json',state)
try:
 # Current visible process tree plus the user's explicit sole-worker/idle-reviewer coordination.
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
 lock=Path('/tmp/distance-sparsification-single-compiler.lock')
 capacity=VisibleAccounting().sample()
 pre=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),processes=list(entries.values()),
  ancestors=sorted(ancestors),active_compilers=active,other_worker_candidates=other,
  memory=capacity,free_disk_bytes=shutil.disk_usage(ROOT).free,lock_exists=lock.exists(),lock_is_symlink=lock.is_symlink(),
  qualification='Current visible namespace only; sole-worker and reviewer-idle coordination supplied explicitly by the user. Historical lock continuity is not assumed.')
 save(HERE/'preflight.json',pre)
 require(not active and not other,'Another worker/compiler is active')
 require(not lock.exists() and not lock.is_symlink(),'Unexpected existing common lock; do not adopt or replace')
 require(capacity['headroom']>=4*1024**3 and capacity['system_available']>=3*1024**3,'Fresh capacity below approved maximum stage admission')
 require(pre['free_disk_bytes']>2*1024**3,'Fresh disk not above2GiB')
 coord=dict(approved_wrapper_commit=REVIEWED,exclusive_worker=True,reviewer_idle=True,allow_new_epoch=True,same_directory='/tmp',
  coordination_reference='User/source-thread 01a144fe-14cb-74aa-b32b-6d4b9b1060c1 explicitly authorizes one fresh bounded four-stage attempt of 2aa4e6f531b7968a1f3dd820aa856b73c628d161, with sole worker and idle independent reviewer.',
  facts=facts(),issued_ns=time.monotonic_ns())
 save(HERE/'coordination.json',coord)
 state['status']='invoking-reviewed-entry-once';save(HERE/'controller-result.json',state)
 result=driver.execute_production(REVIEWED,coord)
 state.update(status='reviewed-entry-returned',entry_result=result)
except BaseException as exc:
 state.update(status='stopped-first-failure',failure=repr(exc));traceback.print_exc()
finally:
 state['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 save(HERE/'controller-result.json',state)
print(json.dumps({'status':state['status'],'entry_accepted':state.get('entry_result',{}).get('accepted'),'failure':state.get('failure',state.get('entry_result',{}).get('failure'))}),flush=True)
raise SystemExit(0 if state.get('entry_result',{}).get('accepted') else 1)
