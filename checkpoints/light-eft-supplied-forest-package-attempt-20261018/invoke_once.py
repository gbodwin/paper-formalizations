"""One authorized package-stage entry call bound to implementation 2d75404b.

The publication HEAD may be newer evidence. It never replaces REVIEWED in the
entry/plan/receipts. This outer journal is not a production claim or lease.
"""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,time,traceback
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
WRAPPER=ROOT/'checkpoints/light-eft-supplied-forest-package-20261018'
REVIEWED='2d75404bfd140d0e8ecb13d3c2554b853b9a1640'
sys.path.insert(0,str(WRAPPER))
from contracts import save,require
from authority import facts,known_released_lock
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
 return dict(processes=list(entries.values()),ancestors=sorted(ancestors),
  active_compilers=[r for r in entries.values() if r['comm'] in {'lean','leanchecker','lake','leantar','strace'} and r['state']!='Z'],
  other_worker_candidates=[r for r in entries.values() if r['comm'] in {'codex','python','python3','python3.12'} and r['pid'] not in ancestors and r['state']!='Z'])

def fresh_coordination():
 require(state['coordination_callback_calls']==0,'No second coordination call or refresh')
 state['coordination_callback_calls']=1
 observed=processes();known=known_released_lock();expected=known['identity'];lock=Path(expected['path'])
 s=lock.lstat();d=lock.parent.lstat()
 actual=dict(path=str(lock),device=s.st_dev,inode=s.st_ino,directory_identity=[d.st_dev,d.st_ino])
 observed.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),observed_monotonic_ns=time.monotonic_ns(),released_lock_identity=actual,
  released_lock_mode=stat.S_IMODE(s.st_mode),released_lock_uid=s.st_uid,released_lock_nlink=s.st_nlink,
  qualification='Visible namespace only. Explicit user coordination authorizes one retry, sole worker, idle reviewer and only exact released-inode reuse. No free-lock adoption is inferred; reviewed lease acquires nonblocking.')
 save(HERE/'post-planning-ownership.json',observed)
 require(not observed['active_compilers'] and not observed['other_worker_candidates'],'Another worker/compiler is active')
 require(actual==expected and stat.S_ISREG(s.st_mode) and s.st_nlink==1 and stat.S_IMODE(s.st_mode)==known['required_mode'] and s.st_uid==known['required_uid']==os.getuid(),'Exact released lock differs; do not create, replace or adopt')
 document=dict(approved_wrapper_commit=REVIEWED,exclusive_worker=True,reviewer_idle=True,allow_new_epoch=True,same_directory='/tmp',
  allow_released_lock_reuse=True,released_lock_identity=expected,
  coordination_reference='User/source-thread 01a144fe-14cb-74aa-b32b-6d4b9b1060c1 independently approves exactly one bounded four-stage retry through implementation 2d75404bfd140d0e8ecb13d3c2554b853b9a1640, explicitly reusing only released lock device33/inode3258, with sole worker and idle reviewer; no automatic retry.',
  facts=facts(),issued_ns=time.monotonic_ns())
 save(HERE/'coordination.json',document)
 state.update(status='fresh-post-planning-reuse-coordination-issued',coordination_issued_ns=document['issued_ns'])
 save(HERE/'controller-result.json',state)
 return document

subprocess.check_call(['git','merge-base','--is-ancestor',REVIEWED,'HEAD'],cwd=ROOT)
publication_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
state=dict(reviewed_wrapper=REVIEWED,publication_base_head=publication_head,staged_payload_origin_commit='40029953e9e53525f0f1f431d6d56333b05183a3',
 frozen_import_source='78cb40c7837db049d645d73696f2e0b724ce8a3b',target='LightEFTSuppliedForestStage.SuppliedForestGoodEvent',
 status='entry-call-pending',entry_calls=0,coordination_callback_calls=0,automatic_retry=False,
 invoker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),controller_pid=os.getpid(),
 started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),started_ns=time.monotonic_ns())
with (HERE/'controller-result.json').open('x') as f:json.dump(state,f,indent=2);f.write('\n')
try:
 state.update(status='calling-reviewed-package-entry-once',entry_calls=1);save(HERE/'controller-result.json',state)
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
