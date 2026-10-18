from pathlib import Path
import json,sys,time,traceback
REPO=Path('/workspace/light-eft-verification')
ADAPTER=REPO/'checkpoints/light-eft-joint-flag-assignment-adapter-20261018'
OUT=REPO/'checkpoints/light-eft-joint-flag-assignment-result-20261018'
COMMIT='41f4e793e8d56f754c152964b5af9c2445f2706e'
sys.path.insert(0,str(ADAPTER))
from contracts import save
from authority import facts,known_released_lock
from driver import execute_production
called=False
def coordination():
 global called
 if called:raise RuntimeError('Coordination called more than once; no retry')
 called=True
 document=dict(approved_wrapper_commit=COMMIT,exclusive_worker=True,reviewer_idle=True,allow_new_epoch=True,
  same_directory='/tmp',allow_released_lock_reuse=True,released_lock_identity=known_released_lock()['identity'],
  coordination_reference='User/source-thread 01a144fe-14cb-74aa-b32b-6d4b9b1060c1 independently approves one bounded sequential joint-flag compile, exact singleton resolution, singleton replay and focused audit using implementation 41f4e793e8d56f754c152964b5af9c2445f2706e and draft 33e162e467cea919ee60d2c17e1f13d8586caba3; sole ordinary worker and idle reviewer; explicit exact known released inode33:3258 reuse bound to epoch f9446665c62e4e5c90b1578b930dd6ec and verified receipt; no automatic retry.',
  facts=facts(),issued_ns=time.monotonic_ns())
 save(OUT/'fresh-post-planning-coordination.json',document)
 print('Fresh coordination issued after read-only planning',flush=True)
 return document
print('One approved invocation; read-only planning begins',flush=True)
try:
 result=execute_production(reviewed_commit=COMMIT,coordination=coordination)
 save(OUT/'invocation-result.json',result)
 print(json.dumps(result),flush=True)
except BaseException as exc:
 save(OUT/'invocation-result.json',dict(accepted=False,failure=repr(exc),coordination_called=called,ended_ns=time.monotonic_ns()))
 traceback.print_exc();sys.exit(1)
sys.exit(0 if result.get('accepted') else 1)
