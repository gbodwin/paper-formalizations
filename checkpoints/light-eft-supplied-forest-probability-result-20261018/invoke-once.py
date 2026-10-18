from pathlib import Path
import json,sys,time,traceback
REPO=Path('/workspace/light-eft-verification')
ADAPTER=REPO/'checkpoints/light-eft-supplied-forest-probability-adapter-20261018'
OUT=REPO/'checkpoints/light-eft-supplied-forest-probability-result-20261018'
COMMIT='b6483cccabdf4afdbb8004a768afe8ea9ed0ff32'
sys.path.insert(0,str(ADAPTER))
from contracts import save
from authority import facts,known_released_lock
from driver import execute_production
called=False
def coordination():
 global called
 if called: raise RuntimeError('Coordinator called more than once; no retry')
 called=True
 document=dict(approved_wrapper_commit=COMMIT,exclusive_worker=True,reviewer_idle=True,
  allow_new_epoch=True,same_directory='/tmp',allow_released_lock_reuse=True,
  released_lock_identity=known_released_lock()['identity'],
  coordination_reference='User/source-thread 01a144fe-14cb-74aa-b32b-6d4b9b1060c1 independently approves exactly one sequential probability-package compile, exact resolution, singleton replay and focused audit using implementation b6483cccabdf4afdbb8004a768afe8ea9ed0ff32 and draft 88d297fa58a15406aac6e7c0ea3c85f65965d19a; reviewer idle; sole worker; explicit exact known released-lock inode33:3258 reuse; no automatic retry.',
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
 traceback.print_exc()
 sys.exit(1)
sys.exit(0 if result.get('accepted') else 1)
