from pathlib import Path
import json,sys,time,traceback
REPO=Path('/workspace/light-eft-verification')
ADAPTER=REPO/'checkpoints/light-eft-joint-flag-assignment-corrected-adapter-20261018'
OUT=REPO/'checkpoints/light-eft-joint-flag-assignment-corrected-result-20261018'
COMMIT='154e108179324f74f163049f2fe450be5522d616'
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
  coordination_reference='User/source-thread 01a144fe-14cb-74aa-b32b-6d4b9b1060c1 independently approves one bounded sequential joint-flag compile, exact singleton resolution, singleton replay and focused audit using implementation 154e108179324f74f163049f2fe450be5522d616 and draft 7a4ab29cebfdd86808d4d6708411967fdb4a3bd4; sole ordinary worker and idle reviewer; explicit exact known released inode33:3258 reuse bound to epoch 9dd0d7e576bc4fb7b7fa05d4413d4bff and verified 719-byte receipt SHA256 06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1; reviewed evidence 84b22163e171e8146cff0af75cb8209811a18ade; unchanged 77 dependencies, 78 imports, 16 roots, eight interfaces, six preservation-only source/object bindings and 3/3/4/4 GiB gates; no automatic retry.',
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
