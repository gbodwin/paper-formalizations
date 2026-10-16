"""Process-safety tests use Python stand-ins only, never Lean/compiler processes."""
from pathlib import Path
import subprocess,sys,time,json,signal,fcntl,os
root=Path.cwd();ev=root/'checkpoints/directed-ci-20261016/supervisor-tests';ev.mkdir(exist_ok=True)
runner=root/'scripts/SequentialLean.py'
def start(label,seconds):
 return subprocess.Popen([sys.executable,str(runner),'--label',label,'--cwd',str(root),'--evidence',str(ev),'--',sys.executable,'-c',f'import time,os; print(os.getpid(),flush=True); time.sleep({seconds})'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
def receipt(label):
 for _ in range(200):
  for p in (ev/'attempts').glob('*/receipt.json'):
   r=json.loads(p.read_text())
   if r['label']==label and r['child_pid']:return r
  time.sleep(.01)
 raise AssertionError('No child receipt')
a=start('normal-a',.25);receipt('normal-a');b=start('normal-b',.1)
assert a.wait()==0 and b.wait()==0
ra,rb=receipt('normal-a'),receipt('normal-b')
assert ra['end_monotonic_ns']<=rb['start_monotonic_ns'] and ra['attempt_id']!=rb['attempt_id']
a=start('interrupt-term',10);r=receipt('interrupt-term');a.terminate();a.communicate(timeout=7)
r=receipt('interrupt-term');assert r['child_reaped'] and r['exit']!=0
# Kill the supervisor, not the stand-in. The child must retain the inherited lock.
a=start('interrupt-kill',1.5);r=receipt('interrupt-kill');a.kill();a.communicate(timeout=3)
held=False
with open('/tmp/distance-sparsification-single-compiler.lock','a+') as f:
 try:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:held=True
assert held,'Supervisor SIGKILL released lock while child still alive'
b=start('after-kill',.01);assert b.wait(timeout=4)==0
assert receipt('after-kill')['start_monotonic_ns']>r['start_monotonic_ns']+1_000_000_000
(ev/'result.json').write_text(json.dumps({'PASS':True,'uses_Lean':False,'mutual_exclusion':True,'unique_ids':True,'SIGTERM_child_reaped':True,'SIGKILL_child_retains_lock':True,'SIGKILL_incomplete_receipt_preserved':r['attempt_id']},indent=2)+'\n')
print('PASS: mutual exclusion, unique IDs, SIGTERM cleanup, SIGKILL inherited lock. No Lean executed.')
