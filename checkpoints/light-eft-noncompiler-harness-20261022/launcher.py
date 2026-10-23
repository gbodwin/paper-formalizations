"""Diagnostic-only adapter to the unchanged private Python-fixture supervisor.

The legacy stage token 'compile' selects the existing non-audit resource/output
class ONLY. synthetic_fixture is true; exact Python argv is independently
authenticated here. This is never a CI Lean plan or a production acceptance.
"""
from pathlib import Path
import hashlib, json, os, signal, stat, subprocess, sys, time, traceback
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]
ENGINE=REPO/'checkpoints/light-eft-canonical-output-adapter-20261020'
BRANCH='refs/heads/light-eft-spanners-checkpoints'
WORKFLOW='.github/workflows/light-eft-noncompiler-diagnostics.yml'
NON_AUDIT_ENGINE_TOKEN='compile'

def require(ok,message):
 if not ok:raise RuntimeError(message)

def main():
 require(sys.flags.isolated and sys.dont_write_bytecode,'Isolated -I -B bootstrap required')
 require(os.environ.get('GITHUB_ACTIONS')=='true' and os.environ.get('GITHUB_REPOSITORY')=='gbodwin/paper-formalizations','Not reviewed repository runner')
 require(os.environ.get('GITHUB_REF')==BRANCH and os.environ.get('GITHUB_EVENT_NAME')=='push','Diagnostic-only excluded-branch push required')
 require(os.environ.get('GITHUB_JOB')=='diagnostic' and os.environ.get('LEAN_NUM_THREADS')=='1','Diagnostic job/thread identity differs')
 head=os.environ['GITHUB_SHA'];run=os.environ['GITHUB_RUN_ID'];attempt=os.environ['GITHUB_RUN_ATTEMPT']
 require(len(head)==40 and all(c in '0123456789abcdef' for c in head) and run.isdecimal() and attempt.isdecimal(),'Bad exact event identity')
 require(os.environ.get('GITHUB_WORKFLOW_SHA')==head and os.environ.get('GITHUB_WORKFLOW_REF')=='gbodwin/paper-formalizations/'+WORKFLOW+'@'+BRANCH,'Actual workflow differs')
 require(os.environ.get('LIGHTEFT_JOB_WORKFLOW_SHA')==head and
   os.environ.get('LIGHTEFT_JOB_WORKFLOW_PATH')==WORKFLOW and
   os.environ.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY')=='gbodwin/paper-formalizations' and
   os.environ.get('LIGHTEFT_JOB_WORKFLOW_REF') in ['gbodwin/paper-formalizations/'+WORKFLOW+'@'+BRANCH,'gbodwin/paper-formalizations/'+WORKFLOW+'@'+head],
   'Actual job workflow identity differs')
 temp=Path(os.environ['RUNNER_TEMP']);require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(),'Invalid runner temp')
 root=temp/('light-eft-noncompiler-'+run+'-'+attempt);root.mkdir(mode=0o700)
 require(signal.getitimer(signal.ITIMER_REAL)==(0.0,0.0),'Existing admission timer')
 old_alarm=signal.getsignal(signal.SIGALRM)
 def expired(*unused):raise TimeoutError('Diagnostic source/admission exceeded 90 seconds')
 signal.signal(signal.SIGALRM,expired);signal.setitimer(signal.ITIMER_REAL,90)
 try:
  raw=(HERE/'bindings.json').read_bytes()
  require(hashlib.sha256(raw).hexdigest()==os.environ['LIGHTEFT_DIAGNOSTIC_BINDINGS_SHA'],'Diagnostic binding bytes differ')
  spec=json.loads(raw);rows=spec['files'];require(0<len(rows)<=80,'Finite source binding count')
  require(sum(r['bytes'] for r in rows)<=2*1024**2,'Finite source byte budget')
  os.environ['PATH']='/usr/bin:/bin'
  require(subprocess.check_output(['/usr/bin/git','rev-parse','HEAD'],cwd=REPO,text=True).strip()==head,'Exact checkout SHA differs')
  require(not subprocess.check_output(['/usr/bin/git','status','--porcelain'],cwd=REPO),'Dirty checkout')
  def authenticate():
   for row in rows:
    p=REPO/row['path'];require(not Path(row['path']).is_absolute() and '..' not in Path(row['path']).parts,'Unsafe source binding path')
    for q in [p,*p.parents]:require(not q.is_symlink(),'Source parent/symlink differs')
    st=p.stat();require(stat.S_ISREG(st.st_mode) and st.st_nlink==1 and st.st_size==row['bytes'],'Nonregular source binding')
    b=p.read_bytes();require(hashlib.sha256(b).hexdigest()==row['sha256'],'Source hash differs')
    require(subprocess.check_output(['/usr/bin/git','show',head+':'+row['path']],cwd=REPO)==b,'Source not exact event Git bytes')
  authenticate()
  require((REPO/WORKFLOW).read_bytes()==(HERE/'PROPOSED-workflow.yml').read_bytes(),'Submitted workflow differs from reviewed proposal')
  # A new absent prefix ensures authenticated source imports ignore old pyc.
  sys.pycache_prefix=str(root/'absent-python-cache');require(not Path(sys.pycache_prefix).exists(),'Cache prefix already exists')
  sys.path[:0]=[str(ENGINE),str(REPO/'scripts')]
  from LightEFTCgroup import memory_snapshot
  from ci_accounting import CIAccounting
  from ci_lease import CILease
  from contracts import bind,save,unchanged
  import child_runner
  account=CIAccounting(memory_snapshot);before=account.sample()
  # Retain the outer 8-GiB recovery admission as well as engine runtime floors.
  require(before['headroom']>=8*1024**3 and before['system_available']>=8*1024**3,'Existing outer 8-GiB admission failed')
  child_runner.assert_idle('noncompiler-before-claim',{})
  source_bindings={str(REPO/r['path']):bind(REPO/r['path']) for r in rows}
  python=Path(sys.executable).resolve();source_bindings[str(python)]=bind(python)
  source_bindings[str(HERE/'bindings.json')]=bind(HERE/'bindings.json')
  source_bindings[str(REPO/WORKFLOW)]=bind(REPO/WORKFLOW)
  source_bindings[str(HERE/'PROPOSED-workflow.yml')]=bind(HERE/'PROPOSED-workflow.yml')
  work=root/'work';work.mkdir();objects=root/'empty-objects';objects.mkdir();audit=root/'empty-audit';audit.mkdir()
  plan=dict(stage=NON_AUDIT_ENGINE_TOKEN,argv=[str(python),'-I','-B',str(HERE/'payload.py'),'--child',str(work)],
   env=dict(LANG='C.UTF-8',LC_ALL='C.UTF-8',PATH='/usr/bin:/bin',LEAN_NUM_THREADS='1',MIMALLOC_ARENA_RESERVE='128MiB',MIMALLOC_VERBOSE='1'),cwd=str(work))
  frozen=json.dumps(plan,sort_keys=True)
  identity={k:os.environ.get(k) for k in ['GITHUB_ACTIONS','GITHUB_REPOSITORY','GITHUB_EVENT_NAME',
    'GITHUB_SHA','GITHUB_REF','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_WORKFLOW_SHA','GITHUB_WORKFLOW_REF',
    'GITHUB_JOB','LEAN_NUM_THREADS','LIGHTEFT_JOB_WORKFLOW_SHA','LIGHTEFT_JOB_WORKFLOW_PATH',
    'LIGHTEFT_JOB_WORKFLOW_REPOSITORY','LIGHTEFT_JOB_WORKFLOW_REF','LIGHTEFT_DIAGNOSTIC_BINDINGS_SHA']}
  def check_identity():
   require({k:os.environ.get(k) for k in identity}==identity,'Diagnostic run identity drift')
  class DiagnosticContext:
   fixture=True;source_commit=head;wrapper_commit=head
   def __init__(self,lease):
    self.lease=lease;self.lock=lease.file;self.acquired_ns=lease.acquired_ns;self.preservation_failed=False
   def visible_gate(self,p):return 8*1024**3
   def verify(self,p):
    require(json.dumps(p,sort_keys=True)==frozen,'Changed diagnostic argv/env/stage/cwd')
    require(p['argv']==[str(python),'-I','-B',str(HERE/'payload.py'),'--child',str(work)],'Non-Python diagnostic command')
    self.lease.check();unchanged(source_bindings);authenticate()
    require(not list(objects.iterdir()) and not list(audit.iterdir()),'Unexpected compiler/audit outputs')
   def before_child(self,p,r,persist):
    self.verify(p)
    r.update(stage_kind='NON_COMPILER_DIAGNOSTIC',diagnostic_only=True,qualification_acceptance=False,
      resource_class='ordinary non-audit Python fixture; legacy stage token only',
      planned_command=json.loads(frozen),working_directory=str(work),
      output_guard_spec=dict(stage=NON_AUDIT_ENGINE_TOKEN,objects=str(objects),target=str(objects/'NeverProduced.olean'),audit=str(audit),protected=source_bindings))
    persist()
   def prepare_child(self,p,r,persist,accounting):
    self.verify(p);child_runner.assert_idle('noncompiler-preflight',r)
    now=accounting.sample();child_runner.check_memory(now,before,8*1024**3)
    require(now['system_available']>=8*1024**3,'Outer host admission drift')
    import shutil
    require(shutil.disk_usage(work).free>2*1024**3,'Existing free-disk admission failed')
    r['admission']=now;persist();return now
   def preexec(self,p,r,persist):
    import shutil
    self.verify(p);free=shutil.disk_usage(work).free
    require(free>2*1024**3,'Fresh preexec disk below boundary')
    r.update(preexec_binding_verified=True,preexec_disk_bytes=free);persist()
   def after_child(self,p,r,persist):
    self.verify(p)
    if r.get('exit')==0 and 'failure' not in r:
     path=work/'result.json';require(path.is_file() and not path.is_symlink() and path.stat().st_size<=1024**2,'Missing/unbounded diagnostic result')
     data=json.loads(path.read_text());require(data.get('scope')=='NON_COMPILER_COMPONENT_DIAGNOSTIC' and data.get('accepted') is True,'Diagnostic component failure')
     require((root/'runtime/raw.log').read_text().strip()=='NONCOMPILER_DIFFERENTIAL_COMPONENTS_PASS','Missing/duplicate diagnostic marker')
     r['diagnostic_result']=bind(path)
    r['between_child_preservation_passed']=True;persist()
   def complete_log(self,path,r,persist):
    r.setdefault('completed_logs',{})[path.name]=bind(path);persist()
   def output_summary(self):return dict(production_acceptance=False,generated_Lean_objects=[],audit_exports=[])
  save(root/'diagnostic-plan.json',dict(identity=identity,plan=plan,source_bindings=source_bindings,
   original_populated_roots='unavailable; no compiler/setup/cache action permitted'))
  # Source/admission alarm is explicitly cancelled before the unchanged engine
  # installs its own 300-s preflight / 90-s whole-child supervision.
 except BaseException as error:
  (root/'admission-failure.json').write_text(json.dumps(dict(type=type(error).__name__,
    error=str(error),partial=getattr(error,'partial',None),traceback=traceback.format_exc()),indent=2)+'\n')
  raise
 finally:
  signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old_alarm)
 try:
  with CILease(root,save,check_identity) as lease:
   plan['env'].update(LIGHTEFT_DIAGNOSTIC_LOCK_FD=str(lease.file.fileno()),LIGHTEFT_DIAGNOSTIC_LOCK_PATH=str(lease.path))
   plan['env'].update(LIGHTEFT_DIAGNOSTIC_IDENTITY=json.dumps(identity,separators=(',',':')),
                     LIGHTEFT_DIAGNOSTIC_LEASE=json.dumps(lease.record,separators=(',',':')))
   frozen=json.dumps(plan,sort_keys=True)
   save(root/'submitted-diagnostic-plan.json',dict(identity=identity,plan=plan,source_bindings=source_bindings))
   ctx=DiagnosticContext(lease)
   r=child_runner.run_child(plan,work,root/'runtime',ctx,accounting=account)
   require(r['state']=='finished' and r['exit']==0 and not r.get('failure') and
     r.get('direct_reaped') is True and r.get('kernel_no_children_verified') is True and
     r.get('all_descendants_gone') is True and
     not r.get('cleanup_errors'),'Incomplete diagnostic lifecycle')
  require(lease.record['state']=='released' and lease.record.get('kernel_echild') and not lease.record.get('release_errors'),'Unreleased diagnostic lease')
  save(root/'result-summary.json',dict(component_diagnostic_passed=True,production_acceptance=False,
    identity=identity,attempt=r['attempt_id'],lease=lease.record))
 except BaseException as error:
  save(root/'diagnostic-failure.json',dict(type=type(error).__name__,error=str(error),traceback=traceback.format_exc()))
  raise

if __name__=='__main__':main()
