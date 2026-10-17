"""Focused unittest/mocking fixtures following the existing lifecycle suite.
Only real harmless Python children execute. Never call production run_once.
"""
import contextlib,fcntl,json,os,pathlib,resource,shutil,sys,tempfile,unittest
from unittest.mock import patch
import pilot_runner as p
import pilot_child as launch
import LightEFTProcessLifecycle as life
import test_light_eft_exact_review3 as prior

class Accounting:
    def __init__(self,fail=False):self.calls=0;self.fail=fail
    def sample(self):
        self.calls+=1
        if self.fail and self.calls>1:raise OSError('intentional unreadable accounting')
        return {'headroom':8*1024**3,'system_available':8*1024**3,'nodes':[{'path':'fixture','limit':str(16*1024**3),'current':0,'oom':{'oom':0,'oom_kill':0,'oom_group_kill':0}}],'qualification':'TEST_FIXTURE_NOT_REAL_ADMISSION'}

class PilotTests(unittest.TestCase):
    def case(self,code,failure=False,account=None,deadline=90,readback=False,cleanup_fault=False,bad_launcher=False):
        with tempfile.TemporaryDirectory() as t:
            root=pathlib.Path(t);work=root/'pilot';work.mkdir();source=work/'harmless.py';source.write_text(code);lock=root/'lock';lock.touch();evidence=root/'evidence'
            plan={'source':str(source),'argv':[sys.executable,'-I',str(source)],'cwd':str(work),'env':{'LANG':'C.UTF-8','LC_ALL':'C.UTF-8'},'inputs':[str(source),str(p.HERE/'pilot_runner.py'),str(p.HERE/'pilot_child.py')]}
            events=[]
            def only_python(plan):self.assertEqual(pathlib.Path(plan['argv'][0]).resolve(),pathlib.Path(sys.executable).resolve())
            real_cleanup=life.cleanup;remaining=1
            def faulty(*a,**kw):
                nonlocal remaining
                if remaining:
                    remaining-=1
                    with lock.open('r+') as other:
                        with self.assertRaises(BlockingIOError):fcntl.flock(other,fcntl.LOCK_EX|fcntl.LOCK_NB)
                    events.append('cleanup failure injected; lock excludes second opener')
                    raise OSError('intentional cleanup failure')
                return real_cleanup(*a,**kw)
            with contextlib.ExitStack() as stack:
                stack.enter_context(patch.object(p,'LOCK',lock));stack.enter_context(patch.object(p,'validate_plan',side_effect=only_python));stack.enter_context(patch.object(p,'DEADLINE',deadline))
                if readback:stack.enter_context(patch.object(p.resource,'prlimit',return_value=(1,1)))
                if cleanup_fault:stack.enter_context(patch.object(life,'cleanup',side_effect=faulty))
                if bad_launcher:
                    helper=root/'helper';helper.mkdir()
                    original=(p.HERE/'pilot_child.py').read_text()
                    (helper/'pilot_child.py').write_text(original.replace('actual=configure()',"raise OSError('intentional limit setup failure')"))
                    stack.enter_context(patch.object(p,'HERE',helper))
                if failure:
                    with self.assertRaises(RuntimeError):p._run(plan,work,evidence,account or Accounting())
                else:p._run(plan,work,evidence,account or Accounting())
            r=json.loads((evidence/'receipt.json').read_text())
            self.assertTrue(r['direct_reaped']);self.assertTrue(r['kernel_no_children_verified']);self.assertTrue(r['all_descendants_gone']);self.assertEqual(life.descendants(),[]);self.assertEqual(life.set_subreaper(),0)
            self.assertEqual(r['direct_wait_owner'],'runner wait4')
            with lock.open('r+') as f:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
            if dest:=os.environ.get('LIGHTEFT_TEST_EVIDENCE'):
                out=pathlib.Path(dest)/self._testMethodName/r['attempt_id'];out.parent.mkdir(parents=True,exist_ok=True);shutil.copytree(evidence,out)
                (out/'test-events.json').write_text(json.dumps(events)+'\n')
            return r,(evidence/'raw.log').read_text()
    def test_success_limits_and_handshake(self):
        r,log=self.case("import resource,os\nprint('payload',os.getpid(),resource.getrlimit(resource.RLIMIT_AS),flush=True)\n")
        self.assertEqual(r['handshake']['limits'],{k:[v,v] for k,v in launch.LIMITS.items()});self.assertIn('1610612736',log);self.assertTrue(r['preserved_inputs_verified'])
    def test_limit_setup_failure_never_executes_payload(self):
        r,log=self.case("print('PAYLOAD_MUST_NOT_RUN')",failure=True,bad_launcher=True)
        self.assertNotIn('PAYLOAD_MUST_NOT_RUN',log);self.assertIn('setup',r['failure'])
    def test_limit_kernel_readback_failure_never_executes_payload(self):
        r,log=self.case("print('PAYLOAD_MUST_NOT_RUN')",failure=True,readback=True)
        self.assertNotIn('PAYLOAD_MUST_NOT_RUN',log);self.assertIn('readback',r['failure'])
    def test_deadline_kills_child_not_supervisor(self):
        r,_=self.case('import time,signal\nsignal.signal(signal.SIGTERM,signal.SIG_IGN)\ntime.sleep(30)',failure=True,deadline=.7)
        self.assertIn('deadline',r['failure']);self.assertEqual(r['exit'],-9)
    def test_detached_adopted_child_is_failure_and_reaped(self):
        code=prior.CleanupFaultTests.CHILD.replace('os.close(r);signal.signal','os.close(r);os.setsid();signal.signal')
        r,_=self.case(code,failure=True)
        self.assertIn('descendant',r['failure'].lower());self.assertTrue(r['adopted_descendants_reaped'])
    def test_unreadable_monitor_fails_and_reaps(self):
        r,_=self.case('import time;time.sleep(30)',failure=True,account=Accounting(fail=True))
        self.assertIn('unreadable accounting',r['failure'])
    def test_cleanup_failure_retains_exclusion(self):
        r,_=self.case("print('ordinary harmless exit')",failure=True,cleanup_fault=True)
        self.assertTrue(r['cleanup_errors'])
    def test_limit_set_readback_unit_failure(self):
        with patch.object(launch.resource,'setrlimit') as setter,patch.object(launch.resource,'getrlimit',return_value=(0,0)):
            with self.assertRaisesRegex(RuntimeError,'readback'):launch.configure()
            setter.assert_called_once_with(resource.RLIMIT_AS,(1610612736,1610612736))
    def test_lock_collision_no_child(self):
        with tempfile.TemporaryDirectory() as t:
            root=pathlib.Path(t);lock=root/'lock';lock.touch()
            with lock.open('r+') as f,patch.object(p,'LOCK',lock),patch.object(p.subprocess,'Popen',side_effect=AssertionError('NO CHILD')):
                fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
                with self.assertRaises(BlockingIOError):p._run({'argv':[],'env':{}},root,root/'evidence',Accounting())
                r=json.loads((root/'evidence/receipt.json').read_text());self.assertEqual(r['state'],'refused-lock')
    def test_evidence_collision_rejected(self):
        with tempfile.TemporaryDirectory() as t,patch.object(p.subprocess,'Popen',side_effect=AssertionError('NO CHILD')):
            root=pathlib.Path(t)
            with self.assertRaises(FileExistsError):p._run({'argv':[],'env':{}},root,root,Accounting())
    def test_monitor_floors_and_oom(self):
        base=Accounting().sample();low=Accounting().sample();low['headroom']=512*1024**2-1
        with self.assertRaisesRegex(RuntimeError,'headroom'):p.check_memory(low,base,512*1024**2)
        oom=Accounting().sample();oom['nodes'][0]['oom']['oom_kill']=1
        with self.assertRaisesRegex(RuntimeError,'OOM'):p.check_memory(oom,base,512*1024**2)
        changed=Accounting().sample();changed['nodes'][0]['limit']='max'
        with self.assertRaisesRegex(RuntimeError,'limit'):p.check_memory(changed,base,512*1024**2)

if __name__=='__main__':unittest.main(verbosity=2)
