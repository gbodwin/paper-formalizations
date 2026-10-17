"""Preparation-only tests: no Lean/checker subprocess may be spawned."""
import contextlib, fcntl, importlib, json, pathlib, tempfile, unittest
from unittest.mock import patch
import LightEFTExactSupervisor as s

class AdmissionTests(unittest.TestCase):
    def preflight(self, memory=4*1024**3):
        return dict(memory=dict(system_available=memory,cgroup_headroom=memory),
                    free_disk=3*1024**3, processes='PID PPID STAT COMMAND\n1 0 S python3\n')
    def test_memory_boundaries(self):
        s.admit(self.preflight())
        for key in ['system_available','cgroup_headroom']:
            p=self.preflight();p['memory'][key]-=1
            with self.assertRaises(RuntimeError):s.admit(p)
        p=self.preflight();p['memory']['cgroup_headroom']=None;s.admit(p)
    def test_disk_and_active_process(self):
        p=self.preflight();p['free_disk']=s.MIN_DISK
        with self.assertRaises(RuntimeError):s.admit(p)
        for command in ['lean','lake','leanchecker']:
            p=self.preflight();p['processes']+=f'2 1 S {command}\n'
            with self.assertRaises(RuntimeError):s.admit(p)
    def test_refusal_is_source_bound_and_no_spawn(self):
        with tempfile.TemporaryDirectory() as t, patch.object(s.subprocess,'Popen',side_effect=AssertionError('NO CHILD ALLOWED')):
            root=pathlib.Path(t);source=root/'input';source.write_text('snapshot')
            with patch.object(s,'LOCK',root/'lock'),patch.object(s,'memory_snapshot',return_value=self.preflight(0)['memory']),patch.object(s.subprocess,'check_output',return_value=self.preflight()['processes']):
                with self.assertRaises(RuntimeError):s.run_locked('refused',['/unused/lean'],root,root/'evidence',submitted_sources=[source])
            receipts=list((root/'evidence/attempts').glob('*/receipt.json'));self.assertEqual(len(receipts),1)
            receipt=json.loads(receipts[0].read_text());self.assertIsNone(receipt['child_pid']);self.assertIn('REFUSED',receipt['failure'])
            self.assertEqual(len(receipt['submitted_sources']),1)
            self.assertTrue((receipts[0].parent/(receipt['submitted_sources'][0]['sha256']+'.source')).exists())
    def test_lock_contention_records_without_spawn(self):
        with tempfile.TemporaryDirectory() as t,patch.object(s.subprocess,'Popen',side_effect=AssertionError('NO CHILD ALLOWED')):
            root=pathlib.Path(t)
            with patch.object(s,'LOCK',root/'lock'),(root/'lock').open('a+') as lock:
                fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
                with self.assertRaises(BlockingIOError):s.run_locked('busy',[],root,root/'evidence')
            receipt=json.loads(next((root/'evidence/attempts').glob('*/receipt.json')).read_text())
            self.assertIn('failure',receipt);self.assertIsNone(receipt['child_pid'])
    def test_startup_does_not_spawn(self):
        with tempfile.TemporaryDirectory() as t,patch.object(s.subprocess,'Popen',side_effect=AssertionError('NO CHILD ALLOWED')):
            root=pathlib.Path(t)
            with patch.object(s,'LOCK',root/'lock'),patch.object(s,'memory_snapshot',return_value=self.preflight()['memory']),patch.object(s.subprocess,'check_output',return_value=self.preflight()['processes']):
                self.assertEqual(s.run_locked('startup',[],root,root/'evidence'),'')
    def test_singleton_and_shadow_rejection(self):
        with tempfile.TemporaryDirectory() as t:
            root=pathlib.Path(t);a=root/'a';b=root/'b';a.mkdir();b.mkdir()
            obj=a/'Leaf.olean';obj.write_text('fake object; never executed')
            resolution=root/'resolution.json';resolution.write_text(json.dumps(dict(target='Leaf',count=1,resolved=[dict(module='Leaf',object=str(obj))])))
            env={'LEAN_PATH':str(a)+':'+str(b),'LIGHTEFT_CHECKER_RESOLUTION_FILE':str(resolution)}
            self.assertEqual(s.singleton(['leanchecker','-v','Leaf'],env)['object'],str(obj))
            (b/'Leaf.olean').write_text('duplicate')
            with self.assertRaises(ValueError):s.singleton(['leanchecker','-v','Leaf'],env)
            for target in ['LightEFTSpanners','LightSpanners']:
                with self.assertRaises(ValueError):s.singleton(['leanchecker','-v',target],env)
            (b/'Leaf.olean').unlink();(a/'Leaf').mkdir();(a/'Leaf/Child.olean').write_text('prefix')
            with self.assertRaises(ValueError):s.singleton(['leanchecker','-v','Leaf'],env)
    def test_harness_import_is_inert(self):
        with patch('subprocess.Popen',side_effect=AssertionError('NO CHILD ALLOWED')):
            importlib.import_module('LightEFTExactCI')

if __name__=='__main__':unittest.main()
