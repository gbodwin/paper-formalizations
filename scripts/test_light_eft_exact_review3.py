"""Third-review preparation tests. Only Python fixtures/harmless children execute."""
import contextlib,errno,fcntl,json,os,pathlib,signal,sys,tempfile,unittest,shutil
from unittest.mock import patch
import LightEFTCgroup as cg
import LightEFTExactSupervisor as s
import LightEFTProcessLifecycle as life
import test_light_eft_exact_fixes as previous

class MountTests(unittest.TestCase):
    def fixture(self):
        c,m,f=previous.CgroupTests().fixture();f.pop('/cg/cgroup.type')
        return c,m,f
    def test_realistic_root_has_no_cgroup_type(self):
        c,m,f=self.fixture();reads=[]
        def read(p):reads.append(p);return f[p]
        result=cg.discover('0::/\n',m,cg.INITIAL_CGROUP_NS_INO,read)
        self.assertTrue(result['initial_namespace_verified']);self.assertEqual(reads,['/cg/cgroup.controllers'])
    def test_leaf_same_device_subtree_bind(self):
        c,m,f=self.fixture();m+='2 1 0:24 /job/child /cg/job/child rw - cgroup2 cgroup rw\n'
        with self.assertRaisesRegex(ValueError,'overmounted'):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_ancestor_same_device_subtree_bind(self):
        c,m,f=self.fixture();m+='2 1 0:24 /job /cg/job rw - cgroup2 cgroup rw\n'
        with self.assertRaisesRegex(ValueError,'overmounted'):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_leaf_and_ancestor_noncgroup_overmounts(self):
        c,m,f=self.fixture()
        for point in ['/cg/job/child','/cg/job','/cg/job/memory.max','/cg/cgroup.controllers']:
            with self.subTest(point=point),self.assertRaisesRegex(ValueError,'overmounted'):
                cg.discover(c,m+f'2 1 1:2 / {point} rw - tmpfs tmpfs rw\n',cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_stacked_root_mount(self):
        c,m,f=self.fixture();m+='2 0 0:24 / /cg rw - cgroup2 cgroup rw\n'
        with self.assertRaisesRegex(ValueError,'overmounted'):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_overmount_above_selected_base(self):
        c,m,f=self.fixture()
        m='10 0 1:2 / / rw - ext4 disk rw\n11 10 1:3 / /host rw - tmpfs tmpfs rw\n1 11 0:24 / /host/cg rw - cgroup2 cgroup rw\n12 10 1:4 / /host rw - tmpfs tmpfs rw\n'
        f={k.replace('/cg/','/host/cg/'):v for k,v in f.items()}
        with self.assertRaisesRegex(ValueError,'overmounted'):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_visible_parent_mount_chain_is_accepted(self):
        c,m,f=self.fixture();m='10 0 1:2 / / rw - ext4 disk rw\n'+m.replace('1 0 ','1 10 ')
        self.assertEqual(cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])['cgroup_headroom'],5*1024**3)

class CleanupFaultTests(unittest.TestCase):
    CHILD='''import os,signal,time
r,w=os.pipe()
pid=os.fork()
if pid==0:
 os.close(r);signal.signal(signal.SIGTERM,signal.SIG_IGN)
 os.write(w,b'ready');os.close(w);time.sleep(20);os._exit(0)
os.close(w);os.read(r,5);os.close(r)
print('harmless descendant',pid,flush=True)
'''
    def run_fault(self,kind):
        with tempfile.TemporaryDirectory() as t:
            root=pathlib.Path(t);source=root/'child.py';source.write_text(self.CHILD)
            lockpath=root/'lock';events=[]
            def fault():
                with lockpath.open('a+') as other:
                    with self.assertRaises(BlockingIOError):fcntl.flock(other,fcntl.LOCK_EX|fcntl.LOCK_NB)
                events.append('injected '+kind+' with lock held')
                raise PermissionError(errno.EPERM,'intentional harmless '+kind+' fault')
            originals=dict(discovery=life.descendants,signaling=life.os.killpg,
                           subreaper=s.set_subreaper,finalization=s.os.fsync,barrier=s.cleanup)
            original=originals[kind];remaining=3 if kind=='discovery' else 1
            def injection(*args,**kwargs):
                nonlocal remaining
                eligible=kind!='subreaper' or (args and args[0]==0)
                if eligible and remaining:
                    remaining-=1;fault()
                return original(*args,**kwargs)
            targets=dict(discovery=(life,'descendants'),signaling=(life.os,'killpg'),
                         subreaper=(s,'set_subreaper'),finalization=(s.os,'fsync'),barrier=(s,'cleanup'))
            def python_only(argv,env):
                self.assertEqual(pathlib.Path(argv[0]).resolve(),pathlib.Path(sys.executable).resolve())
            owner,name=targets[kind]
            with patch.object(s,'LOCK',lockpath),patch.object(s,'validate_command',side_effect=python_only),patch.object(s,'memory_snapshot',return_value={'system_available':8*1024**3,'cgroup_headroom':8*1024**3}),patch.object(owner,name,side_effect=injection):
                with self.assertRaisesRegex(RuntimeError,'Cleanup/finalization errors'):
                    s.run_locked('fault-'+kind,[sys.executable,str(source)],root,root/'evidence',submitted_sources=[source])
            self.assertTrue(events);self.assertEqual(remaining,0)
            folder=next((root/'evidence/attempts').iterdir());receipt=json.loads((folder/'receipt.json').read_text())
            self.assertEqual(receipt['state'],'failed');self.assertTrue(receipt['cleanup_errors'])
            self.assertTrue(receipt['all_descendants_gone']);self.assertTrue(receipt['kernel_no_children_verified']);self.assertTrue(receipt['child_reaped'])
            self.assertEqual(life.descendants(),[]);self.assertEqual(life.set_subreaper(),0)
            with lockpath.open('a+') as lock:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            if dest:=os.environ.get('LIGHTEFT_TEST_EVIDENCE'):
                out=pathlib.Path(dest)/self._testMethodName/folder.name;out.parent.mkdir(parents=True,exist_ok=True)
                shutil.copytree(folder,out);(out/'injection-events.json').write_text(json.dumps(events,indent=2)+'\n')
    def test_discovery_errors_retain_lock_and_poison_success(self):self.run_fault('discovery')
    def test_signaling_error_retain_lock_and_poison_success(self):self.run_fault('signaling')
    def test_subreaper_restore_error_retries_under_lock(self):self.run_fault('subreaper')
    def test_finalization_io_error_retries_under_lock(self):self.run_fault('finalization')
    def test_unexpected_cleanup_error_hits_outer_barrier(self):self.run_fault('barrier')

if __name__=='__main__':unittest.main()
