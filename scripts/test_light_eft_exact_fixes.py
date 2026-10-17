"""Preparation fixtures and harmless Python process tests. Never launch Lean/Lake/checker."""
import ast, contextlib, hashlib, io, json, os, pathlib, signal, sys, tarfile, tempfile, unittest, shutil
from unittest.mock import patch
import LightEFTCgroup as cg
import LightEFTExactSupervisor as s
import LightEFTDependencyArtifact as art

class CgroupTests(unittest.TestCase):
    def fixture(self,member='/job/child',mountroot='/',point='/cg'):
        mount=f'1 0 0:24 {mountroot} {point} rw - cgroup2 cgroup rw\n'
        files={'/cg/cgroup.controllers':'cpu memory pids','/cg/cgroup.type':'domain',
               '/cg/job/memory.current':'1073741824','/cg/job/memory.max':'6442450944',
               '/cg/job/child/memory.current':'0','/cg/job/child/memory.max':'max'}
        return '0::'+member+'\n',mount,files
    def discover(self,member='/job/child',**kwargs):
        c,m,f=self.fixture(member,**kwargs)
        return cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_verified_global_root(self):
        r=self.discover('/');self.assertTrue(r['explicit_unlimited']);self.assertEqual(r['ancestors'],[])
    def test_nested_parent_limit(self):
        r=self.discover();self.assertEqual(r['cgroup_headroom'],5*1024**3);self.assertEqual(len(r['ancestors']),2)
    def test_leaf_limit_and_overcommitted_ancestor(self):
        c,m,f=self.fixture();f['/cg/job/child/memory.max']='100'
        self.assertEqual(cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])['cgroup_headroom'],100)
        f['/cg/job/memory.current']='6442450950'
        self.assertEqual(cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])['cgroup_headroom'],-6)
    def test_noninitial_namespace_refuses_even_slash_root(self):
        c,m,f=self.fixture('/')
        with self.assertRaisesRegex(ValueError,'Non-initial'):cg.discover(c,m,123456,lambda p:f[p])
    def test_truncated_and_dotdot_mounts_refuse(self):
        for root in ['/job','/..']:
            with self.assertRaises(ValueError):self.discover(mountroot=root)
    def test_full_mount_supplies_ancestors_despite_subtree_bind(self):
        c,m,f=self.fixture();m+='2 1 0:24 /job /bound rw - cgroup2 cgroup rw\n'
        r=cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p]);self.assertEqual(r['selected_mount']['mountpoint'],'/cg')
    def test_missing_or_bad_limit_never_unlimited(self):
        c,m,f=self.fixture()
        for path in ['/cg/job/memory.max','/cg/job/memory.current','/cg/job/child/memory.max']:
            bad=dict(f);del bad[path]
            with self.assertRaises(KeyError):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:bad[p])
        f['/cg/job/memory.max']='invalid'
        with self.assertRaises(ValueError):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_mount_escapes_and_ambiguous_hierarchies(self):
        c,m,f=self.fixture();m=m.replace('/cg ',r'/c\040g ');f={k.replace('/cg/','/c g/'):v for k,v in f.items()}
        self.assertEqual(cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])['selected_mount']['mountpoint'],'/c g')
        m+='2 1 1:2 / /other rw - cgroup2 cgroup rw\n'
        with self.assertRaises(ValueError):cg.discover(c,m,cg.INITIAL_CGROUP_NS_INO,lambda p:f[p])
    def test_missing_discovery_refuses_admission(self):
        with self.assertRaises(RuntimeError):s.admit({'memory':{'discovery_error':'missing file'}})

class LifecycleTests(unittest.TestCase):
    def run_case(self,code,expected_error=None):
        # Real harmless Python processes, temporary lock; no fake Lean binary/shim.
        with tempfile.TemporaryDirectory() as t:
            root=pathlib.Path(t);source=root/'child.py';source.write_text(code)
            def allow_python(argv,env):
                if pathlib.Path(argv[0]).resolve()!=pathlib.Path(sys.executable).resolve():raise AssertionError('Only harmless Python allowed in this fixture')
            with patch.object(s,'LOCK',root/'lock'),patch.object(s,'validate_command',side_effect=allow_python),patch.object(s,'memory_snapshot',return_value={'system_available':8*1024**3,'cgroup_headroom':8*1024**3}):
                args=['harmless-python',[sys.executable,str(source)],root,root/'evidence']
                if expected_error:
                    with self.assertRaises(expected_error):s.run_locked(*args,submitted_sources=[source])
                else:s.run_locked(*args,submitted_sources=[source])
            receipts=list((root/'evidence/attempts').glob('*/receipt.json'));self.assertEqual(len(receipts),1)
            receipt=json.loads(receipts[0].read_text());self.assertTrue(receipt['child_reaped']);self.assertTrue(receipt['all_descendants_gone'])
            self.assertEqual(s.descendants(),[])
            # The lock must be free only after all children have gone.
            import fcntl
            with (root/'lock').open('a+') as lock:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            if destination:=os.environ.get('LIGHTEFT_TEST_EVIDENCE'):
                dest=pathlib.Path(destination)/self._testMethodName/receipt['attempt_id']
                dest.parent.mkdir(parents=True,exist_ok=True);shutil.copytree(receipts[0].parent,dest)
            return receipt,(receipts[0].parent/'raw.log').read_text()
    def test_successful_child(self):
        r,raw=self.run_case("print('harmless lifecycle success')\n");self.assertEqual(r['exit'],0);self.assertIn('success',raw)
    def test_nonzero_child(self):
        r,raw=self.run_case("print('intentional harmless failure'); raise SystemExit(7)\n",RuntimeError);self.assertEqual(r['exit'],7)
    def test_term_interrupt_reaps(self):
        r,raw=self.run_case('import os,signal,time\nos.kill(os.getppid(),signal.SIGTERM)\ntime.sleep(30)\n',InterruptedError)
        self.assertIn('signal',r['failure'])
    def test_int_interrupt_reaps(self):
        r,raw=self.run_case('import os,signal,time\nos.kill(os.getppid(),signal.SIGINT)\ntime.sleep(30)\n',InterruptedError)
        self.assertIn('signal',r['failure'])
    def test_hup_interrupt_reaps(self):
        r,raw=self.run_case('import os,signal,time\nos.kill(os.getppid(),signal.SIGHUP)\ntime.sleep(30)\n',InterruptedError)
        self.assertIn('signal',r['failure'])
    def test_child_inherits_exclusive_lock(self):
        code="""import fcntl,pathlib
with pathlib.Path('lock').open('a+') as lock:
 try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:print('inherited lock excludes second open')
 else:raise RuntimeError('lock not held')
"""
        r,raw=self.run_case(code);self.assertIn('excludes second open',raw)
    def test_orphan_ignoring_term_is_reaped(self):
        code='''import os,signal,time
r,w=os.pipe()
pid=os.fork()
if pid==0:
 os.close(r)
 signal.signal(signal.SIGTERM,signal.SIG_IGN)
 os.setsid()
 os.write(w,b'ready');os.close(w)
 time.sleep(30)
 os._exit(0)
os.close(w);os.read(r,5);os.close(r)
print('grandchild',pid,flush=True)
'''
        r,raw=self.run_case(code);self.assertEqual(len(r['adopted_descendants_reaped']),1)
        self.assertEqual(os.waitstatus_to_exitcode(r['adopted_descendants_reaped'][0]['wait_status']),-signal.SIGKILL)

class ArtifactTests(unittest.TestCase):
    def test_no_unreviewed_artifact(self):
        with self.assertRaisesRegex(RuntimeError,'BLOCKED'):art.reviewed_spec(pathlib.Path(__file__).with_name('LightEFTDependencyArtifact.json'),[],None)
    def test_dependency_path_filter(self):
        base='.lake/packages/mathlib/.lake/build/lib/lean/'
        self.assertEqual(art.dependency_file(base+'Mathlib/X.olean',{'mathlib':'pin'}),('mathlib','Mathlib/X.lean'))
        for name in ['../x.olean','LightEFTSpanners/X.olean','LightSpanners.olean','Mathlib/X.lean','Mathlib//X.olean']:
            with self.assertRaises(ValueError):art.dependency_file(base+name,{'mathlib':'pin'})
    def test_hash_checked_artifact_without_subprocess(self):
        with tempfile.TemporaryDirectory() as t:
            root=pathlib.Path(t);e=root/'evidence';e.mkdir();source=root/'.lake/packages/mathlib/Mathlib/X.lean';source.parent.mkdir(parents=True);source.write_text('fixture source, not Lean-executed')
            obj=b'fixture object, not Lean-executed';path='.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/X.olean'
            h=lambda b:hashlib.sha256(b).hexdigest()
            manifest=dict(pins={'mathlib':'fixture'},toolchain='fixture',lake_manifest_sha256='fixture',official_archives=[dict(url='https://cache.mathlib.org/fixture.ltar',sha256='a'*64)],files=[dict(path=path,bytes=len(obj),sha256=h(obj),source_sha256=h(source.read_bytes()),archive_sha256='a'*64)])
            raw=json.dumps(manifest).encode();archive=root/'artifact.tar'
            with tarfile.open(archive,'w') as tar:
                for name,data in [(art.MANIFEST,raw),(path,obj)]:
                    entry=tarfile.TarInfo(name);entry.size=len(data);tar.addfile(entry,io.BytesIO(data))
            spec={k:manifest[k] for k in ['pins','toolchain','lake_manifest_sha256']};spec.update(bytes=archive.stat().st_size,sha256=art.digest(archive),manifest_sha256=h(raw),provenance_review='fixture only')
            with patch('subprocess.Popen',side_effect=AssertionError('No subprocess permitted')):
                result=art.install(archive,spec,root,e)
            self.assertEqual(result['lean_invocations'],0);self.assertEqual((root/path).read_bytes(),obj)
            with self.assertRaises(ValueError):art.install(archive,spec,root,e)

class StaticGateTests(unittest.TestCase):
    def test_no_cache_execution_and_success_after_finally(self):
        source=pathlib.Path(__file__).with_name('LightEFTExactCI.py').read_text();tree=ast.parse(source)
        self.assertNotIn('Cache.Main',source);self.assertNotIn('cache-bootstrap-',source);self.assertNotIn('official-cache-get',source)
        main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
        self.assertIsInstance(main.body[-2],ast.Try);self.assertTrue(main.body[-2].finalbody)
        self.assertIn('EXACT_SOURCE_PASS',ast.unparse(main.body[-1]))
        self.assertNotIn('EXACT_SOURCE_PASS',ast.unparse(main.body[-2]))
        # Execute only the extracted finalization/announcement control flow with
        # a deliberately failed Python finalizer, not the gate body or any Lean.
        final=ast.parse("try:\n pass\nfinally:\n finalize()\nprint('EXACT_SOURCE_PASS')\n")
        output=io.StringIO()
        def fail():raise RuntimeError('intentional reconciliation failure')
        with contextlib.redirect_stdout(output),self.assertRaises(RuntimeError):exec(compile(final,'fixture','exec'),{'finalize':fail})
        self.assertEqual(output.getvalue(),'')

if __name__=='__main__':unittest.main()
