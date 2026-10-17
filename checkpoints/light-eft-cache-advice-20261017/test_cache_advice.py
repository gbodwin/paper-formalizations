"""Harmless temporary-file tests; no Lean or child process is invoked."""
from pathlib import Path
import errno,fcntl,json,os,tempfile,unittest
from unittest.mock import patch
import pilot_cache_advice as a
class AdviceTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name);self.patch=patch.object(a,'PACKAGE_ROOT',self.root/'packages');self.patch.start()
        self.file=self.root/'packages/pkg/.lake/build/lib/lean/X.olean';self.file.parent.mkdir(parents=True);self.file.write_bytes(b'harmless file\n'*4096);self.log=self.root/'advice.jsonl';self.expected=a.hash_input(self.file)
    def tearDown(self):self.patch.stop();self.tmp.cleanup()
    def test_actual_advice_preserves_bytes_and_identity(self):
        self.assertEqual(a.hash_input(self.file,self.expected,self.log),self.expected)
        self.assertEqual(a.hash_input(self.file),self.expected)
        row=json.loads(self.log.read_text());self.assertTrue(row['advised']);self.assertIsNone(row['reclaimed_bytes'])
    def test_same_descriptor_is_regular_and_read_only(self):
        def advise(fd,offset,length,kind):
            self.assertEqual(fcntl.fcntl(fd,fcntl.F_GETFL)&os.O_ACCMODE,os.O_RDONLY)
            st=os.fstat(fd);self.assertEqual([st.st_dev,st.st_ino],self.expected['identity'][:2]);self.assertEqual((offset,length,kind),(0,0,os.POSIX_FADV_DONTNEED))
        with patch.object(a.os,'posix_fadvise',side_effect=advise) as fn:a.hash_input(self.file,self.expected,self.log);fn.assert_called_once()
    def test_bad_hash_refuses_before_advice(self):
        expected=dict(self.expected,sha256='0'*64)
        with patch.object(a.os,'posix_fadvise') as fn:
            with self.assertRaisesRegex(RuntimeError,'mismatch'):a.hash_input(self.file,expected,self.log)
            fn.assert_not_called()
    def test_replaced_identity_refuses(self):
        old=self.file.with_suffix('.old');self.file.rename(old);self.file.write_bytes(old.read_bytes())
        with patch.object(a.os,'posix_fadvise') as fn:
            with self.assertRaisesRegex(RuntimeError,'mismatch'):a.hash_input(self.file,self.expected,self.log)
            fn.assert_not_called()
    def test_symlink_no_follow(self):
        link=self.file.with_name('Link.olean');link.symlink_to(self.file)
        with patch.object(a.os,'posix_fadvise') as fn:
            with self.assertRaises(OSError):a.hash_input(link,self.expected,self.log)
            fn.assert_not_called()
    def test_uninventoried_file_refuses_advice(self):
        with patch.object(a.os,'posix_fadvise') as fn:
            with self.assertRaisesRegex(RuntimeError,'inventoried'):a.hash_input(self.file,None,self.log)
            fn.assert_not_called()
    def test_executable_and_shared_library_excluded(self):
        self.file.chmod(0o755);expected=a.hash_input(self.file)
        with patch.object(a.os,'posix_fadvise') as fn:
            a.hash_input(self.file,expected,self.log)
            lib=self.file.with_name('lib.so');lib.write_bytes(b'library fixture, never loaded');a.hash_input(lib,a.hash_input(lib),self.log);fn.assert_not_called()
    def test_evidence_and_project_outputs_excluded(self):
        with patch.object(a.os,'posix_fadvise') as fn:
            for name in ['evidence/output.olean','project/.lake/build/lib/lean/X.olean']:
                p=self.root/name;p.parent.mkdir(parents=True);p.write_bytes(b'untouched fixture');a.hash_input(p,a.hash_input(p),self.log)
            fn.assert_not_called()
    def test_advice_error_is_recorded_and_propagated(self):
        with patch.object(a.os,'posix_fadvise',side_effect=OSError(errno.EIO,'fixture advice error')):
            with self.assertRaises(OSError):a.hash_input(self.file,self.expected,self.log)
        row=json.loads(self.log.read_text());self.assertFalse(row['advised']);self.assertIn('fixture advice error',row['error']);self.assertEqual(a.hash_input(self.file),self.expected)
    def test_dependency_source_is_eligible(self):
        src=self.root/'packages/pkg/Module.lean';src.write_text('-- harmless source fixture')
        expected=a.hash_input(src)
        with patch.object(a.os,'posix_fadvise') as fn:
            self.assertEqual(a.hash_input(src,expected,self.log),expected);fn.assert_called_once()
    def test_runner_bridge_and_caps_unchanged(self):
        here=Path(__file__).resolve().parent;old=here.parent/'light-eft-bounded-pilot-runner-20261017'
        for name in ['pilot_child.py','pilot_accounting.py']:
            self.assertEqual((here/name).read_bytes(),(old/name).read_bytes())
        current=(here/'pilot_runner.py').read_text();prior=(old/'pilot_runner.py').read_text()
        for text in ["INTERVAL=.25", "DEADLINE=90.0", "check_memory(baseline,baseline,2*1024**3)", "check_memory(now,baseline,512*1024**2)", "'-j1','-M512','-DautoImplicit=false','-DwarningAsError=true'", "PILOT=REPO/'.lake/bounded-import-20261017-5ba09dcb949541f29eb286e312c9f8ea'"]:
            self.assertIn(text,current);self.assertIn(text,prior)
        self.assertIn("advice_log=evidence/'hash-advice-before.jsonl'",current)
        self.assertIn("digest(x['path'],expected=x,advice_log=evidence/'hash-advice-after.jsonl')",current)
        self.assertIn("HERE/'pilot_cache_advice.py'",current)
if __name__=='__main__':unittest.main(verbosity=2)
