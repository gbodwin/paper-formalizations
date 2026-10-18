"""Focused Python-only delta fixtures. No child process or system resource probe."""
from pathlib import Path
import contextlib,csv,hashlib,json,os,sys,types,unittest,uuid
from unittest.mock import patch
import contracts as c
import focused_audit as audit
import output_guards as guards
import child_runner as runner
import pilot_child
HERE=Path(__file__).resolve().parent
RUN=HERE/'test-evidence'/uuid.uuid4().hex;RUN.mkdir(parents=True)
SOURCE_SNAPSHOT=RUN/'implementation';SOURCE_SNAPSHOT.mkdir()
for p in HERE.glob('*.py'):(SOURCE_SNAPSHOT/(p.name+'.txt')).write_bytes(p.read_bytes())
def put(path,data=b'fixture'):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);return path
class BeforeLaunch(Exception):pass
class Delta(unittest.TestCase):
 def setUp(self):
  self.root=RUN/self._testMethodName;self.root.mkdir()
  self.events=[]
 def tearDown(self):c.save(self.root/'fixture-events.json',self.events)
 def faithful(self):
  ci=self.root/'ci';ci.mkdir()
  _,b=c.regular(HERE/'fixtures/faithful-recursive-closure.tsv')
  lines=b.decode().splitlines(keepends=True);rows=list(csv.DictReader(lines,delimiter='\t'))
  header=lines[0]
  root=f"{c.THEOREM}\t{c.TARGET}\ttheorem\t\tAnd.rec,Nat.rec,List.rec\tfalse\tfalse\n"
  put(ci/'recursive-dependencies.tsv',(header+root+''.join(lines[1:])).encode())
  put(ci/'actual-owner-inventory.tsv',f"owner\tname\tkind\tunsafe\tpartial\n{c.TARGET}\t{c.THEOREM}\ttheorem\tfalse\tfalse\n".encode())
  loaded=sorted({r['owner'] for r in rows}|{c.TARGET})
  put(ci/'import-closure-loaded.txt',('\n'.join(loaded)+'\n').encode())
  put(ci/'strict-violations.txt',b'\n')
  ax=sorted(r['name'] for r in rows if r['kind']=='axiom')
  opaque=sum(r['kind']=='opaque' for r in rows)
  raw=f"PASS: 1 new-module actual-owner declarations; {len(rows)+1} recursive constants, {opaque} opaque bodies; axioms [{', '.join(ax)}]\n"
  put(self.root/'raw.log',raw.encode())
  return ci,raw
 def live(self,stage):
  root=self.root/stage;root.mkdir()
  objects=root/'objects';objects.mkdir()
  target=put(objects/'LightEFTSpanners/SuppliedForestGoodEvent.olean',b'completed')
  auditdir=root/'audit';auditdir.mkdir()
  fdfile=put(root/'simulated-owner-fd',b'not a lock acquisition')
  handle=fdfile.open('r+b');self.addCleanup(handle.close);st=os.fstat(handle.fileno())
  resolution=put(root/'resolution.json',b'completed resolution')
  protected={} if stage=='compile' else {str(p):c.bind(p) for p in [target,resolution]}
  record={'lock':{'fd':handle.fileno(),'path':str(fdfile),'device':st.st_dev,'inode':st.st_ino},
   'output_guard_spec':{'stage':stage,'objects':str(objects),'target':str(target),'audit':str(auditdir),'protected':protected}}
  return record,target,auditdir,resolution
 def test_faithful_recursors_and_duplicate_edges_pass(self):
  ci,raw=self.faithful()
  seed=list(csv.DictReader((HERE/'fixtures/faithful-recursors.tsv').open(),delimiter='\t'))
  self.assertEqual(seed[0]['bodyDependencies'],'And,And.intro,And,And.intro')
  for row in seed:self.assertGreater(len(row['bodyDependencies'].split(',')),len(set(row['bodyDependencies'].split(','))))
  result=audit.validate(ci,[],raw)
  self.assertEqual(result['recursive_constants'],12)
  self.events.append({'faithful_recursors':[r['name'] for r in seed],'accepted_constants':12})
 def test_empty_dependency_name_still_rejected(self):
  ci,raw=self.faithful();p=ci/'recursive-dependencies.tsv'
  p.write_text(p.read_text().replace('And,And.intro,And,And.intro','And,,And.intro'))
  with self.assertRaisesRegex(c.Rejected,'Empty dependency name'):audit.validate(ci,[],raw)
 def test_dangling_reference_still_rejected(self):
  ci,raw=self.faithful();p=ci/'recursive-dependencies.tsv'
  p.write_text(p.read_text().replace('And,And.intro,And,And.intro','And,And.intro,missing.constant'))
  with self.assertRaisesRegex(c.Rejected,'Dangling'):audit.validate(ci,[],raw)
 def test_recursors_export_and_reconstruct(self):
  ci,raw=self.faithful();audit.validate(ci,[],raw)
  exports=audit.export_all(ci,self.root/'raw.log',self.root/'exports')
  self.assertEqual(len(exports),5)
  for name in c.EXPORTS:audit.verify_chunks(self.root/'exports'/name,ci/name)
 def test_growing_compile_and_audit_files_no_content_reader(self):
  for stage in ['compile','audit']:
   with self.subTest(stage=stage):
    record,target,ci,_=self.live(stage)
    active=target if stage=='compile' else put(ci/'recursive-dependencies.tsv',b'header\n')
    writer=active.open('ab');self.addCleanup(writer.close)
    original=Path.lstat;written=[]
    def growing(path,*args,**kwargs):
     s=original(path,*args,**kwargs)
     if path==active and not written:
      writer.write(b'growth during metadata sample\n');writer.flush();written.append(True)
     return s
    with patch.object(Path,'lstat',growing),patch.object(c,'regular',side_effect=AssertionError('live content read forbidden')),patch.object(c,'bind',side_effect=AssertionError('live hashing forbidden')),patch.object(c,'tree',side_effect=AssertionError('stable tree reader forbidden')):
     self.assertEqual(guards.runtime_errors(record),[])
    self.assertTrue(written);self.assertGreater(active.stat().st_size,9)
    self.events.append({'stage':stage,'grew_inside_metadata_sample':True,'size_after':active.stat().st_size})
 def test_invalid_file_and_directory_paths_rejected(self):
  for stage in ['compile','audit']:
   record,target,ci,_=self.live(stage);base=target.parent if stage=='compile' else ci
   unknown=put(base/'unexpected.olean')
   self.assertTrue(guards.runtime_errors(record));unknown.unlink()
   (base/'unexpected-directory').mkdir()
   self.assertTrue(guards.runtime_errors(record))
 def test_links_and_nonregular_files_rejected(self):
  for stage in ['compile','audit']:
   for kind in ['symlink','hardlink','fifo']:
    with self.subTest(stage=stage,kind=kind):
     record,target,ci,_=self.live(stage)
     active=target if stage=='compile' else put(ci/'recursive-dependencies.tsv')
     active.unlink();other=put(self.root/('source-'+stage+'-'+kind))
     if kind=='symlink':active.symlink_to(other)
     elif kind=='hardlink':os.link(other,active)
     else:os.mkfifo(active)
     self.assertTrue(guards.runtime_errors(record))
     self.events.append({'stage':stage,'kind':kind,'rejected':True})
     if kind=='fifo':active.unlink()
     (self.root/stage).rename(self.root/(stage+'-'+kind))
 def test_audit_root_symlink_rejected_even_before_audit(self):
  record,_,ci,_=self.live('compile');ci.rmdir()
  other=self.root/'empty';other.mkdir();ci.symlink_to(other,target_is_directory=True)
  self.assertTrue(guards.runtime_errors(record))
 def test_oversize_object_and_audit_metadata_rejected(self):
  for stage,size in [('compile',16*1024**2+1),('audit',64*1024**2+1)]:
   record,target,ci,_=self.live(stage)
   active=target if stage=='compile' else ci/'recursive-dependencies.tsv'
   with active.open('wb') as f:f.truncate(size)
   self.assertTrue(guards.runtime_errors(record))
   self.events.append({'stage':stage,'logical_bytes':active.stat().st_size,'rejected':True,'large_sparse_fixture_removed':True})
   active.unlink()
 def test_completed_objects_and_resolution_remain_immutable(self):
  record,target,_,resolution=self.live('audit')
  for p in [target,resolution]:
   old=p.read_bytes();p.write_bytes(old+b'changed')
   self.assertTrue(guards.runtime_errors(record))
   p.write_bytes(old)
   record['output_guard_spec']['protected']={str(q):c.bind(q) for q in [target,resolution]}
 def test_completed_hash_binders_still_used(self):
  record,target,ci,_=self.live('audit')
  with patch.object(c,'regular',wraps=c.regular) as reader:
   c.object_outputs(target.parent.parent,target,True)
   self.assertGreater(reader.call_count,0)
  for name in c.EXPORTS:put(ci/name,b'\n')
  with patch.object(c,'regular',wraps=c.regular) as reader:
   c.outputs(ci,True);self.assertEqual(reader.call_count,4)
 def test_fsize_set_before_receipt_and_matches_launcher_limits(self):
  class HaltLease:
   def check(self):raise BeforeLaunch('fixture stops before admission or child launch')
  class Shared:
   source_commit='synthetic';wrapper_commit='synthetic';fixture=True;lock=None;lease=HaltLease()
   def visible_gate(self,plan):return 4*1024**3 if plan['stage'] in ['audit','replay'] else 3*1024**3
  for number,stage in enumerate(['audit','compile','resolve','replay','audit','compile']):
   evidence=self.root/f'{number}-{stage}'
   with self.assertRaises(BeforeLaunch):runner.run_child({'stage':stage,'argv':['NOT EXECUTED'],'env':{}},self.root,evidence,Shared(),accounting=object())
   r=json.loads((evidence/'receipt.json').read_text());expected=(64 if stage=='audit' else 16)*1024**2
   self.assertEqual(r['memory_policy']['file_size_bytes'],expected);self.assertIsNone(r.get('child_pid'))
   kernel={}
   def setter(key,value):kernel[key]=value
   with patch.object(pilot_child.resource,'setrlimit',side_effect=setter),patch.object(pilot_child.resource,'getrlimit',side_effect=lambda key:kernel[key]):
    limits=pilot_child.configure(stage)
   self.assertEqual(limits['RLIMIT_FSIZE'],[expected,expected])
   self.events.append({'stage':stage,'receipt_fsize':r['memory_policy']['file_size_bytes'],'launcher_readback_fixture':limits['RLIMIT_FSIZE'],'no_child_launched':True})
 def test_chunk_rows_final_partial_and_empty_inputs(self):
  for number,data in enumerate([b'a\nb\nc\n',b'a\nfinal without LF',b'',b'long row that exceeds the target\nlast\n']):
   source=put(self.root/f'source{number}',data);directory=self.root/f'chunks{number}'
   audit.chunk(source,directory,target=3);audit.verify_chunks(directory,source)
 def test_false_row_alignment_flag_cannot_hide_midrow_split(self):
  source=put(self.root/'source',b'alpha\nbeta\n');directory=self.root/'chunks';directory.mkdir()
  payloads=[b'al',b'pha\nbeta\n'];parts=[]
  for i,b in enumerate(payloads):
   name=f'part-{i:04d}.txt';put(directory/name,b);parts.append({'path':name,'bytes':len(b),'sha256':c.sha(b)})
  c.save(directory/'manifest.json',dict(source=str(source),bytes=len(source.read_bytes()),sha256=c.sha(source.read_bytes()),row_aligned=True,target_bytes=100,parts=parts))
  with self.assertRaisesRegex(c.Rejected,'boundary splits'):audit.verify_chunks(directory,source)
 def test_empty_nonfinal_chunk_rejected(self):
  source=put(self.root/'source',b'a\n');directory=self.root/'chunks';directory.mkdir()
  parts=[]
  for i,b in enumerate([b'',b'a\n']):
   name=f'part-{i:04d}.txt';put(directory/name,b);parts.append({'path':name,'bytes':len(b),'sha256':c.sha(b)})
  c.save(directory/'manifest.json',dict(source=str(source),bytes=2,sha256=c.sha(b'a\n'),row_aligned=True,target_bytes=100,parts=parts))
  with self.assertRaisesRegex(c.Rejected,'Empty chunk'):audit.verify_chunks(directory,source)
class Results(unittest.TextTestResult):
 def __init__(self,*a,**k):super().__init__(*a,**k);self.records=[]
 def addSuccess(self,test):super().addSuccess(test);self.records.append({'test':test.id(),'outcome':'pass'})
 def addSubTest(self,test,subtest,err):
  super().addSubTest(test,subtest,err);self.records.append({'test':test.id(),'subcase':str(subtest),'outcome':'pass' if err is None else 'failure'})
if __name__=='__main__':
 with contextlib.ExitStack() as probes:
  for name in ['subprocess.Popen','subprocess.check_output','shutil.disk_usage','pilot_accounting.VisibleAccounting.sample','resource.prlimit']:
   probes.enter_context(patch(name,side_effect=AssertionError('No launch/resource probing in focused fixtures: '+name)))
  result=unittest.TextTestRunner(verbosity=2,resultclass=Results).run(unittest.defaultTestLoader.loadTestsFromTestCase(Delta))
 c.save(RUN/'test-results.json',{'tests':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'records':result.records,'python_only':True,'child_launch_or_resource_probe_authorized':False,'fixture_root':str(RUN)})
 print('PRESERVED_FOCUSED_RUN',RUN)
 raise SystemExit(not result.wasSuccessful())
