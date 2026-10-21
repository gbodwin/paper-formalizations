"""Real finite hooks with filesystem models; no Lean, lease or resource admission."""
from pathlib import Path
from contextlib import ExitStack
import copy,fcntl,json,os,resource,subprocess,sys,tempfile,time,unittest
from unittest.mock import patch
H=Path(__file__).resolve().parent;R=H.parents[1]
D=R/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
sys.path.insert(0,str(D))
import ci_text_fixture as f
import ci_gate,ci_policy
from test_ci_preexec_repair import Fixture,contracts,child_runner,scope
import ci_receipts
SPEC=json.loads((D/'ci-spec.json').read_text())
GOOD=f.MARKER+'\n'+f.RESOLUTION_MARKER+'\n'

class Models(unittest.TestCase):
    def setUp(self):
        self.stack=ExitStack();self.addCleanup(self.stack.close)
        def forbidden(*a,**k):raise AssertionError('Native process/lease/resource/sleep forbidden')
        for obj,names in [(subprocess,['Popen','run','check_output','check_call','call']),
                          (os,['fork','forkpty','posix_spawn','posix_spawnp']),
                          (fcntl,['flock','lockf']),(resource,['setrlimit','prlimit']),
                          (time,['sleep']),(child_runner,['run_child'])]:
            for name in names:
                if hasattr(obj,name):self.stack.enter_context(patch.object(obj,name,side_effect=forbidden))
    def fixture(self):
        obj=Fixture('resolve');self.addCleanup(obj.close);obj.prepare()
        obj.record.update(exit=0)
        obj.ctx.resolution.write_text(json.dumps(dict(target=contracts.TARGET,count=1,
            resolved=[dict(module=contracts.TARGET,object=str(obj.ctx.target))],search_path=list(map(str,obj.roots)))))
        return obj
    def test_exact_source_and_four_stage_schedule(self):
        ci_policy.scope_contract(SPEC);f.validate_sources(R,SPEC)
        plans=ci_policy.plans(R,'/pinned/tool','/fresh/work',SPEC,['/fresh/objects','/ordinary','/tool/lib/lean'],'a'*40)
        self.assertEqual([p['stage'] for p in plans],['compile','resolve','replay','audit'])
        self.assertEqual(plans[1]['argv'][-1],str(R/f.COMPOSITE))
        self.assertEqual(plans[1]['sources'],[str(R/n) for n in [f.COMPOSITE,f.FIXTURE,f.ORIGINAL,SPEC['sources']['source']['path']]])
        self.assertEqual(plans[2]['argv'],['/pinned/tool/bin/leanchecker','-v',ci_policy.TARGET])
        self.assertEqual(plans[2]['env']['LEAN_STACK_SIZE_KB'],'65536')
    def test_wrong_authority_paths_or_original_hashes(self):
        for key in ['resolver','serialization_fixture','original_resolver']:
            bad=copy.deepcopy(SPEC);bad['sources'][key]['path']='other.lean'
            with self.subTest(key=key),self.assertRaises(ValueError):f.contract(bad)
        for key in ['serialization_fixture','original_resolver']:
            bad=copy.deepcopy(SPEC);bad['sources'][key]['sha256']='0'*64
            with self.subTest(key=key),self.assertRaises(ValueError):f.contract(bad)
    def test_changed_composite_and_changed_fixture_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            for rel in [f.FIXTURE,f.ORIGINAL,f.COMPOSITE]:
                p=root/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/rel).read_bytes())
            f.validate_sources(root,SPEC)
            for rel in [f.FIXTURE,f.ORIGINAL,f.COMPOSITE]:
                p=root/rel;original=p.read_bytes();p.write_bytes(original+b'\n-- drift\n')
                with self.subTest(path=rel),self.assertRaises(ValueError):f.validate_sources(root,SPEC)
                p.write_bytes(original)
    def test_log_marker_negative_cases(self):
        for raw in ['',f.RESOLUTION_MARKER+'\n',f.MARKER+'\n',GOOD+f.MARKER+'\n',GOOD+f.RESOLUTION_MARKER+'\n',
                    f.RESOLUTION_MARKER+'\n'+f.MARKER+'\n','prefix '+GOOD,GOOD.replace(f.MARKER,f.MARKER+' trailing'),
                    'error: failure\n'+GOOD,'file.lean:1:2: warning: failure\n'+GOOD]:
            with self.subTest(raw=raw),self.assertRaises(ValueError):f.validate_log(raw)
        for raw in [GOOD,'info: '+f.MARKER+'\nfile.lean:1:2: info: '+f.RESOLUTION_MARKER+'\n']:
            self.assertTrue(f.validate_log(raw)['fixture_before_resolver'])
    def test_live_resolve_requires_marker_before_accepting_stage(self):
        for raw in ['',f.RESOLUTION_MARKER+'\n',f.RESOLUTION_MARKER+'\n'+f.MARKER+'\n',GOOD+f.MARKER+'\n']:
            obj=self.fixture();(obj.ctx.stage_evidence/'raw.log').write_text(raw)
            with self.subTest(raw=raw),self.assertRaises(ValueError):obj.ctx.after_child(obj.plan,obj.record,obj.save)
            self.assertIsNone(obj.ctx.serialization_fixture_result)
            self.assertEqual(len(obj.ctx.seen),1)
    def test_live_success_then_replay_admission(self):
        obj=self.fixture();(obj.ctx.stage_evidence/'raw.log').write_text(GOOD)
        obj.ctx.after_child(obj.plan,obj.record,obj.save)
        self.assertEqual(obj.record['serialization_equivalence_fixture'],f.validate_log(GOOD))
        self.assertEqual(obj.ctx.serialization_fixture_result,f.validate_log(GOOD))
        (obj.evidence/'replay').mkdir()
        obj.ctx.before_child(obj.commands[2],{},obj.save)
    def test_preexec_rejects_each_changed_authority_and_snapshot(self):
        for rel in [f.COMPOSITE,f.FIXTURE,f.ORIGINAL,'submitted_snapshot']:
            obj=self.fixture()
            path=(obj.ctx.stage_evidence/obj.record['submitted_sources'][0]['snapshot']
                  if rel=='submitted_snapshot' else obj.root/rel)
            raw=path.read_bytes();path.write_bytes(b'X'+raw[1:])
            with self.subTest(path=rel),self.assertRaises((ValueError,RuntimeError,OSError)):obj.preexec()
    def test_exit_failure_or_timeout_cannot_enable_replay_or_audit(self):
        for failure in [dict(exit=1),dict(exit=-9,failure='Child wall deadline'),dict(exit=0,failure='cleanup failed'),dict(exit=0,failure='')]:
            obj=self.fixture();obj.record.update(failure);(obj.ctx.stage_evidence/'raw.log').write_text(GOOD)
            obj.ctx.after_child(obj.plan,obj.record,obj.save)
            self.assertIsNone(obj.ctx.serialization_fixture_result)
            for p in obj.commands[2:]:
                with self.subTest(failure=failure,stage=p['stage']),self.assertRaisesRegex(ValueError,'prerequisite'):
                    obj.ctx.before_child(p,{},obj.save)
    def test_inherited_missing_target_and_bad_resolution_still_fail(self):
        for mutation in ['target','resolution']:
            obj=self.fixture();(obj.ctx.stage_evidence/'raw.log').write_text(GOOD)
            if mutation=='target':obj.ctx.target.unlink()
            else:obj.ctx.resolution.write_text('{}')
            with self.subTest(mutation=mutation),self.assertRaises((ValueError,RuntimeError,OSError,KeyError)):
                obj.ctx.after_child(obj.plan,obj.record,obj.save)
            self.assertIsNone(obj.ctx.serialization_fixture_result)
    def test_persisted_prerequisite_rejects_marker_only_or_unsuccessful_receipt(self):
        with tempfile.TemporaryDirectory() as td:
            folder=Path(td);p=folder/'raw.log';p.write_text(GOOD)
            record=dict(state='finished',exit=0,completed_logs={'raw.log':contracts.bind(p)},
                        serialization_equivalence_fixture=f.validate_log(GOOD))
            self.assertEqual(f.receipt_prerequisite('resolve',record,folder),f.validate_log(GOOD))
            for update in [dict(state='failed'),dict(exit=1),dict(exit=-9,failure='timeout'),dict(failure='cleanup'),
                           dict(failure=''),dict(completed_logs={}),dict(completed_logs={'raw.log':dict(bytes=1,sha256='0'*64)}),dict(serialization_equivalence_fixture={})]:
                with self.subTest(update=update),self.assertRaises(ValueError):
                    f.receipt_prerequisite('resolve',dict(record,**update),folder)
            p.write_text(f.RESOLUTION_MARKER+'\n')
            with self.assertRaises(ValueError):f.receipt_prerequisite('resolve',record,folder)
    def test_first_prerequisite_failure_stops_before_replay_and_audit(self):
        for outcome in ['exit1','timeout','missing_marker']:
            called=[]
            def run(plan):
                called.append(plan['stage'])
                if plan['stage']=='resolve':
                    if outcome=='missing_marker':f.validate_log(f.RESOLUTION_MARKER+'\n')
                    raise RuntimeError(outcome)
                return dict(attempt_id='model-only')
            with self.subTest(outcome=outcome),self.assertRaises((ValueError,RuntimeError)):
                ci_gate.execute_four([dict(stage=s) for s in ci_policy.STAGES],run,lambda:self.fail('finish reached'))
            self.assertEqual(called,['compile','resolve'])

if __name__=='__main__':unittest.main(verbosity=2)
