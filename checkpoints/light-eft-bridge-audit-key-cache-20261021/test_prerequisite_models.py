"""Real bridge hooks/receipt reconstruction with blocked native/resource APIs."""
from pathlib import Path
import copy,fcntl,json,os,resource,subprocess,sys,tempfile,time,types,unittest
from unittest.mock import Mock,patch
H=Path(__file__).resolve().parent;R=H.parents[1];B=R/'checkpoints/light-eft-paid-joint-bridge-ci-adapter-20261020'
sys.path.insert(0,str(B))
import test_bridge_contract as old
import ci_gate,bridge_fixture as f
from contracts import bind
GOOD=f.MARKER+'\n'+f.RESOLUTION_MARKER+'\n'
SPEC=json.loads((B/'ci-spec.json').read_text())

class Models(unittest.TestCase):
    fixture=old.Models.fixture;prepare=old.Models.prepare;first_sample=old.Models.first_sample
    @classmethod
    def setUpClass(cls):old.Models.setUpClass.__func__(cls)
    def setUp(self):
        old.Models.setUp(self)
        def forbidden(*a,**k):raise AssertionError('Native process/lease/resource/sleep forbidden')
        for owner,names in [(subprocess,['run','check_output','check_call','call']),
                            (os,['forkpty','posix_spawn','posix_spawnp']),(fcntl,['lockf']),(resource,['prlimit'])]:
            for name in names:
                if hasattr(owner,name):self.block.enter_context(patch.object(owner,name,side_effect=forbidden))
    def resolution(self,obj,raw=GOOD):
        p=obj.plan;folder=obj.ctx.evidence/p['case']/p['stage'];(folder/'raw.log').write_text(raw)
        (obj.work/'resolution'/(p['case']+'.json')).write_text(json.dumps(dict(target=p['module'],count=1,
            resolved=[dict(module=p['module'],object=str(obj.ctx.target(p['module'])))],search_path=list(map(str,obj.ctx.roots)))))
        obj.record['exit']=0
    def test_exact_native_helper_sources_and_unchanged_four_children(self):
        f.validate_sources(R,SPEC);obj=self.fixture();ci_gate.finite_scope(SPEC)
        self.assertEqual([p['stage'] for p in obj.plans],['compile','resolve','replay','audit'])
        proof=next(x['path'] for x in SPEC['sources'] if x['role']=='bridge')
        self.assertEqual(obj.plans[1]['sources'],[str(R/path) for path in [f.COMPOSITE,f.FIXTURE,f.ORIGINAL,proof]])
        self.assertEqual(obj.plans[1]['argv'][-1],str(R/f.COMPOSITE))
        self.assertEqual(obj.plans[2]['env']['LEAN_STACK_SIZE_KB'],'65536')
    def test_wrong_hash_path_duplicate_roles_and_composite_drift_reject(self):
        for role in ['resolver','key_fixture','original_resolver']:
            for key,value in [('path','other.lean'),('sha256','0'*64)]:
                bad=copy.deepcopy(SPEC);next(r for r in bad['sources'] if r['role']==role)[key]=value
                with self.subTest(role=role,key=key),self.assertRaises(ValueError):f.contract(bad)
        bad=copy.deepcopy(SPEC);bad['sources'].append(dict(bad['sources'][-1]))
        with self.assertRaises(ValueError):f.contract(bad)
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            for path in [f.FIXTURE,f.ORIGINAL,f.COMPOSITE]:
                p=root/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/path).read_bytes())
            f.validate_sources(root,SPEC)
            for path in [f.FIXTURE,f.ORIGINAL,f.COMPOSITE]:
                p=root/path;raw=p.read_bytes();p.write_bytes(raw+b'\n-- drift\n')
                with self.subTest(path=path),self.assertRaises(ValueError):f.validate_sources(root,SPEC)
                p.write_bytes(raw)
    def test_negative_marker_order_duplicates_substrings_and_Lean_errors(self):
        for raw in ['',f.RESOLUTION_MARKER+'\n',f.MARKER+'\n',GOOD+f.MARKER+'\n',GOOD+f.RESOLUTION_MARKER+'\n',
                    f.RESOLUTION_MARKER+'\n'+f.MARKER+'\n','prefix '+GOOD,GOOD.replace(f.MARKER,f.MARKER+' trailing'),
                    'error: failure\n'+GOOD,'x.lean:1:2: warning: failure\n'+GOOD,
                    GOOD.replace(f.MARKER,'PASS: pure name-text serialization differential fixtures')]:
            with self.subTest(raw=raw),self.assertRaises(ValueError):f.validate_log(raw)
        for raw in [GOOD,'info: '+f.MARKER+'\nx.lean:1:2: info: '+f.RESOLUTION_MARKER+'\n']:
            self.assertTrue(f.validate_log(raw)['fixture_before_resolver'])
    def test_live_resolve_success_enables_only_existing_replay_then_audit(self):
        obj=self.fixture(1);self.first_sample(obj);self.resolution(obj)
        obj.ctx.after_child(obj.plan,obj.record,lambda:None)
        self.assertEqual(obj.ctx.bridge_fixture_result,f.validate_log(GOOD))
        self.assertEqual(obj.record['bridge_key_equivalence_fixture'],f.validate_log(GOOD))
        obj.plan=obj.plans[2];self.prepare(obj);self.first_sample(obj)
    def test_live_missing_or_reordered_markers_never_enable_later_children(self):
        for raw in ['',f.RESOLUTION_MARKER+'\n',f.RESOLUTION_MARKER+'\n'+f.MARKER+'\n',GOOD+f.MARKER+'\n']:
            obj=self.fixture(1);self.resolution(obj,raw)
            with self.subTest(raw=raw),self.assertRaises(ValueError):obj.ctx.after_child(obj.plan,obj.record,lambda:None)
            self.assertIsNone(obj.ctx.bridge_fixture_result)
            for index in [2,3]:
                obj.ctx.seen=obj.plans[:index]
                with self.assertRaisesRegex(RuntimeError,'fixture prerequisite'):obj.ctx.before_child(obj.plans[index],{},lambda:None)
    def test_failed_or_timed_out_resolve_does_not_qualify(self):
        for update in [dict(exit=1),dict(exit=-9,failure='Child wall deadline'),dict(exit=0,failure='cleanup failed'),dict(exit=0,failure='')]:
            obj=self.fixture(1);self.resolution(obj);obj.record.update(update)
            obj.ctx.after_child(obj.plan,obj.record,lambda:None)
            self.assertIsNone(obj.ctx.bridge_fixture_result)
    def test_existing_resolution_object_and_preservation_checks_remain_mandatory(self):
        for mutation in ['object','resolution','prior']:
            obj=self.fixture(1);self.resolution(obj)
            if mutation=='object':obj.ctx.target(obj.plan['module']).unlink()
            elif mutation=='resolution':(obj.work/'resolution'/(obj.plan['case']+'.json')).write_text('{}')
            else:(obj.producers[0]/'result.json').write_text('CHANGED')
            with self.subTest(mutation=mutation),self.assertRaises((RuntimeError,ValueError,KeyError,OSError)):obj.ctx.after_child(obj.plan,obj.record,lambda:None)
            self.assertIsNone(obj.ctx.bridge_fixture_result)
    def test_submitted_fixture_snapshot_is_critical_preexec_input(self):
        obj=self.fixture(1);row=next(r for r in obj.record['submitted_sources'] if r['path']==str(R/f.FIXTURE))
        snapshot=obj.ctx.evidence/obj.plan['case']/'resolve'/row['snapshot'];snapshot.write_bytes(snapshot.read_bytes()+b'changed')
        with self.assertRaises((RuntimeError,ValueError)):obj.ctx.preexec(obj.plan,obj.record,lambda:None)
    def test_persisted_prerequisite_hash_state_exit_and_record_negatives(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'raw.log';p.write_text(GOOD)
            record=dict(state='finished',exit=0,completed_logs={'raw.log':bind(p)},bridge_key_equivalence_fixture=f.validate_log(GOOD))
            self.assertEqual(f.receipt_prerequisite('resolve',record,root),f.validate_log(GOOD))
            for change in [dict(state='failed'),dict(exit=1),dict(exit=-9,failure='timeout'),dict(failure=''),dict(completed_logs={}),dict(bridge_key_equivalence_fixture={})]:
                with self.subTest(change=change),self.assertRaises(ValueError):f.receipt_prerequisite('resolve',dict(record,**change),root)
            p.write_text(f.RESOLUTION_MARKER+'\n')
            with self.assertRaises(ValueError):f.receipt_prerequisite('resolve',record,root)
    def test_batch_style_bound_policy_reconstruction_rechecks_fixture_after_generic_receipts(self):
        # This is the same pure module_at loader and verify_schedule call used
        # by the unchanged batch same-run bridge handoff; no kernel checks mocked
        # here are reported as native receipt acceptance.
        policy=old.same_run.module_at(B/'ci_gate.py','_test_bound_bridge_policy')
        for mutation in ['none','missing','result-only','stale-hash','failed-resolve','generic-failure']:
            obj=self.fixture();case=obj.plans[0]['case'];lease=dict(acquired_ns=101,state='released',kernel_echild=True)
            handoff=dict(prior_attempt_ids=['prior-%d'%i for i in range(13)],last_release_ns=100)
            for i,plan in enumerate(obj.plans):
                folder=obj.ctx.evidence/case/plan['stage'];folder.mkdir(parents=True,exist_ok=True)
                rec=dict(CI_identity=obj.identity,workflow_job='check',focused_module=plan['module'],focused_case=case,
                    attempt_id='new-%d'%i,started_ns=110+i*10,ended_ns=115+i*10)
                if i==1:
                    p=folder/'raw.log';p.write_text(GOOD)
                    rec.update(state='finished',exit=0,completed_logs={'raw.log':bind(p)},bridge_key_equivalence_fixture=f.validate_log(GOOD))
                    if mutation=='missing':p.write_text(f.RESOLUTION_MARKER+'\n');rec['completed_logs']={'raw.log':bind(p)}
                    elif mutation=='result-only':rec['completed_logs']={}
                    elif mutation=='stale-hash':p.write_text(GOOD+'changed')
                    elif mutation=='failed-resolve':rec['exit']=1
                (folder/'receipt.json').write_text(json.dumps(rec))
            generic=Mock(side_effect=ValueError('generic preservation failure') if mutation=='generic-failure' else None)
            if mutation=='none':policy.verify_schedule(obj.plans,obj.ctx.evidence,lease,obj.ctx.base_dependencies,handoff,obj.identity,generic)
            else:
                with self.subTest(mutation=mutation),self.assertRaises(ValueError):policy.verify_schedule(obj.plans,obj.ctx.evidence,lease,obj.ctx.base_dependencies,handoff,obj.identity,generic)
            generic.assert_called_once()

if __name__=='__main__':unittest.main(verbosity=2)
