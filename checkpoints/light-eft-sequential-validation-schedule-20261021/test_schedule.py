"""Pure identity/status models with process, admission and resource actions blocked."""
from pathlib import Path
import contextlib,copy,fcntl,importlib.util,json,os,resource,subprocess,sys,tempfile,time,unittest
from unittest.mock import patch
H=Path(__file__).resolve().parent;R=H.parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(H))
import acceptance
from acceptance import aggregate
def policy(name):
    s=importlib.util.spec_from_file_location(name,R/'checkpoints'/name/'ci_policy.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
POLICIES=[policy(n) for n in ['light-eft-canonical-output-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019']]
def env(role='focused',event='push'):
    repo='gbodwin/paper-formalizations';ref='refs/pull/1/merge' if event=='pull_request' else 'refs/heads/integration/light-eft-joint-flag-ci-20261019'
    path='.github/workflows/'+('light-eft-fair-bit-focused.yml' if role=='focused' else 'lean.yml')
    return dict(GITHUB_ACTIONS='true',GITHUB_REPOSITORY=repo,GITHUB_SHA='a'*40,GITHUB_RUN_ID='1',GITHUB_RUN_ATTEMPT='1',
        GITHUB_EVENT_NAME=event,LEAN_NUM_THREADS='1',GITHUB_REF=ref,GITHUB_WORKFLOW='Lean',GITHUB_WORKFLOW_SHA='a'*40,
        GITHUB_WORKFLOW_REF=repo+'/.github/workflows/lean.yml@'+ref,GITHUB_JOB='check',LIGHTEFT_VALIDATION_ROLE=role,
        LIGHTEFT_EXPECTED_SOURCE='a'*40,LIGHTEFT_JOB_WORKFLOW_REPOSITORY=repo,LIGHTEFT_JOB_WORKFLOW_PATH=path,
        LIGHTEFT_JOB_WORKFLOW_SHA='a'*40,LIGHTEFT_JOB_WORKFLOW_REF=repo+'/'+path+'@'+ref)
def forbidden(*a,**k):raise AssertionError('Source-only scheduling models cannot launch/admit/claim')
class Models(unittest.TestCase):
    def setUp(self):
        stack=contextlib.ExitStack();self.addCleanup(stack.close)
        for owner,name in [(subprocess,'Popen'),(fcntl,'flock'),(resource,'setrlimit'),(os,'fork'),(os,'killpg'),(os,'waitid'),(os,'wait4'),(os,'waitpid'),(time,'sleep')]:
            stack.enter_context(patch.object(owner,name,side_effect=forbidden))
    def test_both_policies_same_identity_all_reviewed_events_and_roles(self):
        for role in ['full','focused']:
            for event in ['push','pull_request','workflow_dispatch']:
                e=env(role,event);a,b=[p.ci_identity(e,'a'*40) for p in POLICIES]
                self.assertEqual(a,b);self.assertEqual(a['LIGHTEFT_JOB_WORKFLOW_PATH'],e['LIGHTEFT_JOB_WORKFLOW_PATH'])
                if role=='focused':
                    e['LIGHTEFT_JOB_WORKFLOW_REF']=e['GITHUB_REPOSITORY']+'/'+e['LIGHTEFT_JOB_WORKFLOW_PATH']+'@'+'a'*40
                    for p in POLICIES:p.ci_identity(e,'a'*40)
    def test_every_actual_workflow_field_missing_or_wrong_is_rejected(self):
        for key in ['GITHUB_WORKFLOW','GITHUB_WORKFLOW_SHA','GITHUB_WORKFLOW_REF','GITHUB_JOB','LIGHTEFT_VALIDATION_ROLE',
            'LIGHTEFT_EXPECTED_SOURCE','LIGHTEFT_JOB_WORKFLOW_REPOSITORY','LIGHTEFT_JOB_WORKFLOW_PATH','LIGHTEFT_JOB_WORKFLOW_SHA','LIGHTEFT_JOB_WORKFLOW_REF']:
            for value in ['', 'wrong']:
                for p in POLICIES:
                    e=env();e[key]=value
                    with self.assertRaises(ValueError):p.ci_identity(e,'a'*40)
    def test_cross_role_workflow_and_stale_workflow_sha_rejected(self):
        for p in POLICIES:
            for change in [dict(LIGHTEFT_VALIDATION_ROLE='full'),dict(LIGHTEFT_JOB_WORKFLOW_SHA='b'*40),
                dict(GITHUB_SHA='b'*40),dict(GITHUB_EVENT_NAME='workflow_run'),dict(LEAN_NUM_THREADS='2'),
                dict(GITHUB_REF='refs/heads/light-eft-spanners-checkpoints')]:
                e=env();e.update(change)
                with self.assertRaises(ValueError):p.ci_identity(e,'a'*40)
    def test_aggregation_requires_both_successes(self):
        for full in ['success','failure','cancelled','skipped']:
            for focused in ['success','failure','cancelled','skipped']:
                needs={n:dict(result=s,outputs=dict(validated_commit='a'*40)) for n,s in [('check',full),('focused',focused)]}
                if full==focused=='success':self.assertTrue(aggregate(needs,'a'*40)['accepted'])
                else:
                    with self.assertRaises(ValueError):aggregate(needs,'a'*40)
    def test_missing_or_different_commit_cannot_be_accepted(self):
        good={n:dict(result='success',outputs=dict(validated_commit='a'*40)) for n in ['check','focused']}
        for name in good:
            for value in ['', 'b'*40,None]:
                bad=copy.deepcopy(good);bad[name]['outputs']['validated_commit']=value
                with self.assertRaises(ValueError):aggregate(bad,'a'*40)
            bad=copy.deepcopy(good);bad.pop(name)
            with self.assertRaises(ValueError):aggregate(bad,'a'*40)
            bad=copy.deepcopy(good);bad[name]['outputs']={}
            with self.assertRaises(ValueError):aggregate(bad,'a'*40)
        bad=copy.deepcopy(good);bad['other']=bad['check']
        with self.assertRaises(ValueError):aggregate(bad,'a'*40)
        with self.assertRaises(ValueError):aggregate(good,'not-a-commit')
    def test_real_aggregation_entrypoint_preserves_success_and_rejections(self):
        good={n:dict(result='success',outputs=dict(validated_commit='a'*40)) for n in ['check','focused']}
        cases=[(good,True),({'check':good['check']},False)]
        for name in good:
            for field,value in [('result','failure'),('result','cancelled'),('result','skipped'),('outputs',{'validated_commit':'b'*40})]:
                bad=copy.deepcopy(good);bad[name][field]=value;cases.append((bad,False))
        cases.append(('INVALID JSON',False))
        for needs,ok in cases:
            with tempfile.TemporaryDirectory() as tmp:
                e=env();e.update(GITHUB_JOB='acceptance',RUNNER_TEMP=tmp,LIGHTEFT_NEEDS_JSON=json.dumps(needs) if isinstance(needs,dict) else needs)
                with patch.dict(os.environ,e,clear=True),patch.object(sys,'argv',['acceptance.py','aggregate']),\
                     patch.object(acceptance,'head',return_value='a'*40),patch.object(acceptance,'exact_controls',return_value={'MODEL':'control'}):
                    if ok:acceptance.main()
                    else:
                        with self.assertRaises((ValueError,json.JSONDecodeError)):acceptance.main()
                record=json.loads((Path(tmp)/'light-eft-combined-acceptance-1-1/result.json').read_text())
                self.assertEqual(record['accepted'],ok)
                if not ok:self.assertIn('failure',record)
    def test_real_commit_marker_requires_matching_role_and_exact_identity(self):
        for role in ['full','focused']:
            with tempfile.TemporaryDirectory() as tmp:
                output=Path(tmp)/'outputs';output.write_text('')
                e=env(role);e['GITHUB_OUTPUT']=str(output)
                with patch.dict(os.environ,e,clear=True),patch.object(sys,'argv',['acceptance.py','mark',role]),\
                     patch.object(acceptance,'head',return_value='a'*40),patch.object(acceptance,'exact_controls',return_value={'MODEL':'control'}),patch('builtins.print'):
                    acceptance.main()
                self.assertEqual(output.read_text(),'commit='+'a'*40+'\n')
                output.write_text('');e['LIGHTEFT_JOB_WORKFLOW_SHA']='b'*40
                with patch.dict(os.environ,e,clear=True),patch.object(sys,'argv',['acceptance.py','mark',role]),\
                     patch.object(acceptance,'head',return_value='a'*40),patch.object(acceptance,'exact_controls',return_value={'MODEL':'control'}):
                    with self.assertRaises(ValueError):acceptance.main()
                self.assertEqual(output.read_text(),'')
if __name__=='__main__':unittest.main(verbosity=2)
