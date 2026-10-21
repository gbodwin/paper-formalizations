"""Process-blocked filesystem/telemetry models. No Lean or actual lease/admission."""
from pathlib import Path
import contextlib,copy,fcntl,importlib.util,json,os,resource,subprocess,sys,tempfile,time,types,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
ENGINE=ROOT/'checkpoints/light-eft-canonical-output-adapter-20261020'
sys.dont_write_bytecode=True
sys.path.insert(0,str(ENGINE));sys.path.insert(0,str(HERE));sys.path.insert(0,str(ROOT/'scripts'))
import ci_gate,output_guards,prior_guard,same_run
from finite_contract import CONTRACT
from batch_context import FocusedContext
from contracts import bind,tree,EXPORTS
from ci_inventory import CIInventory

def forbidden(*a,**k):raise AssertionError('Native process/lease/resource action forbidden in source models')
def put(p,b=b'MODEL ONLY; NOT A LEAN OBJECT'):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return p
def accounting():return dict(namespace='model',membership='model',identities=['model'],headroom=8*1024**3,
    system_available=8*1024**3,nodes=[dict(path='/model',limit=str(16*1024**3),current=1,
    memory_stat={'anon':1},oom={'oom':0},pids_max='100',pids_current=1,pids_events={'max':0})])

class Models(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        s=importlib.util.spec_from_file_location('child_runner',ENGINE/'child_runner.py')
        cls.runner=importlib.util.module_from_spec(s);sys.modules['child_runner']=cls.runner;s.loader.exec_module(cls.runner)
    def setUp(self):
        self.block=contextlib.ExitStack();self.addCleanup(self.block.close)
        for owner,name in [(subprocess,'Popen'),(fcntl,'flock'),(resource,'setrlimit'),(os,'killpg'),
            (os,'waitpid'),(os,'waitid'),(os,'wait4'),(os,'fork'),(time,'sleep')]:
            self.block.enter_context(patch.object(owner,name,side_effect=forbidden))
    def fixture(self,index=0):
        t=tempfile.TemporaryDirectory();self.addCleanup(t.cleanup);base=Path(t.name)
        root=base/'light-eft-fair-bit-batch-1-1';work=root/'work';objects=work/'objects'
        (objects/CONTRACT['modules'][0].split('.')[0]).mkdir(parents=True);(work/'resolution').mkdir()
        evidence=root/'runtime';evidence.mkdir();ordinary=base/'ordinary';ordinary.mkdir()
        identity=dict(GITHUB_SHA='a'*40,GITHUB_RUN_ID='1',GITHUB_RUN_ATTEMPT='1',GITHUB_EVENT_NAME='push',GITHUB_JOB='check')
        producers=[base/('light-eft-'+label+'-1-1') for label in ['paid-focused','staged','paid-joint-bridge']]
        for p in producers:(p/'work/objects').mkdir(parents=True);put(p/'result.json');(p/'empty').mkdir()
        spec=json.loads((HERE/'ci-spec.json').read_text());deps={}
        for r in spec['dependencies']:
            dest={'paid':producers[0],'decoder':producers[1],'bridge':producers[2]}.get(r['origin'])
            dest=dest/'work/objects' if dest else ordinary
            p=put(dest/Path(*r['module'].split('.')).with_suffix('.olean'));deps[r['module']]=dict(bind(p),module=r['module'])
        roots=[objects,producers[2]/'work/objects',producers[0]/'work/objects',producers[1]/'work/objects',ordinary]
        plans=ci_gate.build_plans(base/'tool',work,spec,roots,identity['GITHUB_SHA'],bind)
        inv=CIInventory(roots[1:],base/'tool',bind);classified=inv.scan()
        protected={k:v for p in producers for k,v in tree(p).items()};inputs={**classified['semantic'],**protected}
        for p in plans:
            for src in p['sources']:inputs[src]=bind(src)
        lock=put(root/'MODEL-UNLOCKED-FD',b'').open('r+');self.addCleanup(lock.close)
        lease=types.SimpleNamespace(file=lock,path=Path(lock.name),acquired_ns=1,check=lambda:None)
        ctx=FocusedContext(lease,work,evidence,plans,roots,deps,identity,inputs,inv,classified,prior_guard.capture(producers),protected)
        for i,m in enumerate(CONTRACT['modules']):
            case=m.rsplit('.',1)[-1]
            if index>i*4:
                p=put(ctx.target(m));ctx.new[str(p)]=bind(p)
            if index>i*4+1:
                p=put(work/'resolution'/(case+'.json'));ctx.resolved[str(p)]=bind(p)
            if index>=i*4+4:
                for n in EXPORTS:
                    p=put(work/'audit'/case/'ci-evidence'/n);ctx.audit_files[str(p)]=bind(p)
        ctx.seen=plans[:index];p=plans[index]
        if p['stage']=='compile':ctx.target(p['module']).parent.mkdir(parents=True,exist_ok=True)
        folder=evidence/p['case']/p['stage'];folder.mkdir(parents=True)
        st=os.fstat(lock.fileno());record=dict(stage=p['stage'],argv=p['argv'],environment=p['env'],state='created',
            supervisor_pid=os.getpid(),deadline_seconds=90,lock=dict(fd=lock.fileno(),path=lock.name,device=st.st_dev,inode=st.st_ino))
        ctx.before_child(p,record,lambda:None)
        with patch.object(self.runner,'assert_idle'),patch('batch_context.shutil.disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
            ctx.prepare_child(p,record,lambda:None,types.SimpleNamespace(sample=accounting))
        record.update(state='handshake-wait',child_pid=12345,runtime_wall_started_ns=time.monotonic_ns())
        return types.SimpleNamespace(base=base,root=root,work=work,ctx=ctx,plan=p,plans=plans,record=record,producers=producers)
    def sample(self,f,reject=False):
        now=time.monotonic_ns();s=dict(sample_utc='MODEL',sample_started_ns=now,sample_finished_ns=now+1,
            accounting=accounting(),child=dict(pid=12345,start_ticks=1,state='S',rss=1,vm=1,collection_errors=[]),collection_errors=[])
        def assess(c,s,r,b,d):s.update(exit_lifecycle={'terminal_confirmed':False},observed_process_memory=dict(rss=1,vm=1))
        with patch.object(self.runner.exits,'probe',return_value={'terminal':False}),patch.object(self.runner.exits,'assess',side_effect=assess), \
             patch.object(self.runner.telemetry,'collect',return_value=s),patch.object(self.runner,'kill_memory_group') as kill, \
             patch.object(self.runner,'audit_output_errors',wraps=output_guards.runtime_errors) as guard:
            with tempfile.TemporaryFile(mode='w+') as log:
                if reject:
                    with self.assertRaises(self.runner.MemoryGuardError):self.runner.runtime_sample(types.SimpleNamespace(pid=12345),accounting(),None,None,f.record,lambda:None,log)
                    kill.assert_called_once()
                else:self.runner.runtime_sample(types.SimpleNamespace(pid=12345),accounting(),None,None,f.record,lambda:None,log);kill.assert_not_called()
            guard.assert_called_once_with(f.record,preexec=False,terminal=False)
        self.assertNotIn('handshake',f.record)
    def test_real_first_handshake_sample_all_twelve_stages(self):
        for i in range(12):
            with self.subTest(index=i):self.sample(self.fixture(i))
    def test_each_producer_mutation_rejected_live_and_full(self):
        for i in range(3):
            f=self.fixture(8);(f.producers[i]/'result.json').write_bytes(b'CHANGED')
            self.sample(f,True)
            with self.assertRaises(RuntimeError):f.ctx.verify(f.plan)
    def test_prior_tree_extra_missing_symlink_hardlink_directory(self):
        for mode in ['extra','missing','symlink','hardlink','directory']:
            f=self.fixture(4);p=f.producers[2]/'result.json'
            if mode=='extra':put(f.producers[2]/'extra')
            elif mode=='missing':p.unlink()
            elif mode=='directory':(f.producers[2]/'extra-dir').mkdir()
            elif mode=='symlink':p.unlink();p.symlink_to(f.base/'absent')
            else:p.unlink();os.link(put(f.base/'outside'),p)
            self.sample(f,True)
    def test_prior_generated_objects_immutable_through_later_modules(self):
        for index in [4,8]:
            for mutation in ['bytes','remove','companion']:
                f=self.fixture(index);p=f.ctx.target(CONTRACT['modules'][0])
                if mutation=='bytes':p.write_bytes(b'CHANGED')
                elif mutation=='remove':p.unlink()
                else:put(str(p)+'.server')
                self.sample(f,True)
                with self.assertRaises((RuntimeError,OSError)):f.ctx.verify(f.plan)
    def test_missing_current_completed_target_rejected(self):
        for i in [1,2,3,5,6,7,9,10,11]:
            f=self.fixture(i);f.ctx.target(f.plan['module']).unlink();self.sample(f,True)
    def test_early_resolution_audit_prefix_and_temporary_rejected(self):
        for kind in ['resolution','dangling','audit','prefix','temporary','foreign']:
            f=self.fixture(4);m=f.plan['module'];case=f.plan['case'];target=f.ctx.target(m)
            p=f.work/'resolution'/(case+'.json')
            if kind=='resolution':put(p)
            elif kind=='dangling':p.symlink_to(f.base/'absent')
            elif kind=='audit':put(f.work/'audit'/case/'ci-evidence'/EXPORTS[0])
            elif kind=='prefix':put(target.with_suffix('')/'Unexpected.olean')
            elif kind=='temporary':put(str(target)+'.tmp.12345')
            else:put(f.ctx.objects/'LightEFTFairBitStage/Unexpected.olean')
            self.sample(f,True)
    def test_real_preexec_rejects_mutated_first_module(self):
        f=self.fixture(8);f.ctx.target(CONTRACT['modules'][0]).write_bytes(b'CHANGED')
        with patch('batch_context.shutil.disk_usage',return_value=types.SimpleNamespace(free=3*1024**3)):
            with self.assertRaises((RuntimeError,ValueError)):f.ctx.preexec(f.plan,f.record,lambda:None)
    def test_exact_per_module_sets_and_sources(self):
        s=json.loads((HERE/'ci-spec.json').read_text());ci_gate.finite_scope(s)
        for module in CONTRACT['modules']:
            bad=copy.deepcopy(CONTRACT['imports']);bad[module]=bad[module][1:]
            with patch.dict(CONTRACT,{'imports':bad}):
                with self.assertRaises(ValueError):ci_gate.finite_scope(s)
        bad=copy.deepcopy(s);bad['sources'][0]['sha256']='0'*64
        with self.assertRaises(ValueError):ci_gate.finite_scope(bad)
    def test_schedule_stops_first_failure(self):
        f=self.fixture();seen=[]
        def child(p):
            seen.append(p)
            if len(seen)==6:raise ValueError('MODEL FIRST FAILURE')
            return {'attempt_id':str(len(seen))}
        with self.assertRaises(ValueError):ci_gate.execute_sequence(f.plans,child,lambda:self.fail('finish after failure'))
        self.assertEqual(len(seen),6)
        with self.assertRaises(ValueError):ci_gate.execute_sequence(f.plans[::-1],lambda p:self.fail('bad schedule ran'),lambda:None)
    def test_only_module_mode_and_exact_three_prior_roots(self):
        f=self.fixture();s=f.ctx.spec(f.plan);r=dict(stage=f.plan['stage'],argv=f.plan['argv'],working_directory=f.plan['cwd'],focused_module=f.plan['module'],CI_identity=f.ctx.identity)
        for mode in ['fixtures','admission']:
            bad=copy.deepcopy(s);bad['focused']['mode']=mode
            with self.assertRaises(RuntimeError):output_guards.focused_contract(r,bad)
        bad=copy.deepcopy(s);bad['prior_trees'].pop(next(iter(bad['prior_trees'])))
        with self.assertRaises(RuntimeError):output_guards.focused_contract(r,bad)
    def test_known_runner_configuration_bound_and_replay_settings(self):
        s=json.loads((HERE/'ci-spec.json').read_text())
        repo=Path('/home/runner/work/paper-formalizations/paper-formalizations')
        tool=Path('/home/runner/.elan/toolchains/leanprover--lean4---v4.34.0')
        temp=Path('/home/runner/work/_temp');suffix='39507492456-1'
        work=temp/('light-eft-fair-bit-batch-'+suffix)/'work'
        roots=[work/'objects',*[temp/(prefix+suffix)/'work/objects' for prefix in
            ['light-eft-paid-joint-bridge-','light-eft-paid-focused-','light-eft-staged-']],
            repo/'.lake/build/lib/lean',*[repo/'.lake/packages'/n/'.lake/build/lib/lean' for n in s['pins']],tool/'lib/lean']
        with patch.object(ci_gate,'ROOT',repo):
            plans=ci_gate.build_plans(tool,work,s,roots,'a'*40,lambda p:dict(path=str(p),synthetic_model=True))
        self.assertEqual(len(plans),12)
        for p in plans:
            self.assertLessEqual(len(json.dumps(dict(argv=p['argv'],env=p['env'],stage=p['stage'])).encode()),4096)
            self.assertEqual(p['env']['LEAN_NUM_THREADS'],'1')
            self.assertEqual(p['env']['MIMALLOC_ARENA_RESERVE'],'128MiB')
            if p['stage']=='replay':
                self.assertEqual(p['argv'][1:],['-v',p['module']])
                self.assertEqual(p['env']['LEAN_STACK_SIZE_KB'],'65536')
                self.assertNotIn('MIMALLOC_VERBOSE',p['env'])
    def test_retained_context_not_normalized(self):
        f=self.fixture();rows=f.ctx.classified['semantic'];normal=[f.base/'ordinary']
        original={p:r for p,r in rows.items() if Path(p).is_relative_to(normal[0])}
        old={'prior_bindings':original,'retained_roots':list(map(str,normal))}
        same_run.retained_context(old,normal,rows,f.ctx.inputs)
        p=put(normal[0]/'Unexpected.olean');fresh={**rows,str(p):bind(p)}
        with self.assertRaises(RuntimeError):same_run.retained_context(old,normal,fresh,{**f.ctx.inputs,str(p):bind(p)})

if __name__=='__main__':unittest.main(verbosity=2)
