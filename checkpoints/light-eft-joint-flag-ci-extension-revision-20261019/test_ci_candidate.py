"""Synthetic/static tests only. Every real launch/lock/resource probe is forbidden."""
from pathlib import Path
import ast, contextlib, copy, csv, datetime, fcntl, hashlib, json, os, resource, shutil, subprocess, sys, tempfile, types, unittest, uuid
from unittest.mock import patch
import ci_gate as gate
import ci_policy as p
from ci_accounting import normalize
from ci_inventory import CIInventory

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SPEC=json.loads((HERE/'ci-spec.json').read_text())
RUN=HERE/'test-evidence'/uuid.uuid4().hex;RUN.mkdir(parents=True,exist_ok=False)
SNAPSHOTS=RUN/'python-sources';SNAPSHOTS.mkdir()
for f in HERE.glob('*.py'):(SNAPSHOTS/(f.name+'.txt')).write_bytes(f.read_bytes())

def forbid(*a,**k):raise AssertionError('Real compiler/process/lock/resource API forbidden in synthetic tests')
def put(path,data=b'synthetic; not a Lean object'):
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);return path
def bind(path):
    path=Path(path);s=path.stat();b=path.read_bytes()
    return dict(path=str(path),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),identity=[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns])

class Candidate(unittest.TestCase):
    def setUp(self):
        self.root=RUN/self._testMethodName;self.root.mkdir()
        self.now=datetime.datetime(2026,10,19,0,0,0,tzinfo=datetime.timezone.utc)
        self.env=dict(GITHUB_ACTIONS='true',GITHUB_REPOSITORY='gbodwin/paper-formalizations',GITHUB_SHA='a'*40,
            GITHUB_RUN_ID='123',GITHUB_RUN_ATTEMPT='1',GITHUB_EVENT_NAME='workflow_dispatch',GITHUB_REF='refs/heads/reviewed-ci',
            GITHUB_WORKFLOW='Lean',GITHUB_WORKFLOW_SHA='a'*40,GITHUB_ACTOR='synthetic-operator',LEAN_NUM_THREADS='1')
        self.identity=p.ci_identity(self.env,'a'*40)


    def test_ci_identity_binds_commit_event_run_and_rejects_ignored_branch(self):
        for key,value in [('GITHUB_ACTIONS','false'),('GITHUB_REPOSITORY','other/repo'),('GITHUB_SHA','b'*40),('GITHUB_RUN_ID','../x'),
            ('GITHUB_RUN_ATTEMPT','0'),('GITHUB_EVENT_NAME','repository_dispatch'),('LEAN_NUM_THREADS','2'),('GITHUB_REF','refs/heads/light-eft-spanners-checkpoints')]:
            e=self.env.copy();e[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):p.ci_identity(e,'a'*40)





    def test_exact_scope_roots_interfaces_helper_and_resource_gates(self):
        p.scope_contract(SPEC)
        for key,value in [('dependencies',SPEC['dependencies'][:-1]),('project_imports',77),('required_public_roots',15),('required_interfaces',7),
            ('private_identity_helper_required',False),('resource_gates_GiB',[3,3,3,3]),('toolchain','other')]:
            bad=copy.deepcopy(SPEC);bad[key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):p.scope_contract(bad)
        bad=copy.deepcopy(SPEC);bad['dependencies'][0]['module']='OtherPaper.X'
        with self.assertRaises(ValueError):p.scope_contract(bad)

    def test_exact_files_rejects_mutation_git_mismatch_symlink_and_unsafe_path(self):
        f=put(self.root/'source.lean',b'synthetic source, not compiled')
        row=dict(path='source.lean',bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest())
        spec=dict(sources={'source':row},dependencies=[],engine_files=[])
        with patch.object(gate,'ROOT',self.root),patch.object(gate.subprocess,'check_output',return_value=f.read_bytes()):
            gate.exact_files(spec)
            for change in ['hash','Git','unsafe','symlink']:
                bad=copy.deepcopy(spec)
                if change=='hash':bad['sources']['source']['sha256']='0'*64
                if change=='unsafe':bad['sources']['source']['path']='../source.lean'
                if change=='symlink':
                    (self.root/'link.lean').symlink_to(f);bad['sources']['source']['path']='link.lean'
                if change=='Git':
                    with patch.object(gate.subprocess,'check_output',return_value=b'different'),self.assertRaises(ValueError):gate.exact_files(bad)
                else:
                    with self.subTest(change=change),self.assertRaises(ValueError):gate.exact_files(bad)


    def test_four_plans_exact_order_options_roles_environment_and_cwd(self):
        roots=[self.root/'work/objects',self.root/'deps',self.root/'tool/lib/lean'];work=self.root/'work'
        plans=p.plans(self.root,self.root/'tool',work,SPEC,roots,'a'*40)
        self.assertEqual([r['stage'] for r in plans],list(p.STAGES));self.assertEqual([len(r['sources']) for r in plans],[1,2,1,2])
        for r in plans:
            self.assertEqual(r['env']['LIGHTEFT_SOURCE_COMMIT'],'a'*40);self.assertEqual(r['env']['LIGHTEFT_HARNESS_COMMIT'],'a'*40)
            self.assertEqual(r['env']['LEAN_PATH'],':'.join(map(str,roots)))
            self.assertEqual(r['cwd'],str(work/'audit' if r['stage']=='audit' else work))
            if r['stage']!='replay':self.assertEqual(r['argv'][1:6],p.FLAGS)
        self.assertEqual(plans[2]['argv'],[str(self.root/'tool/bin/leanchecker'),'-v',p.TARGET])
        self.assertNotIn('MIMALLOC_VERBOSE',plans[2]['env'])

    def test_first_failure_at_each_stage_stops_all_following_stages(self):
        for failing in range(4):
            calls=[]
            def child(plan):
                calls.append(plan['stage'])
                if len(calls)-1==failing:raise ValueError('synthetic failure')
                return {'attempt_id':str(len(calls))}
            with self.subTest(failing=failing),self.assertRaises(ValueError):gate.execute_four([{'stage':s} for s in p.STAGES],child,forbid)
            self.assertEqual(calls,list(p.STAGES[:failing+1]))

    def test_success_is_strictly_sequential_then_finish(self):
        events=[]
        def child(plan):events.append(plan['stage']);return {'attempt_id':str(len(events))}
        def finish():events.append('finish');return {'synthetic':True}
        gate.execute_four([{'stage':s} for s in p.STAGES],child,finish)
        self.assertEqual(events,[*p.STAGES,'finish'])

    def test_private_helper_actual_owner_identity_is_not_assumed(self):
        r=dict(name='_private.Generated.27.LightEFTSpanners.JointFlagSampling.retainInstanceArguments',owner=p.TARGET,kind='theorem',unsafe='false',partial='false')
        self.assertEqual(p.private_helper([r]),r['name'])
        for bad in [[],[r,r],[dict(r,owner='Other')],[dict(r,kind='axiom')],[dict(r,unsafe='true')],[dict(r,name=r['name'].replace('_private.','public.'))]]:
            with self.subTest(bad=bad),self.assertRaises(ValueError):p.private_helper(bad)

    def audit_fixture(self,omit_root=None,omit_interface=None,omit_helper=False,omit_generated_inventory=False):
        engine=ROOT/SPEC['engine_directory'];sys.path.insert(0,str(engine))
        import focused_audit, probability_plan
        names=[r['module'] for r in SPEC['dependencies']]
        required=list(probability_plan.REQUIRED_ROOTS)
        interfaces=[n for n in probability_plan.REQUIRED_INTERFACES if n!=omit_interface]
        helper='_private.Generated.13.LightEFTSpanners.JointFlagSampling.retainInstanceArguments'
        generated='_private.Generated.14.LightEFTSpanners.JointFlagSampling.extra_generated'
        roots=[n for n in required if n!=omit_root]+([] if omit_helper else [helper])+[generated]
        ci=self.root/('audit-'+str(len(list(self.root.iterdir()))));ci.mkdir()
        inv=[dict(owner=p.TARGET,name=n,kind='theorem',unsafe='false',partial='false') for n in roots]
        if omit_generated_inventory:inv=[r for r in inv if r['name']!=generated]
        dep=[]
        for n in roots:
            dep.append(dict(name=n,owner=p.TARGET,kind='theorem',typeDependencies=','.join(interfaces+['propext']),bodyDependencies=helper if not omit_helper and n!=helper else '',unsafe='false',partial='false'))
        for n in interfaces:dep.append(dict(name=n,owner=names[0],kind='theorem',typeDependencies='propext',bodyDependencies='',unsafe='false',partial='false'))
        dep.append(dict(name='propext',owner='[anonymous]',kind='axiom',typeDependencies='',bodyDependencies='',unsafe='false',partial='false'))
        def table(file,rows,fields):
            with (ci/file).open('w',newline='') as f:
                w=csv.DictWriter(f,fieldnames=fields,delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(rows)
        table('actual-owner-inventory.tsv',inv,['owner','name','kind','unsafe','partial'])
        table('recursive-dependencies.tsv',dep,['name','owner','kind','typeDependencies','bodyDependencies','unsafe','partial'])
        (ci/'import-closure-loaded.txt').write_text('\n'.join(names+[p.TARGET])+'\n');(ci/'strict-violations.txt').write_text('\n')
        raw=f'PASS: {len(inv)} new-module actual-owner declarations; {len(dep)} recursive constants, 0 opaque bodies; axioms [propext]\n'
        return focused_audit,ci,names,raw,inv

    def test_full_owner_audit_and_private_helper_gate_compose(self):
        audit,ci,names,raw,inv=self.audit_fixture()
        result=audit.validate(ci,names,raw);self.assertEqual(result['new_owner_roots'],18);p.private_helper(inv)
        audit,ci,names,raw,inv=self.audit_fixture(omit_helper=True)
        audit.validate(ci,names,raw)  # counts/reachability are self-consistent
        with self.assertRaises(ValueError):p.private_helper(inv)

    def test_each_required_public_root_and_interface_remains_mandatory(self):
        sys.path.insert(0,str(ROOT/SPEC['engine_directory']));import probability_plan
        for name in probability_plan.REQUIRED_ROOTS:
            audit,ci,names,raw,_=self.audit_fixture(omit_root=name)
            with self.subTest(root=name),self.assertRaises(Exception):audit.validate(ci,names,raw)
        for name in probability_plan.REQUIRED_INTERFACES:
            audit,ci,names,raw,_=self.audit_fixture(omit_interface=name)
            with self.subTest(interface=name),self.assertRaisesRegex(Exception,'Missing required reachable interface'):audit.validate(ci,names,raw)

    def test_additional_generated_owner_cannot_be_omitted(self):
        audit,ci,names,raw,_=self.audit_fixture(omit_generated_inventory=True)
        with self.assertRaisesRegex(Exception,'Omitted new-module private/generated root'):audit.validate(ci,names,raw)

    def accounting(self):
        row=dict(path='/synthetic/group',limit=str(8*1024**3),current=1024**3,memory_stat={'anon':1,'file':2,'kernel':3},oom={'oom':0,'oom_kill':0,'oom_group_kill':0},pids_max='100',pids_current=2)
        snap=dict(initial_namespace_verified=True,ancestors=[dict(directory=row['path'],max=row['limit'],current=0)],system_available=9*1024**3,namespace_inode=123,membership='/group',mountinfo_raw='synthetic')
        return snap,[row],[{'directory':[7,8]}]

    def test_full_hierarchy_current_observation_and_explicit_unlimited(self):
        s,r,i=self.accounting();value=normalize(s,r,i)
        self.assertEqual(value['headroom'],7*1024**3)
        s['ancestors']=[];value=normalize(s,[],[])
        self.assertEqual(value['headroom'],s['system_available']);self.assertTrue(value['explicit_unlimited'])

    def test_unknown_hidden_partial_and_corrupt_accounting_refuse(self):
        for change in ['namespace','discovery','missing-row','duplicate','negative-current','negative-stat','missing-oom','zero-limit','host']:
            s,r,i=self.accounting()
            if change=='namespace':s['initial_namespace_verified']=False
            if change=='discovery':s['discovery_error']='hidden limits'
            if change=='missing-row':r=[]
            if change=='duplicate':r=r+r;s['ancestors']*=2;i*=2
            if change=='negative-current':r[0]['current']=-1
            if change=='negative-stat':r[0]['memory_stat']['anon']=-1
            if change=='missing-oom':r[0]['oom'].pop('oom')
            if change=='zero-limit':r[0]['limit']='0';s['ancestors'][0]['max']='0'
            if change=='host':s['system_available']=-1
            with self.subTest(change=change),self.assertRaises((ValueError,KeyError)):normalize(s,r,i)

    def test_fresh_inventory_binds_objects_signatures_and_metadata_without_history_claim(self):
        root=self.root/'search';put(root/'M.olean');put(root/'M.ir');put(root/'M.ir.sig');put(root/'M.trace')
        inv=CIInventory([root],self.root/'tool',bind);v=inv.scan();self.assertEqual(len(v['semantic']),3);self.assertEqual(len(v['excluded']),1);inv.scan()
        (root/'M.ir.sig').write_bytes(b'mutated')
        with self.assertRaisesRegex(ValueError,'changed'):inv.scan()

    def test_unknown_orphan_sidecar_duplicate_root_and_link_refuse(self):
        for change in ['unknown','orphan','signature','symlink','hardlink','duplicate']:
            root=self.root/change;root.mkdir();m=put(root/'M.olean')
            if change=='unknown':put(root/'extra.so')
            if change=='orphan':put(root/'Missing.olean.hash')
            if change=='signature':put(root/'M.ir.sig')
            if change=='symlink':(root/'linked.olean').symlink_to(m)
            if change=='hardlink':os.link(m,root/'linked.olean')
            with self.subTest(change=change),self.assertRaises(ValueError):CIInventory([root,root] if change=='duplicate' else [root],self.root/'tool',bind).scan()

    def runtime_fixture(self):
        base=self.root/str(len(list(self.root.iterdir())))
        tool=base/'tool';lib=tool/'lib/lean';deps=base/'deps'
        for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.trace']:
            put(lib/('Init'+suffix))
        put(lib/'libInit.a');put(deps/'Dependency.olean')
        names=['libInit_shared.so','libLake_shared.so','libleanshared.so','libleanshared_1.so','libleanshared_2.so']
        runtime=[put(lib/n,('synthetic runtime '+n).encode()) for n in names]
        return CIInventory([deps,lib],tool,bind),runtime,deps

    def test_toolchain_layout_hashes_and_identity_binds_all_five_runtime_libraries(self):
        inv,runtime,_=self.runtime_fixture();value=inv.scan()
        for f in runtime:
            self.assertEqual(value['semantic'][str(f)],bind(f))
            self.assertNotIn(str(f),value['excluded'])
            self.assertIn(str(f),value['members'][str(f.parent)])
        self.assertEqual(len(value['semantic']),12);self.assertEqual(len(value['excluded']),2)
        self.assertEqual(inv.scan(),value)

    def test_missing_each_shared_runtime_library_refuses_initial_inventory(self):
        for index in range(5):
            inv,runtime,_=self.runtime_fixture();runtime[index].unlink()
            with self.subTest(index=index),self.assertRaisesRegex(ValueError,'Missing CI toolchain shared runtime'):inv.scan()

    def test_each_shared_runtime_content_mutation_refuses_revalidation(self):
        for index in range(5):
            inv,runtime,_=self.runtime_fixture();inv.scan();f=runtime[index]
            f.write_bytes(b'x'*f.stat().st_size)
            with self.subTest(index=index),self.assertRaisesRegex(ValueError,'changed'):inv.scan()

    def test_each_shared_runtime_identity_replacement_refuses_revalidation(self):
        for index in range(5):
            inv,runtime,_=self.runtime_fixture();inv.scan();f=runtime[index];old=bind(f)
            f.rename(self.root/('held-inode-'+str(index)));put(f,('synthetic runtime '+f.name).encode())
            self.assertEqual(bind(f)['sha256'],old['sha256']);self.assertNotEqual(bind(f)['identity'],old['identity'])
            with self.subTest(index=index),self.assertRaisesRegex(ValueError,'changed'):inv.scan()

    def test_each_shared_runtime_removal_refuses_revalidation(self):
        for index in range(5):
            inv,runtime,_=self.runtime_fixture();inv.scan();runtime[index].unlink()
            with self.subTest(index=index),self.assertRaisesRegex(ValueError,'Missing CI toolchain shared runtime'):inv.scan()

    def test_extra_or_misplaced_shared_libraries_refuse_before_and_after_binding(self):
        for name in ['libUnexpected.so','libInit_shared.so','libLake_shared.so','libleanshared.so','libleanshared_1.so','libleanshared_2.so']:
            for location in ['tool-root','nested-tool','dependency']:
                if location=='tool-root' and name!='libUnexpected.so':continue
                for bound in [False,True]:
                    inv,runtime,deps=self.runtime_fixture()
                    if bound:inv.scan()
                    parent={'tool-root':runtime[0].parent,'nested-tool':runtime[0].parent/'nested','dependency':deps}[location]
                    put(parent/name)
                    with self.subTest(name=name,location=location,bound=bound),self.assertRaisesRegex(ValueError,'Unknown CI search input'):inv.scan()

    def test_existing_workflow_steps_triggers_permissions_and_group_are_retained(self):
        old=(HERE/'original-lean-workflow.txt').read_text();new=(ROOT/'.github/workflows/lean.yml').read_text()
        env="    # Bounded pinned-source review: trusted Lake/compiler paths serialize\n    # with one task worker. Not a semaphore for arbitrary future custom tasks.\n    env:\n      LEAN_NUM_THREADS: '1'\n"
        self.assertEqual(new.count(env),1)
        stripped=new.replace(env,'',1)
        stripped=stripped[:stripped.index('      - name: Verify exact staged joint-flag source sequentially')]
        self.assertEqual(stripped,old)
        self.assertNotIn('light_eft_handoff',new);self.assertNotIn('ci_gate.py preflight',new)
        self.assertNotIn('lake build -j1',new);self.assertNotIn('matrix:',new)
        self.assertIn('if: always()',new)

    def summary_script(self):
        workflow=(ROOT/'.github/workflows/lean.yml').read_text()
        summary=workflow.split('      - name: Record workflow outcome independently of staged gate\n',1)[1]
        body=summary.split("          python3 -B - <<'PY'\n",1)[1].split('\n          PY\n',1)[0]
        return '\n'.join(line[10:] for line in body.splitlines())+'\n'

    def test_import_index_is_exact_reviewed_429_line_sorted_permutation(self):
        data=(ROOT/'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners.lean').read_bytes()
        lines=data.decode().splitlines(True)
        self.assertEqual(len(lines),429);self.assertEqual(len(set(lines)),429)
        self.assertTrue(all(line.startswith('import LightEFTSpanners.') for line in lines))
        self.assertEqual(lines,sorted(lines));self.assertEqual(len(data),20221)
        self.assertEqual(hashlib.sha256(data).hexdigest(),'c6ef5ff64cc9b6b4b3f4e8e8227490caa5fbb878c945cfa4bafe81d57c0be610')

    def test_workflow_summary_records_exact_identity_and_each_staged_outcome(self):
        for outcome in ['success','failure','cancelled','skipped']:
            directory=self.root/outcome;directory.mkdir()
            record=dict(commit='e'*40,run_id='39193216511',run_attempt='2',job='check',
                job_status='failure' if outcome=='skipped' else outcome,staged_step_outcome=outcome)
            env=dict(RUNNER_TEMP=str(directory),LIGHTEFT_SUMMARY_COMMIT=record['commit'],
                LIGHTEFT_SUMMARY_RUN_ID=record['run_id'],LIGHTEFT_SUMMARY_RUN_ATTEMPT=record['run_attempt'],
                LIGHTEFT_SUMMARY_JOB=record['job'],LIGHTEFT_SUMMARY_JOB_STATUS=record['job_status'],
                LIGHTEFT_SUMMARY_STAGED_OUTCOME=outcome)
            with patch.dict(os.environ,env,clear=True):exec(self.summary_script(),{})
            summary=directory/'light-eft-summary-39193216511-2/workflow-summary.json'
            with self.subTest(outcome=outcome):self.assertEqual(json.loads(summary.read_text()),record)
            self.assertFalse((directory/'light-eft-staged-39193216511-2').exists())
            self.assertEqual(list(directory.iterdir()),[summary.parent])

    def test_workflow_summary_preserves_existing_gate_directory_and_refuses_reuse(self):
        staged=self.root/'light-eft-staged-123-1';put(staged/'partial.log',b'preserve failed gate')
        env=dict(RUNNER_TEMP=str(self.root),LIGHTEFT_SUMMARY_COMMIT='a'*40,LIGHTEFT_SUMMARY_RUN_ID='123',
            LIGHTEFT_SUMMARY_RUN_ATTEMPT='1',LIGHTEFT_SUMMARY_JOB='check',LIGHTEFT_SUMMARY_JOB_STATUS='failure',
            LIGHTEFT_SUMMARY_STAGED_OUTCOME='failure')
        with patch.dict(os.environ,env,clear=True):
            exec(self.summary_script(),{})
            with self.assertRaises(FileExistsError):exec(self.summary_script(),{})
        self.assertEqual((staged/'partial.log').read_bytes(),b'preserve failed gate')
        self.assertEqual(list(staged.iterdir()),[staged/'partial.log'])

    def test_always_summary_precedes_always_upload_with_both_independent_paths(self):
        workflow=(ROOT/'.github/workflows/lean.yml').read_text()
        staged=workflow.index('      - name: Verify exact staged joint-flag source sequentially\n')
        summary=workflow.index('      - name: Record workflow outcome independently of staged gate\n')
        upload=workflow.index('      - name: Preserve complete staged-gate evidence including failures\n')
        self.assertLess(staged,summary);self.assertLess(summary,upload)
        self.assertIn('        id: light_eft_staged\n',workflow[staged:summary])
        self.assertIn('        if: always()\n',workflow[summary:upload])
        self.assertIn('        if: always()\n',workflow[upload:])
        for name,expression in [('COMMIT','github.sha'),('RUN_ID','github.run_id'),('RUN_ATTEMPT','github.run_attempt'),
                ('JOB','github.job'),('JOB_STATUS','job.status'),('STAGED_OUTCOME','steps.light_eft_staged.outcome')]:
            self.assertIn('          LIGHTEFT_SUMMARY_'+name+': ${{ '+expression+' }}\n',workflow[summary:upload])
        for directory in ['summary','staged']:
            self.assertIn('            ${{ runner.temp }}/light-eft-'+directory+'-${{ github.run_id }}-${{ github.run_attempt }}\n',workflow[upload:])
        for unchanged in ['actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02',
                '          include-hidden-files: true\n','          if-no-files-found: error\n','          retention-days: 30\n']:
            self.assertIn(unchanged,workflow[upload:])
        self.assertNotIn('continue-on-error',workflow[staged:])

    def test_ported_full_receipt_verifier_changes_only_explicit_source_parameter(self):
        old=(ROOT/SPEC['engine_directory']/'scope.py').read_text();new=(HERE/'ci_receipts.py').read_text()
        find=lambda text:next(n for n in ast.parse(text).body if isinstance(n,ast.FunctionDef) and n.name=='verify_receipts')
        a=find(old);b=find(new);self.assertEqual(b.args.args[-1].arg,'expected_source');b.args.args.pop();b.args.defaults.pop()
        class Restore(ast.NodeTransformer):
            def visit_Name(self,n):
                if n.id=='expected_source':n.id='APPROVED'
                return n
        self.assertEqual(ast.dump(a,include_attributes=False),ast.dump(Restore().visit(b),include_attributes=False))

    def test_reviewed_resource_and_lifecycle_engine_hashes_are_unchanged(self):
        for row in SPEC['engine_files']:
            if row['path'].startswith(SPEC['engine_directory']+'/'):
                data=(ROOT/row['path']).read_bytes();self.assertEqual(hashlib.sha256(data).hexdigest(),row['sha256'])
        runner=(ROOT/SPEC['engine_directory']/'child_runner.py').read_text()
        for literal in ['ADMISSION_HEADROOM=3221225472','STOP_HEADROOM=1073741824','RSS_STOP=6442450944','ANON_GROWTH_STOP=3221225472','INTERVAL=.1','DEADLINE=90.0']:
            self.assertIn(literal,runner)
        pilot=(ROOT/SPEC['engine_directory']/'pilot_child.py').read_text()
        for literal in ['12884901888',"'RLIMIT_CPU':60",'64*1024**2','16']:
            self.assertIn(literal,pilot)

    def test_complete_review_spec_binds_every_candidate_and_engine_source(self):
        for row in [*SPEC['sources'].values(),*SPEC['dependencies'],*SPEC['engine_files']]:
            b=(ROOT/row['path']).read_bytes();self.assertEqual(len(b),row['bytes']);self.assertEqual(hashlib.sha256(b).hexdigest(),row['sha256'])

    def test_decode_assignment_uses_non_self_referential_recursor_with_same_type(self):
        source=(ROOT/SPEC['sources']['source']['path']).read_text()
        declaration=source.split('def decodeAssignment {n m : ℕ} :\n',1)[1].split('\n/-- This applies even when e occurs again in es:',1)[0]
        header,body=declaration.split(':=',1)
        self.assertEqual(' '.join(header.split()),'(l : List (OriginalEdge n)) → JointFlags n J m l → SampledGreedy.Assignment (Fin n) J m')
        self.assertEqual(body.count('List.rec'),1);self.assertNotIn('decodeAssignment',body)
        self.assertIn('(fun _ => fun _ _ _ => ∅)',body)
        self.assertIn('(decodeTail (fun p => bits p.succ)) e',body)
        self.assertIn('(decodeHost (bits 0))',body)
        self.assertIn('Function.update',body)
        self.assertIn('JointFlags n J m l → SampledGreedy.Assignment (Fin n) J m',body)

    def test_every_stage_binds_new_decode_source_and_stale_source_seal_refuses(self):
        row=SPEC['sources']['source'];source=ROOT/row['path'];actual=bind(source)
        self.assertEqual(actual['sha256'],'b7718de506f41b46341ef4f846df8cebda48c810990e8d92a3ec75282c700f1d')
        commands,_=gate.build_plans(self.root,self.root/'tool',self.root/'work',SPEC,'a'*40,bind)
        self.assertEqual([plan['stage'] for plan in commands],list(p.STAGES))
        for plan in commands:self.assertIn(actual,plan['source_bindings'])
        stale=dict(row,bytes=12533,sha256='7187c40f88f68caa69ef7fb188acc29eba9bed4b5b065c62a994f2fc3118d901')
        with patch.object(gate.subprocess,'check_output',return_value=source.read_bytes()),self.assertRaisesRegex(ValueError,'Reviewed source/hash changed'):
            gate.exact_files(dict(sources={'source':stale},dependencies=[],engine_files=[]))

    def test_strict_audit_still_rejects_generated_decode_runtime_partial_helper(self):
        audit,ci,names,raw,_=self.audit_fixture()
        for filename in ['actual-owner-inventory.tsv','recursive-dependencies.tsv']:
            path=ci/filename
            with path.open() as f:
                reader=csv.DictReader(f,delimiter='\t');fields=reader.fieldnames;rows=list(reader)
            found=0
            for row in rows:
                if row['name'].endswith('.extra_generated'):
                    row.update(name='LightEFTSpanners.JointFlagSampling.decodeAssignment._unsafe_rec',kind='definition',partial='true');found+=1
            self.assertEqual(found,1)
            with path.open('w',newline='') as f:
                writer=csv.DictWriter(f,fieldnames=fields,delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(rows)
        with self.assertRaisesRegex(Exception,'Unsafe/partial declaration'):audit.validate(ci,names,raw)

    def test_actual_reviewed_visible_gates_are_three_three_four_four(self):
        sys.path.insert(0,str(ROOT/SPEC['engine_directory']));import scope
        self.assertEqual([scope.Context.visible_gate(None,{'stage':s}) for s in p.STAGES],[3*1024**3,3*1024**3,4*1024**3,4*1024**3])

    def test_actual_reviewed_live_stop_boundaries_oom_and_pid_drift(self):
        sys.path.insert(0,str(ROOT/SPEC['engine_directory']));import child_runner, decision_telemetry
        row=dict(path='/synthetic',limit=str(8*1024**3),current=1,memory_stat={'anon':1},oom={'oom':0,'oom_kill':0,'oom_group_kill':0},pids_max='100',pids_current=2,pids_events={'max':0})
        account=dict(namespace='synthetic',membership='synthetic',identities=['synthetic'],headroom=4*1024**3,system_available=4*1024**3,nodes=[row])
        baseline=copy.deepcopy(account)
        def errors(change):
            a=copy.deepcopy(account);child={'rss':1,'vm':1}
            if change=='rss':child['rss']=6*1024**3
            if change=='anon':a['nodes'][0]['memory_stat']['anon']=1+3*1024**3
            if change=='headroom':a['headroom']=1024**3-1
            if change=='host':a['system_available']=1024**3-1
            if change=='oom':a['nodes'][0]['oom']['oom_kill']=1
            if change=='pid':a['nodes'][0]['pids_max']='99'
            sample=dict(accounting=a,child=child,collection_errors=[])
            return decision_telemetry.policy_errors(sample,baseline,{'/synthetic':1},1024**3,6*1024**3,3*1024**3,child_runner.check_memory)
        self.assertEqual(errors('none'),[])
        for change in ['rss','anon','headroom','host','oom','pid']:
            with self.subTest(change=change):self.assertTrue(errors(change))

    def test_all_ordinary_events_need_no_dispatch_document_or_readiness_flag(self):
        for event,ref in [('push','refs/heads/reviewed-ci'),('pull_request','refs/pull/42/merge'),('workflow_dispatch','refs/heads/reviewed-ci')]:
            for attempt in ['1','2']:
                e=self.env.copy();e.update(GITHUB_EVENT_NAME=event,GITHUB_REF=ref,GITHUB_RUN_ATTEMPT=attempt)
                e['GITHUB_WORKFLOW_SHA']='c'*40
                identity=p.ci_identity(e,'a'*40)
                self.assertEqual(identity['GITHUB_SHA'],'a'*40);self.assertEqual(identity['GITHUB_RUN_ID'],'123');self.assertEqual(identity['GITHUB_RUN_ATTEMPT'],attempt)
        self.assertFalse(hasattr(gate,'preflight'));self.assertFalse(hasattr(p,'readiness'));self.assertFalse(hasattr(p,'coordination'))
        source=(HERE/'ci_gate.py').read_text()
        for forbidden in ['LIGHTEFT_CI_HANDOFF_JSON','approved-preflight.json','readiness-policy.json','CI_external_reservation']:
            self.assertNotIn(forbidden,source)

    def test_job_worker_setting_reaches_every_explicit_child_environment(self):
        work=self.root/'work';plans=p.plans(self.root,self.root/'tool',work,SPEC,[work/'objects',self.root/'deps'],'a'*40)
        self.assertTrue(all(row['env']['LEAN_NUM_THREADS']=='1' for row in plans))

    def test_ci_spec_is_bound_to_the_exact_event_checkout(self):
        here=self.root/'candidate';here.mkdir();raw=b'{"synthetic": true}\n';(here/'ci-spec.json').write_bytes(raw)
        with patch.object(gate,'ROOT',self.root),patch.object(gate,'HERE',here),patch.object(gate.subprocess,'check_output',return_value=raw):
            self.assertEqual(gate.bound_spec(),{'synthetic':True})
            (here/'ci-spec.json').write_bytes(b'{"synthetic": false}\n')
            with self.assertRaises(ValueError):gate.bound_spec()

    def test_fresh_ci_lock_has_no_local_fixed_identity_or_reuse(self):
        source=(HERE/'ci_lease.py').read_text()
        self.assertIn('os.O_EXCL',source);self.assertIn('fcntl.LOCK_EX|fcntl.LOCK_NB',source)
        self.assertNotIn('3258',source);self.assertNotIn('distance-sparsification-single-compiler.lock',source)
        self.assertNotIn('os.O_TRUNC',source);self.assertNotIn('unlink(',source)
        self.assertIn('kernel_echild=True',source)

if __name__=='__main__':
    def audit(event,args):
        if event=='subprocess.Popen':forbid()
        if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)):
            path=os.path.abspath(os.fsdecode(args[0]))
            if path.startswith(('/proc/','/sys/')) or path=='/tmp/distance-sparsification-single-compiler.lock':forbid()
    sys.addaudithook(audit)
    with contextlib.ExitStack() as stack:
        for obj,name in [(subprocess,'Popen'),(fcntl,'flock'),(os,'fork'),(os,'statvfs'),(shutil,'disk_usage'),(resource,'getrlimit'),(resource,'setrlimit'),(resource,'getrusage')]:
            stack.enter_context(patch.object(obj,name,forbid))
        result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Candidate))
    (RUN/'result.json').write_text(json.dumps(dict(tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),successful=result.wasSuccessful(),qualification='Synthetic/static only; real launches, locks and resource probes forbidden'),indent=2)+'\n')
    sys.exit(0 if result.wasSuccessful() else 1)
