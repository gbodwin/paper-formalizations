"""Ordinary-event staged gate. Operator-exclusive window precedes publication.
No dispatch-only prerequisite, readiness flag or cross-host pause assertion.
"""
from pathlib import Path
import csv, datetime, hashlib, json, os, shutil, subprocess, sys, time, tomllib, traceback
from ci_policy import STAGES, TARGET, QUALIFICATION, require, ci_identity, scope_contract, plans
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]

def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def save(p,data):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(data,indent=2)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc)
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()

def bound_spec():
    path=HERE/'ci-spec.json'
    blob=subprocess.check_output(['git','show','HEAD:'+str(path.relative_to(ROOT))],cwd=ROOT)
    require(path.read_bytes()==blob,'CI specification differs from exact event checkout')
    return json.loads(blob)

def exact_files(spec):
    records={}
    for row in [*spec['sources'].values(),*spec['dependencies'],*spec['engine_files']]:
        rel=Path(row['path']);require(not rel.is_absolute() and '..' not in rel.parts,'Unsafe reviewed relative path')
        p=ROOT/rel;require(not p.is_symlink() and p.is_file(),'Missing/symlink reviewed source')
        for parent in p.parents:require(not parent.is_symlink(),'Reviewed source parent symlink')
        require(p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],'Reviewed source/hash changed: '+str(rel))
        require(subprocess.check_output(['git','show','HEAD:'+str(rel)],cwd=ROOT)==p.read_bytes(),'Source not bound to exact checked-out Git commit')
        records[str(p)]=row
    return records

def build_plans(root,tool,work,spec,source_commit,bind,staged_root):
    packages=ROOT/'.lake/packages'
    dependency_roots=[packages/n/'.lake/build/lib/lean' for n in spec['pins'] if (packages/n/'.lake/build/lib/lean').is_dir()]
    roots=[work/'objects',staged_root,ROOT/'.lake/build/lib/lean',*dependency_roots,tool/'lib/lean']
    commands=plans(ROOT,tool,work,spec,roots,source_commit)
    for p in commands:p['source_bindings']=[bind(x) for x in p['sources']]
    return commands,roots

def execute_four(commands,run_child,finish):
    completed=[]
    for p in commands:
        r=run_child(p)  # exception => stop; no catch/retry/parallel worker
        completed.append(dict(stage=p['stage'],attempt_id=r['attempt_id']))
    return dict(stages=completed,result=finish())

def context_type(base,work,evidence,commands,roots,deps,identity,inputs,inv,classified,bind,*,admission_module=None):
    """Actual CI context factory, called only after exact engine authentication.

    Keeping construction separate lets regressions invoke this real preexec
    hook without a CI claim, common lease, process launch or resource probe.
    """
    from ci_inventory import CIIdentityGuard
    from ci_handoff_contract import CONTRACT
    # Mode is explicit constructor authority, never inferred from a mutable
    # plan's module field. Serialized strings recursively detach all plan data.
    canonical_context=admission_module is None
    if canonical_context:
        expected_identity=tuple((TARGET,stage) for stage in STAGES)
    else:
        require(admission_module in tuple(CONTRACT['replay_order']),'Unreviewed singleton admission context')
        expected_identity=((admission_module,'replay'),)
    require(tuple((p.get('module'),p.get('stage')) for p in commands)==expected_identity,
            'Canonical/admission constructor plan identity differs')
    if not canonical_context:
        require(len(commands[0]['argv'])==3 and Path(commands[0]['argv'][0]).name=='leanchecker' and
                commands[0]['argv'][-2:]==['-v',admission_module],'Singleton admission constructor command differs')
    def encoded(plan):
        return json.dumps(plan,sort_keys=True,separators=(',',':'))
    frozen_plans=tuple(encoded(p) for p in commands)
    def checked_plan(plans,index,plan):
        require(tuple(encoded(p) for p in commands)==frozen_plans and
                tuple(encoded(p) for p in plans)==frozen_plans,'Constructor plan authority changed')
        require(0<=index<len(frozen_plans) and encoded(plan)==frozen_plans[index],
                'Out-of-order/mutated immutable context plan')
        return json.loads(frozen_plans[index])
    class CIContext(base):
        def __init__(self,lease):
            require(tuple(encoded(p) for p in commands)==frozen_plans,'Plans changed before context construction')
            self.work=work;self.evidence=evidence;self.lease=lease;self.lock=lease.file;self.acquired_ns=lease.acquired_ns
            self.plans=commands;self.roots=roots;self.dependencies=deps;self.fixture=False
            self.source_commit=identity['GITHUB_SHA'];self.wrapper_commit=identity['GITHUB_SHA'];self.inputs=inputs
            self.new={};self.resolved={};self.objects=roots[0];self.target=roots[0]/Path(*TARGET.split('.')).with_suffix('.olean')
            self.resolution=work/'resolution.json';self.audit=work/'audit/ci-evidence';self.audit.mkdir(parents=True)
            self.preservation_failed=False;self.seen=[];self.audit_result=None;self.inventory_policy=inv
            self.canonical_fixture_result=None;self.canonical_fixture_attempt=None
            self.members=classified['members'];self.signature_ref=dict(qualification=QUALIFICATION)
            self.excluded_ref=None;self._preexec_guard=None
            path=evidence/'excluded-metadata-initial.jsonl';self.write_metadata(path,classified['excluded']);self.excluded_ref=bind(path)
            path=evidence/'inputs.jsonl'
            with path.open('x') as f:
                for row in self.inputs.values():f.write(json.dumps(row,separators=(',',':'))+'\n')
            self.input_ref=bind(path)

        def before_child(self,p,r,save_receipt):
            expected=checked_plan(self.plans,len(self.seen),p)
            r['CI_identity']=identity;r['dependency_qualification']=QUALIFICATION
            if canonical_context and expected['stage'] in ['replay','audit']:
                from canonical_fixture import completed_prerequisite
                require(self.canonical_fixture_result is not None,'No canonical key fixture prerequisite')
                prior=load(self.evidence/'resolve/receipt.json')
                require(prior['attempt_id']==self.canonical_fixture_attempt and
                        prior.get('canonical_key_equivalence_fixture')==self.canonical_fixture_result,
                        'Canonical live prerequisite differs from completed resolve')
                link=completed_prerequisite(prior,json.loads(frozen_plans[1]),self.evidence/'resolve',identity,self.lease.record)
                require(link['resolve_ended_ns']<r['started_ns'],'Canonical resolve must precede replay/audit')
                r['canonical_key_equivalence_prerequisite']=link
            return super().before_child(p,r,save_receipt)

        def after_child(self,p,r,save_receipt):
            expected=checked_plan(self.plans,len(self.seen),p)
            result=None
            if canonical_context and expected['stage']=='resolve' and r.get('exit')==0 and 'failure' not in r:
                from canonical_fixture import validate_log
                result=validate_log((self.evidence/'resolve/raw.log').read_text())
            super().after_child(p,r,save_receipt)
            if result is not None:
                self.canonical_fixture_result=result;self.canonical_fixture_attempt=r['attempt_id']
                r['canonical_key_equivalence_fixture']=result;save_receipt()

        def prepare_child(self,p,r,save_receipt,accounting):
            checked_plan(self.plans,len(self.seen),p)
            # The inherited admission path still performs full content checks.
            admission=super().prepare_child(p,r,save_receipt,accounting)
            semantic=self.inventory_policy.original['semantic']
            self._critical={path:dict(row) for path,row in self.inputs.items() if path not in semantic}
            self._critical.update({path:dict(row) for path,row in {**self.new,**self.resolved}.items()})
            for row in [self.input_ref,self.excluded_ref]:self._critical[row['path']]=dict(row)
            for row in r['submitted_sources']:
                require(row['snapshot']==row['sha256']+'.source','Submitted snapshot name differs')
                path=self.stage_evidence/row['snapshot'];self._critical[str(path)]=bind(path,row)
            tracked={**self.inputs,**self.inventory_policy.original['excluded'],**self.new,**self.resolved,**self._critical}
            directories=self.inventory_policy.original['directories']
            members={str(root):set(names)|{path for path in directories if path!=str(root) and Path(path).is_relative_to(root)}
                     for root,names in self.members.items()}
            output_dirs=set();parent=self.target.parent
            while parent!=self.objects:
                require(parent.is_relative_to(self.objects),'Target output parent outside root')
                output_dirs.add(str(parent));parent=parent.parent
            members[str(self.objects)]=set(self.new)|output_dirs
            members[str(self.audit)]=set()  # No audit output exists before exec.
            self._preexec_guard=CIIdentityGuard(tracked,members,directories)
            self._preexec_plan=json.loads(json.dumps(p))
            return admission

        def preexec(self,p,r,save_receipt):
            began=time.monotonic_ns();self.lease.check()
            checked_plan(self.plans,len(self.seen),p)
            require(self._preexec_guard is not None and p==self._preexec_plan==self.plans[len(self.seen)],'Unprepared/mutated CI preexec')
            self._preexec_guard.verify()
            for path,row in self._critical.items():require(bind(path)==row,'Critical CI input changed: '+path)
            self.lease.check()
            free=shutil.disk_usage(self.work).free;require(free>2*1024**3,'Fresh preexec disk below boundary')
            r.update(preexec_disk_bytes=free,preexec_binding_verified=True,
                     preexec_binding_strategy='exact identity/membership plus critical hashes',
                     preexec_identity_files=len(self._preexec_guard.bindings),preexec_critical_hashes=len(self._critical),
                     preexec_validation_started_ns=began,preexec_validation_finished_ns=time.monotonic_ns())
            save_receipt()

    return CIContext

def run_stage(root,env,spec):
    scope_contract(spec)
    head=git('rev-parse','HEAD');identity=ci_identity(env,head)
    def identity_check():
        require(ci_identity(dict(os.environ),head)==identity,'CI event/run/attempt binding changed')
    exact_files(spec)
    from canonical_fixture import validate_sources
    validate_sources(ROOT,spec)
    # Authenticate every imported runtime file before importing it. All are the
    # preserved reviewed engine; CI adapters below do not rewrite those files.
    engine=ROOT/spec['engine_directory'];sys.path.insert(0,str(engine));sys.path.insert(0,str(ROOT/'scripts'))
    import child_runner, scope, focused_audit
    from contracts import bind, save as durable_save, effective
    from LightEFTCgroup import memory_snapshot
    from ci_accounting import CIAccounting
    from ci_inventory import CIInventory
    from ci_lease import CILease
    candidates=[]
    home=Path(env['HOME'])/'.elan/toolchains'
    for t in home.iterdir():
        p=t/'bin/lean'
        if p.is_file() and digest(p)==spec['tool_hashes']['lean']:candidates.append(t)
    require(len(candidates)==1,'Exactly one hash-pinned official Lean toolchain required')
    tool=candidates[0];require(digest(tool/'bin/leanchecker')==spec['tool_hashes']['leanchecker'],'Wrong official checker')
    for name,rev in spec['pins'].items():
        require(git('-C',str(ROOT/'.lake/packages'/name),'rev-parse','HEAD')==rev,'Fresh CI dependency checkout pin differs')
        require(not git('-C',str(ROOT/'.lake/packages'/name),'status','--porcelain','--untracked-files=no'),'Dirty CI dependency source checkout')
    from ci_staged_inputs import STAGED
    from ci_handoff import verify_decoder,prepare_inputs,admit_carrier,retained_context
    from ci_receipts import verify_receipts
    from ci_admission import replay_plans,context_type as admission_type,execute_sequence,verify_schedule
    from ci_handoff_contract import CONTRACT
    from ci_admission_receipts import verify_singleton_receipt
    decoder=verify_decoder(ROOT,tool,env,identity,spec,verify_receipts)
    carrier=prepare_inputs(root,ROOT,spec,decoder)
    staged_root,staged_protected,staged_parts=carrier['root'],carrier['protected'],carrier['layouts']
    work=root/'work';evidence=root/'runtime'
    require(not work.exists() and not evidence.exists(),'Fresh CI paths required; no retry')
    commands,roots=build_plans(root,tool,work,spec,identity['GITHUB_SHA'],bind,staged_root)
    deps={}
    for r in spec['dependencies']:
        p=(staged_root if r['module'] in STAGED else ROOT/'.lake/build/lib/lean')/Path(*r['module'].split('.')).with_suffix('.olean')
        deps[r['module']]=dict(bind(p),module=r['module'])
        if r['module'] in staged_parts:deps[r['module']]['accepted_staged_olean_parts']=staged_parts[r['module']]
    require(len(deps)==364,'Exactly364 project dependencies required')
    effective(roots,deps,work/'objects'/Path(*TARGET.split('.')).with_suffix('.olean'),False,predicted=True)
    inv=CIInventory(roots[1:],tool,bind);classified=inv.scan()
    inputs={**classified['semantic'],**staged_protected}
    for name in ['lean','leanchecker']:inputs[str(tool/'bin'/name)]=bind(tool/'bin'/name)
    for r in exact_files(spec):inputs[r]=bind(r)
    for p in [HERE/'ci-spec.json',ROOT/'lake-manifest.json',ROOT/'lean-toolchain']:
        inputs[str(p)]=bind(p)
    matched=retained_context(decoder,roots[2:],classified['semantic'],inputs)
    save(root/'same-run-handoff.json',dict(CI_identity=identity,decoder_root=str(decoder['root']),
        decoder_stages=decoder['stages'],decoder_release_ns=decoder['lease']['release_ns'],
        carrier_manifest=carrier['reference'],objects=carrier['objects'],retained_context=matched,
        qualification=spec['object_admission']['context_qualification']))
    inputs[str(root/'same-run-handoff.json')]=bind(root/'same-run-handoff.json')
    # The operator-exclusive window spans publication and all resulting runs.
    # This process records fresh CI facts without asserting external pause state.
    identity_check();child_runner.assert_idle('CI-after-planning-before-claim',{})
    save(root/'fresh-CI-owner.json',dict(identity=identity,supervisor_pid=os.getpid(),
        issued_ns=__import__('time').monotonic_ns(),source_commit=identity['GITHUB_SHA'],
        boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),
        namespaces={n:os.readlink('/proc/self/ns/'+n) for n in ['pid','mnt','cgroup']},
        qualification='Fresh CI environment; pre-publication operator window is external'))
    (root/'production-claim.json').open('x').write(json.dumps(identity)+'\n')
    work.mkdir();(work/'objects').mkdir();evidence.mkdir()

    CIContext=context_type(scope.Context,work,evidence,commands,roots,deps,identity,inputs,inv,classified,bind)
    admissions=replay_plans(root,ROOT,tool,spec,commands,roots)
    admission_authority=tuple(zip(admissions,tuple(CONTRACT['replay_order']),strict=True))

    state=dict(source_commit=identity['GITHUB_SHA'],harness_commit=identity['GITHUB_SHA'],CI_identity=identity,
        accepted=False,independent_review='pending',dependency_qualification=QUALIFICATION)
    try:
        with CILease(root,durable_save,identity_check) as lease:
            require(decoder['lease']['release_ns']<lease.record['acquired_ns'],'Decoder release must precede the corollary lease')
            accounting=CIAccounting(memory_snapshot)
            def admit(a):
                module=next((module for entry,module in admission_authority if entry is a),None)
                require(module is not None,'Admission entry lacks constructor authority')
                admit_carrier(carrier['manifest'],carrier['reference'],spec,carrier['objects'])
                w=a['work'];e=a['evidence'];w.mkdir(parents=True);(w/'objects').mkdir();e.mkdir(parents=True)
                typ=context_type(scope.Context,w,e,[a['plan']],a['roots'],deps,identity,inputs,inv,classified,bind,admission_module=module)
                expected=deps[module]['path']
                ctx=admission_type(typ,module,expected)(lease);ctx.target.parent.mkdir(parents=True)
                return child_runner.run_child(a['plan'],w,e/'replay',ctx,accounting=accounting)
            context=CIContext(lease);context.target.parent.mkdir(parents=True)
            def child(p):
                admit_carrier(carrier['manifest'],carrier['reference'],spec,carrier['objects'])
                return child_runner.run_child(p,Path(p['cwd']),evidence/p['stage'],context,accounting=accounting)
            def progress(rows):
                state['admission_replays']=list(rows);save(root/'admission-progress.json',dict(completed=rows,CI_identity=identity))
            state.update(execute_sequence(admissions,admit,commands,child,context.finish,progress))
        # Core child runner and context preserve reaping/limits/binding facts;
        # additionally reconcile the complete actual four-stage schedule below.
        receipts=[load(evidence/p['stage']/'receipt.json') for p in commands]
        previous=0;ids=set()
        for p,r in zip(commands,receipts,strict=True):
            require(r['state']=='finished' and r['exit']==0 and not r.get('failure') and not r.get('cleanup_errors'),'Failed CI receipt')
            require(r['source_commit']==identity['GITHUB_SHA'] and r['wrapper_commit']==identity['GITHUB_SHA'],'CI receipt commit differs')
            require(r['argv']==p['argv'] and r['environment']==p['env'] and r['planned_source_bindings']==p['source_bindings'],'CI receipt exact command/source differs')
            require(r['attempt_id'] not in ids,'Duplicate CI UUID');ids.add(r['attempt_id'])
            require(lease.record['acquired_ns']<=r['started_ns']<r['ended_ns']<=lease.record['release_ns'] and previous<r['started_ns'],'CI overlap/outside lease')
            previous=r['ended_ns']
            require(all(r.get(k) for k in ['direct_reaped','all_descendants_gone','kernel_no_children_verified','waitid_wait4_status_match','kernel_limits_verified','between_child_preservation_passed']),'CI lifecycle/preservation check missing')
        require(lease.record['state']=='released' and lease.record['kernel_echild'] and not lease.record.get('release_errors'),'CI lease not cleanly released')
        from ci_receipts import verify_receipts
        verify_receipts(evidence,lease.record,commands,deps,identity['GITHUB_SHA'],expected_source=identity['GITHUB_SHA'],expected_identity=identity)
        admission_receipts=[]
        for a in admissions:
            verify_singleton_receipt(a['evidence'],lease.record,[a['plan']],deps,identity['GITHUB_SHA'],expected_source=identity['GITHUB_SHA'])
            admission_receipts.append(load(a['evidence']/'replay/receipt.json'))
        verify_schedule(admission_receipts+receipts,lease.record,identity)
        admit_carrier(carrier['manifest'],carrier['reference'],spec,carrier['objects'])
        state['accepted']=True  # gate pass only; independent proof review is pending
    except BaseException as e:state['failure']=repr(e);traceback.print_exc()
    finally:
        save(root/'result.json',state)
        # Preserve everything available, even before an audit/export succeeds.
        exports=[]
        for p in sorted(evidence.rglob('*')):
            if p.is_file() and p.name in ['raw.log','receipt.json','samples.jsonl','inputs.jsonl','excluded-metadata-initial.jsonl','excluded-metadata-final.jsonl']:
                dest=root/'available-exports'/p.relative_to(evidence);m=focused_audit.chunk(p,dest)
                exports.append(dict(source=str(p),manifest=str(dest/'manifest.json'),sha256=m['sha256'],bytes=m['bytes'],parts=len(m['parts'])))
        save(root/'available-export-index.json',exports)
    return state

def main():
    env=dict(os.environ);identity=ci_identity(env,git('rev-parse','HEAD'))
    temp=Path(env['RUNNER_TEMP']);require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(),'Invalid CI temporary directory')
    cache=temp/('light-eft-corollary-python-'+identity['GITHUB_RUN_ID']+'-'+identity['GITHUB_RUN_ATTEMPT'])
    require(sys.dont_write_bytecode and sys.pycache_prefix==str(cache) and not cache.exists(),
            'Fresh absent Python cache prefix and -B required; do not read inherited control bytecode')
    root=temp/('light-eft-corollary-'+identity['GITHUB_RUN_ID']+'-'+identity['GITHUB_RUN_ATTEMPT'])
    root.mkdir(mode=0o700,exist_ok=False)
    try:
        spec=bound_spec()
        require(run_stage(root,env,spec)['accepted'],'CI staged gate failed')
    except BaseException as e:
        save(root/'stage-failure.json',dict(error=repr(e),CI_identity=identity))
        (root/'stage-raw.log').write_text(traceback.format_exc())
        traceback.print_exc();return 1
    finally:
        rows=[]
        for p in sorted(root.rglob('*')):
            if p.is_file() and p!=root/'evidence-sha256.json':
                with p.open('rb') as f:h=hashlib.file_digest(f,'sha256').hexdigest()
                rows.append(dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=h))
        save(root/'evidence-sha256.json',rows)
    return 0

if __name__=='__main__':sys.exit(main())
