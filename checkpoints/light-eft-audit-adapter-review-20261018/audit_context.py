"""One audit context; no build, resolver, checker, or project-output mutation."""
from pathlib import Path
import hashlib, json, os, re, shutil, stat, subprocess, sys, time
from shared_preservation import inspect, signature, utc
from one_time_extension import ExtendedFrozenInputs
from audit_outputs import OUTPUTS, DISK_FLOOR, bind_outputs, inspect_outputs
import child_runner as child

A = Path(__file__).resolve().parent
R = A.parents[1]
PLAN = json.loads((A/'PLAN.json').read_text())
AUDIT_SHA = 'f4e44e8994c4d43c8bd38fb5f4c029adb52e87192baa73e554178c41b5bb43db'
AUDIT = R/'scripts/LightEFTFullAudit.lean'
ROOT = Path(PLAN['retained_root'])
SOURCE = '78cb40c7837db049d645d73696f2e0b724ce8a3b'


def digest(p):
    with Path(p).open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()


def exact_command():
    return ['/workspace/toolchains/lean-4.34.0-linux/bin/lean', '-j1', '-s65536', '-M5120',
            '-DautoImplicit=false', '-DwarningAsError=true', str(AUDIT)]


def reviewed_files(commit):
    if not re.fullmatch('[0-9a-f]{40}',commit): raise RuntimeError('Exact reviewed40hex adapter commit required')
    prefix=str(A.relative_to(R))
    paths=subprocess.check_output(['git','ls-tree','-r','--name-only',commit,'--',prefix],cwd=R,text=True).splitlines()
    if not paths: raise RuntimeError('Reviewed commit has no adapter files')
    result=[]
    for name in paths:
        p=R/name
        raw=subprocess.check_output(['git','show',commit+':'+name],cwd=R)
        if p.read_bytes()!=raw: raise RuntimeError('Reviewed adapter file changed: '+name)
        result.append(p)
    scripts={p for p in result if p.parent==A and p.suffix=='.py'}
    if scripts!=set(A.glob('*.py')): raise RuntimeError('Unreviewed/missing adapter Python membership')
    return result


class AuditContext:
    fixture_only=False
    preservation_failed=False
    def __init__(self,lock,lease,evidence,work,reviewed_commit,files):
        self.lock=lock;self.acquired_ns=lease.record['acquired_ns']
        self.evidence=Path(evidence);self.work=Path(work);self.reviewed_commit=reviewed_commit;self.files=files
        self.protected=json.loads((A/'protected-bindings.json').read_text())['bindings']
        self.inputs_initialized=False
        self.created_wall_ns=time.time_ns()
        # These directories must not exist before this one authorized attempt.
        self.work.mkdir()
        (self.work/'ci-evidence').mkdir()
        self.output_spec={'work':str(self.work),'work_identity':signature(self.work.stat())[:2],
            'ci_identity':signature((self.work/'ci-evidence').stat())[:2],
            'raw':str(self.evidence/'attempt/raw.log'),'created_wall_ns':self.created_wall_ns}

    def check_pins(self):
        for pin in PLAN['dependencies']:
            path=Path('/workspace/paper-formalizations/.lake/packages')/pin['name']
            if subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()!=pin['rev']:
                raise RuntimeError('Dependency pin changed: '+pin['name'])
            if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=path):
                raise RuntimeError('Dependency tracked source changed: '+pin['name'])

    def check_protected(self):
        actual={str(p) for p in ROOT.rglob('*') if p.is_file()}
        if any(p.is_symlink() for p in ROOT.rglob('*')): raise RuntimeError('Retained-root symlink')
        if actual!={row['path'] for row in self.protected}: raise RuntimeError('Retained486object/414resolution membership changed')
        directories={str(parent) for name in actual for parent in Path(name).parents if parent!=ROOT and ROOT in parent.parents}
        if {str(p) for p in ROOT.rglob('*') if p.is_dir()}!=directories: raise RuntimeError('Retained directory membership changed')
        for row in self.protected:
            p=Path(row['path'])
            if inspect(p,{'role':row['role']})!=row: raise RuntimeError('Protected input changed: '+str(p))

    def initialize(self):
        if PLAN['source_commit']!=SOURCE or PLAN['argv']!=exact_command() or digest(AUDIT)!=AUDIT_SHA:
            raise RuntimeError('Audit source/command changed')
        if len(PLAN['required_modules'])!=len(set(PLAN['required_modules'])) or len(PLAN['required_modules'])!=485:
            raise RuntimeError('Required ordinary module set differs')
        inventory=R/PLAN['prior_inventory']['path']
        if digest(inventory)!=PLAN['prior_inventory']['sha256']: raise RuntimeError('Accepted inventory authority changed')
        specs={}
        with inventory.open() as f:
            for line in f:
                row=json.loads(line)
                specs[Path(row['path'])]={'role':row['role'],'expected_sha256':row['sha256'],
                    'expected_identity':row['identity'],'expected_bytes':row['bytes'],'advice_scope':row['advice_scope']}
        if len(specs)!=82856: raise RuntimeError('Accepted inventory cardinality differs')
        for row in self.protected:
            specs[Path(row['path'])]={'role':row['role'],'expected_sha256':row['sha256'],
                'expected_identity':row['identity'],'expected_bytes':row['bytes'],'advice_scope':None}
        for p in self.files+[AUDIT,inventory,R/'scripts/LightEFTProcessLifecycle.py',Path(sys.executable).resolve()]:
            previous=specs.get(p,{})
            value=digest(p)
            if previous.get('expected_sha256',value)!=value:raise RuntimeError('Accepted source/tool/lifecycle hash changed: '+str(p))
            specs[p]={**previous,'role':'audit_adapter_input','expected_sha256':value,'advice_scope':None}
        specs[AUDIT]['expected_sha256']=AUDIT_SHA
        self.source_members={p for p in specs if p.suffix=='.lean' and any(str(p).startswith(str(R/root)+'/') for root in
            ['Light Edge Fault Tolerant Graph Spanners','An Alternate Proof of Near-Optimal Light Spanners'])}
        self.search_roots=[Path(p) for p in PLAN['environment']['LEAN_PATH'].split(os.pathsep)[1:]]
        self.search_members={p for p in specs if any(str(p).startswith(str(root)+'/') for root in self.search_roots)
            and (str(p).endswith(('.olean','.olean.private','.olean.server','.ilean','.ir')) or '.so' in p.name)}
        self.check_pins();self.check_protected();self.check_membership()
        self.frozen=ExtendedFrozenInputs(specs,self.evidence);self.frozen.lock=self.lock
        self.input_ref=self.frozen.freeze();self.inputs_initialized=True
        self.small=set(self.files+[AUDIT,R/'scripts/LightEFTProcessLifecycle.py'])
        self.save('input-inventory-reference.json',self.input_ref)

    def check_membership(self):
        current=set()
        for folder,ns in [('Light Edge Fault Tolerant Graph Spanners','LightEFTSpanners'),('An Alternate Proof of Near-Optimal Light Spanners','LightSpanners')]:
            root=R/folder;current.update((root/ns).rglob('*.lean'))
            if (root/(ns+'.lean')).exists():current.add(root/(ns+'.lean'))
        if current!=self.source_members: raise RuntimeError('Frozen source membership changed')
        current=set()
        for root in self.search_roots:
            for p in root.rglob('*'):
                if p.is_symlink(): raise RuntimeError('Dependency search symlink')
                if p.is_file() and (str(p).endswith(('.olean','.olean.private','.olean.server','.ilean','.ir')) or '.so' in p.name):
                    if p.relative_to(root).parts[0].split('.')[0] in ('LightSpanners','LightEFTSpanners'):
                        raise RuntimeError('Project object outside exact retained root')
                    current.add(p)
        if current!=self.search_members: raise RuntimeError('Frozen dependency/tool search membership changed')
        self.check_pins()

    def save(self,name,data):
        (self.evidence/name).write_text(json.dumps(data,indent=2)+'\n')

    def visible_gate(self,plan): return 4294967296

    def before_child(self,plan,record,save):
        if plan!={'stage':'audit','module':'LightEFTFullAudit','argv':exact_command(),'env':PLAN['environment']}:
            raise RuntimeError('Only the single exact audit invocation is authorized')
        self.frozen.identities();self.check_membership();self.check_protected()
        for p in self.small:
            if inspect(p,self.frozen.specs[str(p)])!=self.frozen.rows[str(p)]: raise RuntimeError('Adapter/audit input changed')
        if list((self.work/'ci-evidence').iterdir()): raise RuntimeError('Preexisting source outputs')
        snapshot=self.evidence/(AUDIT_SHA+'.lean.txt');snapshot.write_bytes(AUDIT.read_bytes())
        record.update(stage_kind='audit_only',canonical_input_inventory=self.input_ref,
            approved_adapter_commit=self.reviewed_commit,submitted_source_sha256=AUDIT_SHA,
            source_snapshot=str(snapshot.relative_to(self.evidence)),audit_output_budget=self.output_spec,
            source_outputs_absent_before_exec=True,
            final_full_content_verification_required=True,between_child_preservation_passed=True)
        save()

    def prepare_child(self,plan,record,save,accounting):
        child.assert_idle('audit-admission',record)
        info=self.frozen.advise_once_extension(accounting,'single-audit-admission')
        now=accounting.sample()
        record.update(admission=now,idle_advice_reference={'mode':info['mode'],'counts':info['counts'],
            'bytes':info['bytes'],'scope_identity_sha256':info['scope_identity_sha256']})
        save();child.check_memory(now,now,4294967296)
        if now['system_available']<3221225472: raise child.MemoryGuardError('Host admission below3GiB')
        if shutil.disk_usage(self.work).free<=DISK_FLOOR: raise RuntimeError('Disk headroom must exceed2GiB')
        inspect_outputs(self.output_spec)
        return now

    def after_child(self,plan,record,save):
        self.frozen.identities();self.check_membership();self.check_protected()
        record['source_output_snapshot']=inspect_outputs(self.output_spec,complete=False)
        record['between_child_preservation_passed']=True;save()

    def complete_log(self,path,record,save):
        with path.open('r+b') as f:
            f.flush();os.fsync(f.fileno());a=os.fstat(f.fileno());h=hashlib.file_digest(f,'sha256').hexdigest();b=os.fstat(f.fileno())
            if signature(a)!=signature(b): raise RuntimeError('Completed log changed')
            os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
            if signature(os.fstat(f.fileno()))!=signature(b): raise RuntimeError('Completed log changed during advice')
        record.setdefault('completed_logs',{})[path.name]={'bytes':b.st_size,'sha256':h,'identity':signature(b),'fsynced_advised':True};save()

    def output_summary(self): return {'project_outputs_added':0,'project_objects_protected':486,'resolution_records_protected':414}

    def final_verify(self):
        result=self.frozen.final_verify()
        try:self.check_membership();self.check_protected()
        except Exception as exc:result.update(matching=False,membership_or_protected_error=repr(exc))
        if self.preservation_failed: result.update(matching=False,prior_preservation_failure=True)
        self.save('final-content-verification.json',result)
        return result
