"""Exact port/delta/authority source check only; no execution or admission."""
from pathlib import Path
import ast,copy,hashlib,json,re,subprocess,sys
import port as p
R=p.R;B=R/p.BRIDGE;H=p.H
sys.path.insert(0,str(B));import bridge_fixture as f
from phase_report import MAX_BYTES
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
def row(path,**extra):
    raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),**extra)
actual=(R/p.AUDIT).read_text();old=p.base(p.AUDIT);decoder=p.base(p.DECODER)
assert actual==p.audit_source() and (R/p.FIXTURE).read_text()==p.fixture_source() and (R/p.COMPOSITE).read_text()==p.composite_source()
assert p.block(actual)==p.block(decoder)
labels=['frontend-ready']+re.findall(r'LightEFTBridgeAuditTiming.mark "([a-z-]+)"',actual)
assert tuple(labels)==p.PHASES and len(labels)==len(set(labels))==15 and MAX_BYTES<=2048
assert all(not any(t in label for t in ['COLLISION','collision-']) for label in labels)
assert actual.count('IO.monoMsNow')==actual.count('IO.getStderr')==2
assert actual.count('IO.getStdout')==old.count('IO.getStdout')==1
assert actual.index('set_option stderrAsMessages false\n')<actual.index('run_cmd do\n')
assert actual.endswith('\nend LightEFTBridgeAuditDiagnosticChannel\n')
body=actual[actual.index('/- Unexecuted focused audit draft.'):].removesuffix('\nend LightEFTBridgeAuditDiagnosticChannel\n')
body=re.sub(r'^  LightEFTBridgeAuditTiming.mark "[a-z-]+"\n','',body,flags=re.M)
assert body==old[old.index('/- Unexecuted focused audit draft.'):],'Traversal/TSV/PASS delta'
assert all('LightEFTBridgeAuditTiming.mark' not in line for line in actual.splitlines() if line.startswith('    '))
helpers=actual[actual.index('private partial def appendNat'):actual.index('private def hexKey')]
assert helpers in (R/p.FIXTURE).read_text()
assert (R/p.ORIGINAL).read_text()==p.base(p.ORIGINAL)
for name in ['child_runner.py','pilot_child.py','ci_receipts.py','audit_check.py','output_guards.py','finite_contract.py','prior_guard.py','same_run.py']:
    for prefix in [p.BRIDGE,'checkpoints/light-eft-canonical-output-adapter-20261020/','checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/']:
        path=prefix+name
        if (R/path).exists():assert (R/path).read_text()==p.base(path),path
runner=(R/'checkpoints/light-eft-canonical-output-adapter-20261020/child_runner.py').read_text()
assert 'stderr=subprocess.STDOUT' in runner
def functions(text):return {n.name:ast.dump(n,include_attributes=False) for n in ast.walk(ast.parse(text)) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}
before=functions(p.base(p.BRIDGE+'bridge_context.py'));after=functions((B/'bridge_context.py').read_text())
assert before.keys()==after.keys() and all(before[n]==after[n] for n in before if n not in {'__init__','before_child','after_child'})
before=functions(p.base(p.BRIDGE+'ci_gate.py'));after=functions((B/'ci_gate.py').read_text())
assert set(after)-set(before)=={'fixture_policy'}
assert all(before[n]==after[n] for n in before if n not in {'bound_spec','build_plans','finite_scope','verify_schedule'})
assert 'policy.verify_schedule(' in (R/'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/same_run.py').read_text()
names=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019','light-eft-canonical-output-adapter-20261020',
       'light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']
extra={p.BRIDGE+'bridge_fixture.py',p.FIXTURE,p.COMPOSITE,p.ORIGINAL};bound=0;changed=[]
for i,name in enumerate(names):
    rel='checkpoints/'+name+'/ci-spec.json';a=json.loads(p.base(rel));b=json.loads((R/rel).read_text());e=copy.deepcopy(a)
    if i==3:
        proof=next(r for r in a['sources'] if r['role']=='bridge')
        e['sources']=[proof,row(p.AUDIT,role='audit'),row(p.COMPOSITE,role='resolver'),row(p.FIXTURE,role='key_fixture'),row(p.ORIGINAL,role='original_resolver')]
        f.validate_sources(R,b)
    if i>=3:e['engine_files']=[row(path) for path in sorted({r['path'] for r in a['engine_files']}|extra)]
    assert b==e,'Unexpected scope/path/resource/spec delta: '+rel
    if a!=b:changed.append(rel)
    src=b['sources'];src=list(src.values()) if isinstance(src,dict) else src
    for r in [*src,*b['dependencies'],*b['engine_files']]:
        assert all(r[k]==row(r['path'])[k] for k in ['path','bytes','sha256']),r['path'];bound+=1
assert len(changed)==2
allowed={p.AUDIT,p.BRIDGE+'bridge_fixture.py',p.BRIDGE+'bridge_context.py',p.BRIDGE+'ci_gate.py',p.BRIDGE+'test_bridge_contract.py',*changed}
paths=set(git('diff','--name-only',p.BASE).decode().splitlines())|set(git('ls-files','--others','--exclude-standard').decode().splitlines())
assert all(path in allowed or path.startswith(str(H.relative_to(R))+'/') for path in paths),paths-allowed
for q in [*H.glob('*.py'),B/'bridge_fixture.py']:ast.parse(q.read_text())
git('diff','--check',p.BASE)
print(json.dumps(dict(status='PASS_BRIDGE_SOURCE_PORT_ONLY',baseline=p.BASE,audit=row(p.AUDIT),fixture=row(p.FIXTURE),
    collision_namespace='byte-identical to source-reviewed and full-job-elaborated70492ce7 decoder',
    traversal_exports_PASS='restored byte-identically after removing markers',phases=len(labels),max_diagnostic_bytes=MAX_BYTES,
    stderr='standalone scoped option before first command; inherited raw merge unchanged',
    fixture_gate='mandatory in existing resolve child; live, persisted and batch handoff checks',
    production_binding_rows=bound,changed_specs=changed,limits_workflows_authorities_and_other_audits='unchanged',
    native_bridge_elaboration='not attempted',isolated_speedup='not established',compiler_push_CI=False,reservation='not acquired'),indent=2))
