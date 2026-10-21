"""Exact source-only delta and production binding check; no admission or launch."""
from pathlib import Path
import ast,copy,hashlib,json,subprocess,sys
H=Path(__file__).resolve().parent;R=H.parents[1]
BASE='edd7bedf120720643e71cf56f3895a4eb126d34a'
D='checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
sys.path.insert(0,str(R/D))
import ci_policy,ci_text_fixture as f
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
def row(path):
    raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
names=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
       'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']
extra={D+'/ci_text_fixture.py',f.FIXTURE,f.ORIGINAL,f.COMPOSITE};count=0
for i,n in enumerate(names):
    rel='checkpoints/'+n+'/ci-spec.json';before=json.loads(git('show',BASE+':'+rel));actual=json.loads((R/rel).read_text())
    expected=copy.deepcopy(before)
    if i==1:
        for key,path in [('resolver',f.COMPOSITE),('serialization_fixture',f.FIXTURE),('original_resolver',f.ORIGINAL)]:expected['sources'][key]=row(path)
        ci_policy.scope_contract(actual);f.validate_sources(R,actual)
    paths={r['path'] for r in before['engine_files']}|(extra if i else set())
    expected['engine_files']=[row(p) for p in sorted(paths)]
    assert expected==actual,'Unexpected production semantic/path/binding delta: '+rel
    sources=actual['sources'];sources=list(sources.values()) if isinstance(sources,dict) else sources
    for b in [*sources,*actual['dependencies'],*actual['engine_files']]:
        assert all(b[k]==row(b['path'])[k] for k in ['path','bytes','sha256']);count+=1
    if i!=1:assert before['sources']==actual['sources']
# Existing source/evidence/math/audit/fixtures and all workflows are byte-identical.
modified={D+'/'+n for n in ['ci_gate.py','ci_policy.py','ci_receipts.py','test_ci_preexec_repair.py']}
modified.add('checkpoints/light-eft-canonical-output-adapter-20261020/ci_handoff.py')
modified.update('checkpoints/'+n+'/ci-spec.json' for n in names)
paths=set(git('diff','--name-only',BASE).decode().splitlines())|set(git('ls-files','--others','--exclude-standard').decode().splitlines())
assert all(p in modified or p==D+'/ci_text_fixture.py' or p.startswith(str(H.relative_to(R))+'/') for p in paths),paths-modified
for rel in [f.FIXTURE,f.ORIGINAL]:assert (R/rel).read_bytes()==git('show',BASE+':'+rel)
audit='checkpoints/light-eft-joint-flag-assignment-local-repair-20261018/staged/JointAssignmentLawAudit.lean'
assert (R/audit).read_bytes()==git('show',BASE+':'+audit)
for p in [*(H.glob('*.py')),*(R/D).glob('*.py')]:ast.parse(p.read_text())
# Every old complete receipt check remains, with additive prerequisite guards only.
old=git('show',BASE+':'+D+'/ci_receipts.py').decode().splitlines();new=(R/D/'ci_receipts.py').read_text().splitlines()
replacement={' previous=0;ids=set()':' previous=0;ids=set();fixture_passed=False'}
it=iter(new)
for line in old:assert any(candidate==replacement.get(line,line) for candidate in it),'Removed/reordered receipt check: '+line
handoff=(R/'checkpoints/light-eft-canonical-output-adapter-20261020/ci_handoff.py').read_text()
old_handoff=git('show',BASE+':checkpoints/light-eft-canonical-output-adapter-20261020/ci_handoff.py').decode()
assert handoff.replace("    policy.fixture_receipt('resolve',receipts[1],root/'runtime/resolve')\n",'')==old_handoff
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_SOURCE_ONLY',baseline=BASE,production_binding_rows=count,
 fixture='exact reviewed bytes; unelaborated',native_children='unchanged four decoder children',
 wall_CPU_AS_output_admission_workflows='unchanged',existing_receipt_checks='all preserved in order',
 performance='unmeasured',compiler_push_CI=False),indent=2))
