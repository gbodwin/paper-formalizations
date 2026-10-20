"""Finite static source/byte/AST checks only; never imports the execution gate."""
from pathlib import Path
import ast, collections, hashlib, json, subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE='eab618b2e043bd5509e814357c1b8c9305ac74cd'
PAID=ROOT/'checkpoints/light-eft-paid-focused-adapter-20261020'
ENGINE=ROOT/'checkpoints/light-eft-canonical-output-adapter-20261020'
PLAN=ROOT/'checkpoints/light-eft-paid-joint-bridge-ci-plan-20261020'
spec=json.loads((HERE/'ci-spec.json').read_text())
contract=ast.literal_eval((HERE/'finite_contract.py').read_text().split('CONTRACT=',1)[1])
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.check_output(['git','-C',str(ROOT),*a])

assert spec['project_imports']==80 and spec['project_modules_including_target']==81
assert collections.Counter(r['origin'] for r in spec['dependencies'])=={'ordinary_build':77,'paid':2,'decoder':1}
assert {r['module'] for r in spec['dependencies']}==set(contract['imports'][contract['modules'][0]])
assert len(spec['required_theorem_roots'])==12 and len(spec['pins'])==9
assert spec['resource_contract']==contract['resources']
for r in [*spec['sources'],*spec['dependencies'],*spec['engine_files']]:
    b=(ROOT/r['path']).read_bytes();assert (len(b),sha(b))==(r['bytes'],r['sha256']),r['path']
assert (ROOT/'.github/workflows/lean.yml').read_bytes()==(PLAN/'PROPOSED-WORKFLOW.yml').read_bytes()
assert (HERE/'staged/BridgeAudit.lean').read_bytes()==(PLAN/'proposed/staged/BridgeAudit.lean').read_bytes()
assert (HERE/'staged/ResolveBridgeTarget.lean').read_bytes()==(PLAN/'proposed/staged/ResolveBridgeTarget.lean').read_bytes()
assert (HERE/'audit_check.py').read_bytes()==(PAID/'audit_check.py').read_bytes()
for r in json.loads((PLAN/'PLAN.json').read_text())['template_bindings']:
    b=(ROOT/r['path']).read_bytes();assert sha(b)==r['sha256'],r['path']

def functions(path):
    tree=ast.parse(Path(path).read_text())
    return {n.name:ast.dump(n,include_attributes=False) for n in ast.walk(tree) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef))}

old=functions(PAID/'output_guards.py');new=functions(HERE/'output_guards.py')
assert set(old)==set(new)
assert all(old[n]==new[n] for n in old if n!='focused_contract')
old=functions(PAID/'focused_context.py');new=functions(HERE/'bridge_context.py')
allowed={'__init__','spec','verify','before_child'}
assert set(old)==set(new) and all(old[n]==new[n] for n in old if n not in allowed)
for name in ['prepare_child','preexec','after_child','check_selection','visible_gate','complete_log','finish']:
    assert old[name]==new[name],name
normalized=(HERE/'bridge_context.py').read_text()
normalized=normalized.replace('"""Finite bridge context; accepted prepare/preexec/lifecycle operations retained."""', '"""Finite two-module shared-package context; resource/lifecycle engine is reused."""')
normalized=normalized.replace('identity,inputs,inventory,classified,prior_trees,prior_protected):','identity,inputs,inventory,classified):',1)
normalized=normalized.replace('  self.prior_trees=prior_trees;self.prior_protected=prior_protected\n','',1)
normalized=normalized.replace("for case in [m.rsplit('.',1)[-1] for m in CONTRACT['modules']]:", "for case in ['PaidFlagSerialization','PaidFlagSampleComposition','PaidFlagFixtures']:",1)
normalized=normalized.replace('protected={**self.prior_protected,**self.protected(),','protected={**self.protected(),',1)
normalized=normalized.replace('protected=protected,prior_trees=self.prior_trees,','protected=protected,',1)
normalized=normalized.replace("focused_module=p['module'],CI_identity=self.identity)","focused_module=p['module'])",1)
normalized=normalized.replace("CI_identity=self.identity,workflow_job='check',dependency_qualification=",'CI_identity=self.identity,dependency_qualification=',1)
assert normalized==(PAID/'focused_context.py').read_text(), 'Unexpected context change beyond finite metadata/producer protection'

paths=['checkpoints/light-eft-paid-focused-adapter-20261020/ci-spec.json',
       'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019/ci-spec.json',
       'checkpoints/light-eft-canonical-output-adapter-20261020/ci-spec.json']
for path in paths:
    before=json.loads(git('show',BASE+':'+path));after=json.loads((ROOT/path).read_text())
    expected=json.loads(json.dumps(before))
    for i,r in enumerate(expected['engine_files']):
        if r['path']=='.github/workflows/lean.yml' or path==paths[-1] and r['path']==paths[1]:
            b=(ROOT/r['path']).read_bytes();expected['engine_files'][i]=dict(path=r['path'],bytes=len(b),sha256=sha(b))
    assert expected==after,path
changed=git('diff','--name-only',BASE).decode().splitlines()
prefix=str(HERE.relative_to(ROOT))+'/'
assert all(p in paths+['.github/workflows/lean.yml'] or p.startswith(prefix) for p in changed),changed
untracked=git('ls-files','--others','--exclude-standard').decode().splitlines()
assert all(p.startswith(prefix) for p in untracked)
proof=next(r for r in spec['sources'] if r['role']=='bridge')
assert proof['sha256']=='b3ba8f73669c5eea04e58cdb545866382771b6e12537a32cd437d8f13d5b7664'
for p in HERE.glob('*.py'):ast.parse(p.read_text())
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_STATIC_IMPLEMENTATION_ONLY',bound_sources=len(spec['sources']),
    bound_dependencies=len(spec['dependencies']),bound_engine_and_producer_files=len(spec['engine_files']),
    unchanged_template_bindings=18,old_specs_binding_only=True,workflow_equals_reviewed_proposal=True,
    accepted_engine_and_critical_context_hooks_unchanged=True,output_guard_changes='finite singleton/prior-tree authority only',
    owned_collision_and_recursive_audit_unchanged=True,reviewed_proof_unchanged=True,
    compiler_or_CI_or_push_launched=False),indent=2))
