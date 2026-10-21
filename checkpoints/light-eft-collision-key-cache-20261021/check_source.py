"""Offline exact c46-relative transform, finite authority and preservation check."""
import ast,copy,hashlib,json,subprocess
from pathlib import Path
import repair as p
R=p.R;H=p.H
git=lambda *args:subprocess.check_output(['git','-C',str(R),*args])
def row(path):
    raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
for path,text in p.expected().items():assert (R/path).read_text()==text,path
old=p.base(p.AUDIT);new=(R/p.AUDIT).read_text()
# All scan coverage, classifier rules, reader/free code, traversal, stdout and
# command-completion behavior are byte-identical except the finite key sites.
assert new.count('IO.getStdout')==old.count('IO.getStdout')==1
assert new.split('end LightEFTAuditCollision',1)[1]==old.split('end LightEFTAuditCollision',1)[1]
for a,b in [('private partial def appendNat','private def hexKey'),
            ('private unsafe def readPart','private def addClaim'),
            ('private def addClaim','@[noinline] private def consumeNames'),
            ('@[noinline] private def countRegions','@[noinline] private unsafe def scanOne')]:
    before=old[old.index(a):old.index(b)];after=new[new.index(a):new.index(b)]
    if a.startswith('private partial'):after=after.replace(p.HELPER,'')
    assert before==after,a
assert 'KeyCache' not in new.split('structure State where',1)[1].split('/- Same predicate',1)[0]
assert new.index(p.SEED)<new.index('  let parts : OwnedParts :=')<new.index('    loadParts parts file')
assert new.count('rememberKey keys info.name')==1
assert new.count('keyFor keys name')==2 and new.count('keyFor keys info.name')==1
fixture=(R/p.FIXTURE).read_text()
helper=new[new.index('private partial def appendNat'):new.index('private def hexKey')]
assert helper in fixture
names=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
       'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020',
       'light-eft-fair-bit-batch-ci-adapter-20261021']
bound=0;changed=[]
for index,name in enumerate(names):
    rel='checkpoints/'+name+'/ci-spec.json';a=json.loads(p.base(rel));b=json.loads((R/rel).read_text());e=copy.deepcopy(a)
    if index==1:
        for key,path in [('audit',p.AUDIT),('serialization_fixture',p.FIXTURE),('resolver',p.COMPOSITE)]:e['sources'][key]=row(path)
    e['engine_files']=[row(r['path']) for r in a['engine_files']]
    assert b==e,'Contract/path-set/resource drift: '+rel
    if a!=b:changed.append(rel)
    source=b['sources'];source=list(source.values()) if isinstance(source,dict) else source
    for r in [*source,*b['dependencies'],*b['engine_files']]:
        assert all(r[k]==row(r['path'])[k] for k in ['path','bytes','sha256']),r['path'];bound+=1
assert len(changed)==4
paths=set(git('diff','--name-only',p.BASE).decode().splitlines())|set(git('ls-files','--others','--exclude-standard').decode().splitlines())
allowed=set(p.expected())|set(changed)
assert all(path in allowed or path.startswith(str(H.relative_to(R))+'/') for path in paths),paths-allowed
for q in H.glob('*.py'):ast.parse(q.read_text())
git('diff','--check',p.BASE)
print(json.dumps(dict(status='PASS_SOURCE_ONLY',baseline=p.BASE,production_binding_rows=bound,
    changed_specifications=changed,audit=row(p.AUDIT),fixture=row(p.FIXTURE),
    classifier_coverage_cleanup_traversal_output_completion='unchanged',
    limits_workflows_same_job_authority_aggregate='unchanged',
    fixture_gate='existing bounded resolve child; exact hash mandatory before replay/audit',
    native_elaboration='not attempted',performance='unmeasured',compiler_push_CI=False),indent=2))
