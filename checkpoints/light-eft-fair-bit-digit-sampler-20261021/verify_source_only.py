"""Source inventory preservation only. Never starts Lean, admission, push or CI."""
from pathlib import Path
import hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE='9a7e9d8783e4415a59f5f968acca00509c66ebb8'
git=lambda *a:subprocess.check_output(['git','-C',str(ROOT),*a])
m=json.loads((HERE/'SOURCE-BINDINGS.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
assert m['parent']==BASE and m['status']=='UNELABORATED_SOURCE_ONLY'
assert len(m['project_import_union'])==83
assert len({r['module'] for r in m['project_import_union']})==83
for r in [*m['checkpoint_files'],*m['project_import_union'],*m['reviewed_flat_files'],*m['primary_sources']]:
    p=Path(r['path']);b=(p if p.is_absolute() else ROOT/p).read_bytes()
    assert (len(b),sha(b))==(r['bytes'],r['sha256']),r['path']
for r in [*m['reviewed_flat_files'],*[r for r in m['project_import_union'] if r['origin']!='new_sampler']]:
    assert git('show',BASE+':'+r['path'])==(ROOT/r['path']).read_bytes()
for r in m['primary_sources']:
    assert all(s in Path(r['path']).read_text() for s in r['markers'])
prefix=str(HERE.relative_to(ROOT))+'/'
expected={prefix+p for p in m['checkpoint_relative_files']}
changed=set()
for line in git('diff','--name-status',BASE).decode().splitlines():
    state,p=line.split('\t');assert state=='A' and p in expected;changed.add(p)
untracked=set(git('ls-files','--others','--exclude-standard').decode().splitlines())
assert changed|untracked==expected and not changed&untracked
counts=[]
for name,n in [('FairBitDigitSampler.lean',20),('IndependentTapeLaw.lean',6)]:
    text=(HERE/'staged/LightEFTFairBitStage'/name).read_text()
    assert len(re.findall(r'^theorem ',text,re.M))==n
    assert not re.search(r'\b(sorry|admit)\b|^\s*(axiom|unsafe|partial|opaque)\s',text,re.M)
    assert not re.search(r'skipKernelTC|implemented_by|ofReduceBool',text)
    counts.append(n)
flat=ROOT/'checkpoints/light-eft-flat-tape-law-20261021/staged/LightEFTFlatTapeStage/FlatTapeLaw.lean'
assert sha(flat.read_bytes())=='b1d3beaa25f9528611b7ae85c86a41e4feda57b53c62b3a1ccb2cf6c28360ee9'
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_SOURCE_PRESERVATION_ONLY',parent=BASE,
    additive_files=len(expected),new_theorem_bodies=sum(counts),combined_theorem_bodies=36,
    source_derived_project_imports=83,including_final_target=84,reviewed_flat_files_unchanged=6,
    accepted_gate_unchanged=True,kernel_acceptance=False,independent_review='pending',
    no_compiler_push_CI=True),indent=2))
