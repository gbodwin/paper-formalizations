"""Offline finite prerequisite authority, then unchanged acyclic spec cascade."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parent;R=H.parents[1]
D=R/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019'
sys.path.insert(0,str(D))
import ci_text_fixture as fixture
def row(path):
    p=R/path;raw=p.read_bytes()
    return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
p=D/'ci-spec.json';d=json.loads(p.read_text())
for key,path in [('resolver',fixture.COMPOSITE),('serialization_fixture',fixture.FIXTURE),('original_resolver',fixture.ORIGINAL)]:
    d['sources'][key]=row(path)
p.write_text(json.dumps(d,indent=2)+'\n')
extra=[str(D.relative_to(R))+'/ci_text_fixture.py',fixture.COMPOSITE,fixture.FIXTURE,fixture.ORIGINAL]
for name in ['light-eft-joint-flag-ci-extension-revision-20261019','light-eft-canonical-output-adapter-20261020',
             'light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']:
    p=R/'checkpoints'/name/'ci-spec.json';d=json.loads(p.read_text())
    paths={r['path'] for r in d['engine_files']}|set(extra)
    d['engine_files']=[row(path) for path in sorted(paths)]
    p.write_text(json.dumps(d,indent=2)+'\n')
subprocess.run([sys.executable,'-B',str(R/'checkpoints/light-eft-sequential-validation-schedule-20261021/refresh_bindings.py')],check=True)
