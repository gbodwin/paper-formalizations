"""Offline refresh in the existing acyclic producer-spec order; no execution."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;R=H.parents[1]
NAMES=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
       'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020',
       'light-eft-fair-bit-batch-ci-adapter-20261021']
def row(p):
    raw=p.read_bytes();return dict(path=str(p.relative_to(R)),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
extra=[R/'.github/workflows/light-eft-fair-bit-focused.yml',R/'scripts/KernelCheck.sh',H/'workflow_identity.py',H/'acceptance.py']
for i,n in enumerate(NAMES):
    p=R/'checkpoints'/n/'ci-spec.json';d=json.loads(p.read_text())
    paths={R/r['path'] for r in d['engine_files']}|set(extra)
    if i==4:paths.update(q for q in H.iterdir() if q.is_file())
    d['engine_files']=[row(q) for q in sorted(paths)]
    p.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps(dict(status='OFFLINE_BINDING_REFRESH_ONLY',specs=len(NAMES))))
