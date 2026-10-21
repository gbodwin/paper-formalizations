"""Finite offline bridge-source/engine then batch-consumer hash cascade only."""
from pathlib import Path
import hashlib,json
import port
R=port.R;B=R/port.BRIDGE
def row(path,**extra):
    raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),**extra)
p=B/'ci-spec.json';d=json.loads(p.read_text());old={r['role']:r for r in d['sources']}
d['sources']=[old['bridge'],row(port.AUDIT,role='audit'),row(port.COMPOSITE,role='resolver'),
              row(port.FIXTURE,role='key_fixture'),row(port.ORIGINAL,role='original_resolver')]
extra={port.BRIDGE+'bridge_fixture.py',port.FIXTURE,port.COMPOSITE,port.ORIGINAL}
d['engine_files']=[row(path) for path in sorted({r['path'] for r in d['engine_files']}|extra)]
p.write_text(json.dumps(d,indent=2)+'\n')
p=R/'checkpoints/light-eft-fair-bit-batch-ci-adapter-20261021/ci-spec.json';d=json.loads(p.read_text())
d['engine_files']=[row(path) for path in sorted({r['path'] for r in d['engine_files']}|extra)]
p.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps(dict(status='OFFLINE_BRIDGE_BINDING_REFRESH_ONLY',specifications=2)))
