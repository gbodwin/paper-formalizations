"""Offline audit-source binding and existing acyclic specification cascade only."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parent;R=H.parents[1]
P=R/'checkpoints/light-eft-joint-flag-ci-extension-revision-20261019/ci-spec.json'
d=json.loads(P.read_text());row=d['sources']['audit'];raw=(R/row['path']).read_bytes()
row.update(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest());P.write_text(json.dumps(d,indent=2)+'\n')
subprocess.run([sys.executable,'-B',str(R/'checkpoints/light-eft-sequential-validation-schedule-20261021/refresh_bindings.py')],check=True)
