from pathlib import Path
import hashlib,json
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["component_sources"])==290
for name,h in m["component_sources"].items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((p/"verification/GraphExecutionSmoke.lean").read_bytes()).hexdigest()=="665cfe0d3c329f7ff13ce2f9aff2727b7bf34ad80192ab53fd52d1031a416717"
print("PASS 290 inherited component hashes and new graph fixture source")
