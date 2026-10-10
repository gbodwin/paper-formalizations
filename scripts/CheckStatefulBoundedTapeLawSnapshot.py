from pathlib import Path
import json,hashlib
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/stateful-bounded-tape-law.json").read_text())
b=json.loads((p/"verification/component-verification.json").read_text())
assert len(b["component_sources"])==251
for path,h in b["component_sources"].items():assert hashlib.sha256((p/path).read_bytes()).hexdigest()==h,path
for name,h in m["dependency_sources"].items():assert hashlib.sha256((p/(name.replace(".","/")+".lean")).read_bytes()).hexdigest()==h,name
print("PASS251 base sources and",len(m["dependency_sources"]),"exact probability-closure hashes")
