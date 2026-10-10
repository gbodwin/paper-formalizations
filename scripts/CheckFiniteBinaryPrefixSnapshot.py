from pathlib import Path
import json,hashlib
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/finite-binary-prefix.json").read_text())
assert len(m["baseline_sources"])==193
for path,h in m["baseline_sources"].items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h,path
for name,h in m["dependency_sources"].items():assert hashlib.sha256((p/(name.replace(".","/")+".lean")).read_bytes()).hexdigest()==h,name
print("PASS193 unchanged baseline sources and",len(m["dependency_sources"]),"exact finite-prefix closure hashes")
