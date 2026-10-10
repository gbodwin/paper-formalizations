from pathlib import Path
import hashlib,json
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/reference-recovery.json").read_text())
for name,h in m["dependency_sources"].items():
 assert hashlib.sha256((p/(name.replace(".","/")+".lean")).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((p/"verification/ImmutableReferenceSimulationSmoke.lean").read_bytes()).hexdigest()==m["fixture_sha256"]
print("PASS exact recovered reference source and",len(m["dependency_sources"]),"source closure hashes")
