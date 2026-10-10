from pathlib import Path
import hashlib,json
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["component_sources"])==251
for name,h in m["component_sources"].items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((p/"verification/WeightedTapeExecutionSmoke.lean").read_bytes()).hexdigest()=="4a092b118706615b0e8d7cb6c1efcb0691471f95258d8723b108f97495018711"
print("PASS 251 inherited component hashes and new weighted/tape fixture source")
