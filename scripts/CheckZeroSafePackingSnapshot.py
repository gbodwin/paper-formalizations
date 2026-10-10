from pathlib import Path
import hashlib,json
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["component_sources"])==251
for name,h in m["component_sources"].items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((p/"verification/ZeroSafePackingSmoke.lean").read_bytes()).hexdigest()=="65dc0e466fb03bb2f216d9f61ffb32d2a1e0895049f663afb6ccf547f0f6df6e"
print("PASS 251 inherited component hashes and new zero-safe packing fixture source")
