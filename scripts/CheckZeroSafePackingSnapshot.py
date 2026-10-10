from pathlib import Path
import hashlib,json
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["component_sources"])==251
for name,h in m["component_sources"].items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((p/"verification/ZeroSafePackingSmoke.lean").read_bytes()).hexdigest()=="d4dcb1a40639d28266f42315edea7d00d33b525d45b30197a7a9c190ef93331e"
print("PASS 251 inherited component hashes and new zero-safe packing fixture source")
