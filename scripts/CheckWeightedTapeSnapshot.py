from pathlib import Path
import hashlib,json
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["component_sources"])==290
for name,h in m["component_sources"].items():
 assert hashlib.sha256((p/name).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((p/"verification/WeightedTapeExecutionSmoke.lean").read_bytes()).hexdigest()=="b24364d5d71ab2ede94d0ab7bb1dabff02617d700678903388b664d074a43ec6"
print("PASS 290 inherited component hashes and new weighted/tape fixture source")
