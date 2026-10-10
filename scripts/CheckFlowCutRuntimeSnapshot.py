#!/usr/bin/env python3
"""Bind the exact290 sources and the body-preserving eight-case runtime driver."""
from pathlib import Path
import hashlib,json,re
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
sha=lambda data: hashlib.sha256(data).hexdigest()
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["component_sources"]) == 290
for name,h in m["component_sources"].items():
    assert sha((p/name).read_bytes()) == h, name
original=(p/"verification/RuntimeGraphCombinedSmoke.lean").read_text()
driver=(p/"verification/RuntimeGraphCombinedMain.lean").read_text()
assert sha(original.encode()) == "5f4b7ab9795c66743f698323bd2c27f72439a2ede27308fb78c14bc646b3b97f"
assert sha(driver.encode()) == "9da0d052c5057612316410cf610198290373bc9680d796124d8d97a62eb61059"
body=driver.split("\ndef main : IO Unit := do\n")[0]
assert len(re.findall(r"^def runCase[1-8] : IO Unit := do$",body,re.M)) == 8
repairs=json.loads((p/"verification/runtime-elaboration-repairs.json").read_text())
assert repairs["driver_sha256"] == sha(driver.encode())
for edit in reversed(repairs["elaboration_repairs"]):
    assert body.count(edit["replacement"]) == 1
    body=body.replace(edit["replacement"],edit["original"])
assert re.sub(r"^def runCase[1-8] : IO Unit := do$","#eval do",body,flags=re.M) == original
print("PASS exact290 proof hashes and eight runtime bodies with explicit elaboration repairs")
