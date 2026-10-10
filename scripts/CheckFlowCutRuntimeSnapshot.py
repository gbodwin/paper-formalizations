#!/usr/bin/env python3
"""Bind the exact193 sources and the body-preserving eight-case runtime driver."""
from pathlib import Path
import hashlib,json,re
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
sha=lambda data: hashlib.sha256(data).hexdigest()
m=json.loads((p/"verification/component-verification.json").read_text())
assert len(m["sources"]) == 194
for name,h in m["sources"].items():
    assert sha((p/name).read_bytes()) == h, name
original=(p/"verification/RuntimeGraphCombinedSmoke.lean").read_text()
driver=(p/"verification/RuntimeGraphCombinedMain.lean").read_text()
assert sha(original.encode()) == "5f4b7ab9795c66743f698323bd2c27f72439a2ede27308fb78c14bc646b3b97f"
assert sha(driver.encode()) == "1fdc6c6216d7ce703acf06780664dcde3d8ebd794eed347c8df362a55324e7ac"
body=driver.split("\ndef main : IO Unit := do\n")[0]
assert len(re.findall(r"^def runCase[1-8] : IO Unit := do$",body,re.M)) == 8
assert re.sub(r"^def runCase[1-8] : IO Unit := do$","#eval do",body,flags=re.M) == original
print("PASS exact193 proof hashes and eight unchanged runtime bodies")
