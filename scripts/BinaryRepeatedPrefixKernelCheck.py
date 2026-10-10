from pathlib import Path
import json,subprocess
p=Path("Improved Upper Bounds for the Directed Flow-Cut Gap/verification/binary-repeated-prefix.json")
m=json.loads(p.read_text())
for name in sorted(m["dependency_sources"]):
 subprocess.run(["lake","env","leanchecker","-v",name],check=True)
print("PASS kernel replay of",len(m["dependency_sources"]),"repetition probability closure modules")
