import sys,re
from pathlib import Path
lines=[s for s in Path(sys.argv[1]).read_text().splitlines() if s.startswith("PASS ")]
patterns=[r"PASS weighted binary preparation; operations=([1-9][0-9]*)",r"PASS weighted all seven tickets; counts=3,4",r"PASS weighted rejection and exhaustion; operations=([1-9][0-9]*),([1-9][0-9]*),([1-9][0-9]*)",r"PASS retained tape effects and entering ledger; operations=([1-9][0-9]*),([1-9][0-9]*),16",r"PASS all four weighted and tape execution groups"]
assert len(lines)==len(patterns),lines
for s,p in zip(lines,patterns):assert re.fullmatch(p,s),s
print("PASS four weighted/tape groups and printed charge checks")
