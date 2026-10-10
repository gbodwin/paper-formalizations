import sys,re
from pathlib import Path
lines=[s for s in Path(sys.argv[1]).read_text().splitlines() if s.startswith("PASS ")]
patterns=[r"PASS graph primitives and reached-malformed guards",r"PASS graph scans and survivors; operations=([1-9][0-9]*)",r"PASS graph root search and diagonal guard; operations=([1-9][0-9]*)",r"PASS graph matrix and survivor restriction; operations=([1-9][0-9]*),([1-9][0-9]*)",r"PASS graph port decode and full materialization; operations=([1-9][0-9]*),([1-9][0-9]*)",r"PASS all five new graph execution groups"]
assert len(lines)==len(patterns),lines
for s,p in zip(lines,patterns):assert re.fullmatch(p,s),s
print("PASS five graph groups and positive printed charge checks")
