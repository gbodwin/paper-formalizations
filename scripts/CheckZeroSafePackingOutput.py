import sys,re
from pathlib import Path
lines=[s for s in Path(sys.argv[1]).read_text().splitlines() if s.startswith("PASS ")]
patterns=[r"PASS zero-safe selector branches; operations=([1-9][0-9]*),21,([1-9][0-9]*),([1-9][0-9]*)",r"PASS zero-safe provider metadata and bottleneck; operations=([1-9][0-9]*)",r"PASS zero-safe cached packing and final draw; operations=([1-9][0-9]*); calls=1; bits=1",r"PASS all three zero-safe packing execution groups"]
assert len(lines)==len(patterns),lines
for s,p in zip(lines,patterns):assert re.fullmatch(p,s),s
print("PASS three zero-safe packing groups and printed charge checks")
