"""Read-only reconciliation of an extracted artifact; starts no Lean processes."""
from pathlib import Path
import sys,json,hashlib,csv
p=Path(sys.argv[1]);out=Path(sys.argv[2])
source='c189a4e93786b47c7dbc23146c6b44a5b9cc75dc';trigger='3e3e887c39eb3905ccb7db68c5ea81560e627912'
for row in json.loads((p/'evidence-sha256.json').read_text()):
 assert hashlib.sha256((p/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
result=json.loads((p/'result.json').read_text());assert result['result']=='PASS' and result['tested_source']==source and result['ci_commit']==trigger
cmd=[json.loads(s) for s in (p/'commands.jsonl').read_text().splitlines()]
assert all(c['exit']==0 for c in cmd)
builds=[c for c in cmd if c['label'].startswith('compile-')];replays=[c for c in cmd if c['label'].startswith('checker-')]
assert len(builds)==39 and len(replays)==38
assert sum('-DwarningAsError=true' in c['argv'] for c in builds)==16
for c in replays:assert (p/(c['label']+'.log')).read_text().strip()=='replaying '+c['label'].removeprefix('checker-')
warning=json.loads((p/'warning-classification.json').read_text());assert len(warning)==36
rows=list(csv.DictReader((p/'recursive-dependencies.tsv').open(),delimiter='\t'))
roots=list(csv.DictReader((p/'actual-owner-inventory.tsv').open(),delimiter='\t'))
assert len(rows)==19646 and len(roots)==373
assert {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
assert not json.loads((p/'preflight.json').read_text())['other_active_runs']
summary=dict(result='PASS',source=source,trigger=trigger,commands=len(cmd),builds=len(builds),strict_builds=16,replays=len(replays),inherited_warnings=len(warning),roots=len(roots),recursive_constants=len(rows),opaque_bodies=sum(r['kind']=='opaque' for r in rows),artifact_file_hashes_verified=True)
out.write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
