"""Reconcile extracted directed CI evidence without launching Lean."""
from pathlib import Path
import json,hashlib,csv,sys
p=Path(sys.argv[1]);out=Path(sys.argv[2])
for x in json.loads((p/'evidence-sha256.json').read_text()):
 assert hashlib.sha256((p/x['path']).read_bytes()).hexdigest()==x['sha256'],x['path']
result=json.loads((p/'result.json').read_text())
assert result['tested_source']=='58116f153e48e57a055767cabfd1bc89f622214d' and result['result']=='PASS'
cmds=[json.loads(x) for x in (p/'commands.jsonl').read_text().splitlines()]
assert len({x['attempt_id'] for x in cmds})==len(cmds)
assert len({(x['lock_device'],x['lock_inode']) for x in cmds})==1
for x in cmds:
 assert x['exit']==0 and x['child_reaped'] and x['child_pid'] and x['supervisor_pid']
 assert x['lock_acquired_monotonic_ns']<=x['start_monotonic_ns']<=x['end_monotonic_ns']
 assert json.loads((p/'attempts'/x['attempt_id']/'receipt.json').read_text())==x
for a,b in zip(cmds,cmds[1:]):assert a['end_monotonic_ns']<=b['lock_acquired_monotonic_ns']
builds=[x for x in cmds if x['label'].startswith('compile-')];checks=[x for x in cmds if x['label'].startswith('checker-')]
assert len(builds)==len(checks)==10
assert sum('-DwarningAsError=true' in x['argv'] for x in builds)==5
for x in checks:assert (p/(x['label']+'.log')).read_text().strip()=='replaying '+x['label'].removeprefix('checker-')
assert sum(x['count'] for x in json.loads((p/'warning-classification.json').read_text()))==14
roots=list(csv.DictReader((p/'actual-owner-inventory.tsv').open(),delimiter='\t'))
rows=list(csv.DictReader((p/'recursive-dependencies.tsv').open(),delimiter='\t'))
assert len(roots)==119 and len(rows)==18093
assert {x['name'] for x in rows if x['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
r={'PASS':True,'commands':len(cmds),'builds':10,'singleton_replays':10,'strict_builds':5,'inherited_warnings':14,'roots':119,'recursive_constants':18093,'one_lock_inode':True,'unique_attempts':True,'timestamps_nonoverlap':True,'all_children_reaped':True}
out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
