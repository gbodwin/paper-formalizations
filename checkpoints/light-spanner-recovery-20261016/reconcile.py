"""Reconcile saved verification evidence without invoking Lean."""
from pathlib import Path
import csv,hashlib,json,re
B=Path(__file__).resolve().parent;E=B/'evidence';ROOT=B.parents[1]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((E/'evidence-sha256.json').read_text())
for r in manifest:
 p=E/r['path'];assert p.resolve().is_relative_to(E.resolve());assert p.stat().st_size==r['bytes'] and h(p)==r['sha256']
inv=json.loads((E/'module-inventory.json').read_text());result=json.loads((E/'result.json').read_text());assert result['PASS']
records=[json.loads(x) for x in (E/'commands.jsonl').read_text().splitlines()]
assert len(records)==124 and len({r['attempt_id'] for r in records})==124
assert len({(r['lock_device'],r['lock_inode']) for r in records})==1
for a,b in zip(records,records[1:]):assert a['end_monotonic_ns']<=b['lock_acquired_monotonic_ns']<=b['start_monotonic_ns']
failed=[r for r in records if r['exit']!=0];assert len(failed)==1 and failed[0]['attempt_id']=='12a6b6d7843c4c0c9c89ec10282e63cf'
for r in records:
 assert r['child_reaped'] and r['child_pid'] and r['submitted_sources']
 p=E/'attempts'/r['attempt_id'];assert json.loads((p/'receipt.json').read_text())==r
 for s in r['submitted_sources']:
  snap=p/(s['sha256']+'.lean');assert h(snap)==s['sha256'] and snap.stat().st_size==s['bytes']
  # Find submitted sources relative to the original recovered worktree.
  rel=s['path'].split('/light-spanner-verification/',1)[1];assert h(ROOT/rel)==s['sha256']
assert [r['label'][8:] for r in records if r['label'].startswith('compile-')]==inv['compile_order']
assert [r['label'][7:] for r in records if r['label'].startswith('replay-') and r['exit']==0]==inv['replays']
for n in inv['replays']:assert (E/('replay-'+n+'.log')).read_text().strip()=='replaying '+n
w=json.loads((E/'warning-classification.json').read_text());assert len(w)==22 and all(x['historical_header_matches'] for x in w)
assert sum(len(re.findall(r'^.+:\d+:\d+: warning:',p.read_text(),re.M)) for p in E.glob('compile-*.log'))==22
roots=list(csv.DictReader((E/'actual-owner-inventory.tsv').open(),delimiter='\t'))
rows=list(csv.DictReader((E/'recursive-dependencies.tsv').open(),delimiter='\t'))
assert {r['owner'] for r in roots}==set(inv['replays']);assert len(roots)==result['roots'] and len(rows)==result['recursive_constants']
assert {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
by_name={r['name']:r for r in rows};seen=set();todo=[r['name'] for r in roots]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);r=by_name[n]
 for key in ['typeDependencies','bodyDependencies']:todo.extend(x for x in r[key].split(',') if x)
assert seen==set(by_name)
m=json.loads((E/'audit-export/manifest.json').read_text());data=b''.join((E/'audit-export'/p['path']).read_bytes() for p in m['parts'])
assert data==(E/'recursive-dependencies.tsv').read_bytes() and len(data)==m['bytes'] and hashlib.sha256(data).hexdigest()==m['sha256']
print(json.dumps({'PASS':True,'manifest_entries':len(manifest),'receipts':len(records),'preserved_failed_attempts':len(failed),'roots':len(roots),'closure':len(rows),'chunks':len(m['parts'])},indent=2))
