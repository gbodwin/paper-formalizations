"""Read-only reconciliation; does not invoke any compiler or checker."""
from pathlib import Path
import csv,json,hashlib,subprocess,re
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence';OUT=ROOT/'.lake/edges-pilot/lib/lean'
PARENT=ROOT/'checkpoints/light-eft-controller-pilot-20261016';h=lambda b:hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
rows=json.loads((E/'source-graph.json').read_text());state=json.loads((E/'fresh-build-state.json').read_text());assert len(rows)==len(state)==486
rs=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len({r['attempt_id'] for r in rs})==len(rs)
assert len({(r['lock_device'],r['lock_inode']) for r in rs})==1
assert all(r['child_reaped'] for r in rs)
assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(rs,rs[1:]))
for r in rs:
 for s in r['submitted_sources']:
  b=(E/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes();assert len(b)==s['bytes'] and h(b)==s['sha256']
preflights=[json.loads(x) for x in (E/'preflights.jsonl').read_text().splitlines()]
assert {p['attempt_id'] for p in preflights}=={r['attempt_id'] for r in rs} and len(preflights)==len(rs)
for r in rs:
 p=E/'attempts'/r['attempt_id']/'preflight.json'
 assert h(p.read_bytes())==r['preflight_sha256']
 assert json.loads(p.read_text())['attempt_id']==r['attempt_id']
objects=[]
for row in rows:
 n=row['module'];p=ROOT/row['path'];sha=h(p.read_bytes());obj=OUT/Path(*n.split('.')).with_suffix('.olean')
 assert state[n]['inputs']['source_sha256']==sha and state[n]['object_sha256']==h(obj.read_bytes())
 for d,dh in state[n]['inputs']['imports'].items():assert h((OUT/Path(*d.split('.')).with_suffix('.olean')).read_bytes())==dh
 good=[r for r in rs if r['label']=='fresh-compile-'+n and r['exit']==0 and r['submitted_sources'][0]['sha256']==sha];assert good
 raw=(E/'attempts'/good[-1]['attempt_id']/'raw.log').read_text();assert not re.search(r'^.*:\d+:\d+: (warning|error):',raw,re.M)
 objects.append(dict(module=n,path=row['path'],source_sha256=sha,object_path=str(obj),object_sha256=h(obj.read_bytes())))
save(E/'fresh-source-object-hashes.json',objects)
classifications=[]
for r in rs:
 raw=(E/'attempts'/r['attempt_id']/'raw.log').read_text()
 classifications.append(dict(attempt_id=r['attempt_id'],label=r['label'],exit=r['exit'],
  warning_headers=len(re.findall(r'^.*:\d+:\d+: warning(?:\([^)]*\))?:',raw,re.M)),
  error_headers=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',raw,re.M)),
  raw_sha256=h(raw.encode())))
save(E/'diagnostic-classification.json',dict(attempts=classifications,policy='Count anchored diagnostic headers; hints, option names and printed axiom messages are not warning headers. Failed proof outputs remain failures.'))

audit=[r for r in rs if r['label']=='complete-all-owner-audit'][-1];assert audit['exit']==1 and len(audit['submitted_sources'])==487
for s in audit['submitted_sources']:assert h(Path(s['path']).read_bytes())==s['sha256']
inv=list(csv.DictReader((E/'diagnostic-actual-owner-inventory.tsv').open(),delimiter='\t'));deps=list(csv.DictReader((E/'diagnostic-recursive-dependencies.tsv').open(),delimiter='\t'));names={r['name'] for r in deps};assert len(names)==len(deps)
for r in deps:
 for k in ['typeDependencies','bodyDependencies']:assert set(filter(None,r[k].split(',')))<=names
assert {r['name'] for r in deps if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
old=json.loads((PARENT/'evidence/remaining-partial-roots.json').read_text());before={r['name'] for r in old};partial={r['name'] for r in inv if r['partial']=='true'}
removed='LightEFTSpanners.ExecutableVoting.edges._unsafe_rec';assert before-partial=={removed} and not partial-before and len(partial)==55
assert removed not in names and not any(r['unsafe']=='true' for r in inv)
violations=(E/'diagnostic-strict-violations.txt').read_text().splitlines()
assert set(violations)=={'root partial: '+n for n in partial}|{'recursive partial: '+n for n in partial}
assert len(violations)==2*len(partial)
audit_raw=(E/'attempts'/audit['attempt_id']/'raw.log').read_text()
assert f'{len(inv)} actual-owner project declarations' in audit_raw
assert f'{len(deps)} recursively visited constants' in audit_raw
assert f'Strict audit rejected {len(violations)} root/recursive safety findings' in audit_raw

assert not any(r['owner']=='LightEFTSpanners' for r in inv)
replays=[r for r in rs if Path(r['argv'][0]).name=='leanchecker'];assert len(replays)==1
r=replays[0];assert r['exit']==0 and r['checker_resolution']['actual_modules']==['LightEFTSpanners.ExecutableVoting']
assert (E/'attempts'/r['attempt_id']/'raw.log').read_text().strip()=='replaying LightEFTSpanners.ExecutableVoting'
resolution=json.loads((E/'pilot-target-resolution.json').read_text());assert resolution['count']==1 and resolution['resolved'][0]['module']=='LightEFTSpanners.ExecutableVoting'
assert h(Path(resolution['resolved'][0]['object']).read_bytes())==state['LightEFTSpanners.ExecutableVoting']['object_sha256']
assert any(r['label']=='legacy-semantic-equivalence' and r['exit']==0 for r in rs)
for label in ['pilot-semantics-and-safety']:
 assert any(r['label']==label and r['exit']==0 for r in rs)
parent_manifest=json.loads((PARENT/'evidence-sha256.json').read_text())
for r in parent_manifest:
 b=(PARENT/r['path']).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256']
summary=dict(fresh_strict_compiles=486,successful_compile_invocations=sum(r["label"].startswith("fresh-compile-") and r["exit"]==0 for r in rs),actual_owner_roots=len(inv),recursive_constants=len(deps),opaque_bodies=sum(r['kind']=='opaque' for r in deps),partial_roots=len(partial),removed_partial=removed,other_partial_roots_unchanged=True,unsafe_roots=0,aggregate_owned_roots=0,strict_gate_pass=False,new_source_bound_receipts=len(rs),persisted_preflights=len(preflights),historical_qualification="Controller pilot retained 494 persisted preflights for 495 receipts; its legacy comparison preflight was not persisted",failed_attempts=[dict(uuid=r['attempt_id'],label=r['label'],exit=r['exit']) for r in rs if r['exit']],singleton_replays=1,actual_target_preflight=True,aggregate_prefix_not_invoked=True,nonoverlap=True,one_lock_inode=True,children_reaped=True,all_snapshot_hashes_verified=True,prior_manifest_entries_preserved=len(parent_manifest))
old_inv=list(csv.DictReader((PARENT/'evidence/diagnostic-actual-owner-inventory.tsv').open(),delimiter='\t'))
old_names={r['name']:r for r in old_inv};new_names={r['name']:r for r in inv}
removed_names=sorted(old_names.keys()-new_names.keys());added_names=sorted(new_names.keys()-old_names.keys())
assert all(old_names[n]['owner']=='LightEFTSpanners.ExecutableVoting' for n in removed_names)
assert all(new_names[n]['owner']=='LightEFTSpanners.ExecutableVoting' for n in added_names)
save(E/'owner-inventory-delta.json',dict(removed_partials=sorted(before-partial),added_partials=sorted(partial-before),removed_roots=removed_names,added_roots=added_names));save(E/'reconciliation.json',summary);save(E/'remaining-partial-roots.json',[r for r in inv if r['partial']=='true'])
raw=(E/'diagnostic-recursive-dependencies.tsv').read_bytes();directory=B/'audit-export';directory.mkdir(exist_ok=True);parts=[];buf=b''
def emit(b):
 p=directory/('part-%03d.tsv'%len(parts));p.write_bytes(b);parts.append(dict(path=p.name,bytes=len(b),sha256=h(b)))
for line in raw.splitlines(keepends=True):
 if buf and len(buf)+len(line)>200000:emit(buf);buf=b''
 buf+=line
if buf:emit(buf)
save(directory/'manifest.json',dict(source='evidence/diagnostic-recursive-dependencies.tsv',bytes=len(raw),sha256=h(raw),parts=parts,reconstruction='Concatenate listed chunk bytes in order without extra separators or headers.'))
print(json.dumps(dict(**summary,chunks=len(parts)),indent=2))
