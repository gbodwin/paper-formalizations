"""Read-only reconciliation of the full local strict LightEFT checkpoint; never runs Lean."""
from pathlib import Path
import json,hashlib,subprocess,re
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence'
h=lambda b:hashlib.sha256(b).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
rows=json.loads((E/'source-graph.json').read_text());state=json.loads((E/'build-state.json').read_text())
assert len(rows)==len(state)==486
receipts=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len({r['attempt_id'] for r in receipts})==len(receipts)
assert len({(r['lock_device'],r['lock_inode']) for r in receipts})==1
assert all(r['child_reaped'] for r in receipts)
assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(receipts,receipts[1:]))
for r in receipts:
 for s in r['submitted_sources']:
  b=(E/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes();assert len(b)==s['bytes'] and h(b)==s['sha256']
verified=[]
for row in rows:
 n=row['module'];p=ROOT/row['path'];digest=h(p.read_bytes());entry=state[n]
 assert entry['inputs']['source_sha256']==digest
 op=ROOT/'.lake/build/lib/lean'/Path(*n.split('.')).with_suffix('.olean');assert h(op.read_bytes())==entry['object_sha256']
 for dep,sha in entry['inputs']['imports'].items():assert h((ROOT/'.lake/build/lib/lean'/Path(*dep.split('.')).with_suffix('.olean')).read_bytes())==sha
 for label in ['compile-'+n]+([] if n=='LightEFTSpanners' else ['replay-'+n]):
  rs=[r for r in receipts if r['label']==label and r['exit']==0 and r['submitted_sources'][0]['sha256']==digest];assert rs,label
  r=rs[-1];raw=(E/'attempts'/r['attempt_id']/'raw.log').read_text()
  if label.startswith('replay-'):assert raw.strip()=='replaying '+n
  else:assert not re.search(r'^.*:\d+:\d+: (?:warning|error):',raw,re.M)
 verified.append(dict(**row,final_source_sha256=digest,object_sha256=entry['object_sha256']))
audit=[r for r in receipts if r['label']=='diagnostic-recursive-audit' and r['exit']==1][-1]
assert len(audit['submitted_sources'])==487
for s in audit['submitted_sources']:assert h(Path(s['path']).read_bytes())==s['sha256']
assert 'DIAGNOSTIC ONLY: 9327' in (E/'attempts'/audit['attempt_id']/'raw.log').read_text()
assert 'Strict audit rejected 114' in (E/'attempts'/audit['attempt_id']/'raw.log').read_text()
# Prior checkpoint and accepted residual evidence are immutable and rehashed.
parents={}
for name in ['light-eft-aggregate-20261016','light-eft-native-residual-20261016']:
 parent=B.parent/name
 if not parent.exists():continue
 manifest=parent/'evidence-sha256.json'
 if not manifest.exists():continue
 entries=json.loads(manifest.read_text())
 for e in entries:
  data=(parent/e['path']).read_bytes();assert len(data)==e['bytes'] and h(data)==e['sha256'],e['path']
 parents[name]=len(entries)
save(E/'source-object-hashes.json',verified)
save(E/'execution-reconciliation.json',dict(attempts=len(receipts),failures=[dict(uuid=r['attempt_id'],label=r['label'],exit=r['exit']) for r in receipts if r['exit']],strict_compilations=486,singleton_replays=485,strict_all_owner_gate_pass=False,aggregate_prefix_attempt_failed=True,unique_ids=True,one_lock_inode=True,nonoverlap=True,children_reaped=True,all_snapshot_hashes_verified=True,final_sources_objects_and_imports_verified=True,strict_warning_headers=0,parent_manifests=parents))
# Row-aligned ordered exports retain the complete original.
raw=(E/'diagnostic-recursive-dependencies.tsv').read_bytes();out=B/'audit-export';out.mkdir(exist_ok=True);parts=[];buf=b''
def emit(b):
 p=out/('part-%03d.tsv'%len(parts));p.write_bytes(b);parts.append(dict(path=p.name,bytes=len(b),sha256=h(b)))
for line in raw.splitlines(keepends=True):
 if buf and len(buf)+len(line)>200000:emit(buf);buf=b''
 buf+=line
if buf:emit(buf)
save(out/'manifest.json',dict(source='evidence/diagnostic-recursive-dependencies.tsv',bytes=len(raw),sha256=h(raw),parts=parts,reconstruction='Concatenate ordered parts as bytes without separators.'))
diff=subprocess.check_output(['git','diff','85fe8c209ac442bb6729e168c8c00dc870143101','--']+[r['path'] for r in rows],cwd=ROOT)
(E/'mechanical-source-diff.patch').write_bytes(diff)
print(json.dumps(dict(attempts=len(receipts),failures=sum(r['exit']!=0 for r in receipts),compilations=486,replays=485,chunks=len(parts),parents=parents)))
