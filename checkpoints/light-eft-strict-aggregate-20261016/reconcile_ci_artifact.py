"""Read-only artifact reconciliation. Usage: python SCRIPT EXTRACTED_ARTIFACT SOURCE_COMMIT.
Run from the LightEFT repository checkout. Does not invoke Lean or trust cached audit summaries.
"""
from pathlib import Path
import json,hashlib,sys,subprocess,re,csv,collections
E=Path(sys.argv[1]);SOURCE=sys.argv[2];h=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((E/'evidence-sha256.json').read_text())
for x in manifest:
 b=(E/x['path']).read_bytes();assert len(b)==x['bytes'] and h(b)==x['sha256'],x['path']
result=json.loads((E/'result.json').read_text());assert result['source']==SOURCE and result['status']=='PASS'
rows=json.loads((E/'source-graph.json').read_text());assert len(rows)==486
assert sum(x['module'].startswith('LightEFTSpanners.') for x in rows)==429
assert sum(x['module'].startswith('LightSpanners.') for x in rows)==56
sources={x['module']:x for x in rows}
for x in rows:
 b=subprocess.check_output(['git','show',SOURCE+':'+x['path']]);assert h(b)==x['sha256'],x['path']
rs=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len(rs)==993 and len({r['attempt_id'] for r in rs})==len(rs)
assert len({(r['lock_device'],r['lock_inode']) for r in rs})==1
assert all(r['child_reaped'] and r['exit']==0 for r in rs)
assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(rs,rs[1:]))
labels=collections.Counter(r['label'] for r in rs);assert all(n==1 for n in labels.values())
for r in rs:
 for s in r['submitted_sources']:
  b=(E/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes();assert len(b)==s['bytes'] and h(b)==s['sha256']
 label=r['label'];raw=(E/'attempts'/r['attempt_id']/'raw.log').read_text()
 if label.startswith(('compile-','replay-')):
  n=label.split('-',1)[1];assert n in sources
  assert r['submitted_sources'][0]['sha256']==sources[n]['sha256']
  if label.startswith('compile-'):
   assert all(flag in r['argv'] for flag in ['-j1','-DautoImplicit=false','-DwarningAsError=true'])
   assert not re.search(r'^.*:\d+:\d+: (?:warning|error):',raw,re.M)
  else:assert r['argv'][-2:]==['-v',n] and raw.strip()=='replaying '+n
for n in sources:
 assert labels['compile-'+n]==1
 assert labels['replay-'+n]==(0 if n=='LightEFTSpanners' else 1)
assert labels['official-version']==labels['official-cache-get']==labels['complete-owner-audit']==1
assert sum(n.startswith('cache-bootstrap-') for n in labels)==19
objects=json.loads((E/'objects.json').read_text());assert {x['module'] for x in objects}==set(sources)
assert all(len(x['sha256'])==64 and x['bytes']>0 for x in objects)
inv=list(csv.DictReader((E/'actual-owner-inventory.tsv').open(),delimiter='\t'))
deps=list(csv.DictReader((E/'recursive-dependencies.tsv').open(),delimiter='\t'));names={x['name'] for x in deps}
assert len(names)==len(deps)
assert all(x['unsafe']=='false' and x['name'] in names for x in inv)
for x in deps:
 for key in ['typeDependencies','bodyDependencies']:
  assert set(filter(None,x[key].split(',')))<=names,(x['name'],key)
axioms={x['name'] for x in deps if x['kind']=='axiom'};assert axioms=={'propext','Classical.choice','Quot.sound'}
loaded=set((E/'import-closure-loaded.txt').read_text().splitlines());assert set(sources)<=loaded
m=json.loads((E/'audit-export/manifest.json').read_text());parts=[]
for x in m['parts']:
 b=(E/'audit-export'/x['path']).read_bytes();assert len(b)==x['bytes'] and h(b)==x['sha256'];parts.append(b)
b=b''.join(parts);assert len(b)==m['bytes'] and h(b)==m['sha256'] and b==(E/'recursive-dependencies.tsv').read_bytes()
print(json.dumps(dict(source=SOURCE,manifest_entries=len(manifest),receipts=len(rs),strict_compilations=486,singleton_replays=485,actual_owner_roots=len(inv),recursive_constants=len(deps),opaque_bodies=sum(x['kind']=='opaque' for x in deps),chunks=len(parts),axioms=sorted(axioms),status='RECONCILED; no Lean execution'),indent=2))
