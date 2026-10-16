"""Read-only reconciliation of an extracted clean-CI artifact; never invokes Lean."""
from pathlib import Path
import csv,hashlib,json,re,subprocess,sys
E=Path(sys.argv[1]);SOURCE='90b270f5442b3ebe50bd41a45f501b2277380d71';BASELINE='9bb8e69d522f794fd297672131b5d6ef19fddcc6'
hash_bytes=lambda d:hashlib.sha256(d).hexdigest()
read=lambda n:json.loads((E/n).read_text())
manifest=read('evidence-sha256.json')
for r in manifest:
 p=E/r['path'];assert p.resolve().is_relative_to(E.resolve());d=p.read_bytes();assert len(d)==r['bytes'] and hash_bytes(d)==r['sha256'],r['path']
assert {r['path'] for r in manifest}=={str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.name!='evidence-sha256.json'}
result=read('result.json');assert result['PASS'] and result['tested_source']==SOURCE
assert (result['builds'],result['leaf_replays'],result['audits'],result['strict_builds'],result['exact_diagnostic_baselines'],result['warning_headers'])==(60,59,3,51,9,22)
source=read('source-receipt.json');assert source['source_commit']==SOURCE and source['ci_commit']==result['trigger_commit']
pinned=read('candidate-65-file-manifest.json');assert len(pinned['files'])==65
for name,h in pinned['files'].items():
 assert h==source['tracked_file_sha256'][name]==hash_bytes(subprocess.check_output(['git','show',SOURCE+':'+name]))
inv=read('source-module-inventory.json');assert len(inv['compile_order'])==60 and len(set(inv['leaf_replays']))==59
commands=[json.loads(x) for x in (E/'commands.jsonl').read_text().splitlines()]
assert len(commands)==result['commands'] and len({r['attempt_id'] for r in commands})==len(commands)
assert len({(r['lock_device'],r['lock_inode']) for r in commands})==1
for a,b in zip(commands,commands[1:]):assert a['end_monotonic_ns']<=b['lock_acquired_monotonic_ns']<=b['start_monotonic_ns']
for r in commands:
 assert r['child_reaped'] and r['exit']==0 and r['child_pid']
 p=E/'attempts'/r['attempt_id'];assert json.loads((p/'receipt.json').read_text())==r
 assert (p/'raw.log').read_bytes()==(E/(r['label']+'.log')).read_bytes()
 if Path(r['argv'][0]).name in {'lean','leanchecker','lake'}:assert r['submitted_sources']
 for s in r['submitted_sources']:
  d=(p/(s['sha256']+'.lean')).read_bytes();assert len(d)==s['bytes'] and hash_bytes(d)==s['sha256']
  if '/source/' in s['path']:
   rel=s['path'].split('/source/',1)[1]
   if not rel.startswith('.lake/'):assert source['tracked_file_sha256'][rel]==s['sha256']
  else:
   rel='checkpoints/light-spanner-ci-20261016/RecursiveAudit.lean'
   assert s['path'].endswith(rel)
   assert hash_bytes(subprocess.check_output(['git','show',result['trigger_commit']+':'+rel]))==s['sha256']
assert [r['label'][8:] for r in commands if r['label'].startswith('compile-')]==inv['compile_order']
assert [r['label'][8:] for r in commands if r['label'].startswith('checker-')]==inv['leaf_replays']
for n in inv['leaf_replays']:assert (E/('checker-'+n+'.log')).read_text().strip()=='replaying '+n
warnings=read('warning-classification.json');assert len(warnings)==9 and sum(w['headers'] for w in warnings)==22
inherited={w['module']:w for w in warnings};source_root=commands[0]['cwd']
for n in inv['compile_order']:
 raw=(E/('compile-'+n+'.log')).read_text()
 if n not in inherited:assert not raw.strip(),n;continue
 w=inherited[n];old=subprocess.check_output(['git','show',BASELINE+':'+w['baseline_path']])
 assert hash_bytes(old)==w['baseline_sha256']
 assert raw==old.decode().replace('/workspace/light-spanner-verification',source_root),n
 assert len(re.findall(r'^.+:\d+:\d+: warning:',raw,re.M))==w['headers']
roots=list(csv.DictReader((E/'actual-owner-inventory.tsv').open(),delimiter='\t'))
rows=list(csv.DictReader((E/'recursive-dependencies.tsv').open(),delimiter='\t'))
assert len(roots)==795 and len(rows)==22323
assert {r['owner'] for r in roots}==set(inv['leaf_replays'])
assert all(r['unsafe']=='false' for r in roots)
assert {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
by_name={r['name']:r for r in rows};seen=set();todo=[r['name'] for r in roots]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);r=by_name[n]
 for key in ['typeDependencies','bodyDependencies']:todo.extend(x for x in r[key].split(',') if x)
assert seen==set(by_name)
m=read('audit-export/manifest.json');d=b''.join((E/'audit-export'/p['path']).read_bytes() for p in m['parts'])
assert d==(E/'recursive-dependencies.tsv').read_bytes() and len(d)==m['bytes'] and hash_bytes(d)==m['sha256']
objects=read('object-hashes.json');assert {r['path'] for r in objects}=={'.lake/build/lib/lean/'+n.replace('.','/')+'.olean' for n in inv['compile_order']}
print(json.dumps({'PASS':True,'manifest_entries':len(manifest),'commands':len(commands),'roots':len(roots),'closure':len(rows),'chunks':len(m['parts']),'result':result},indent=2))
