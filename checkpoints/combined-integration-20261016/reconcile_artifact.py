"""Read-only artifact reconciliation; does not run Lean. Supply an extracted artifact directory."""
from pathlib import Path
import csv, hashlib, json, re, subprocess, sys
b=Path(sys.argv[1]); sha='34bda2f53bb8bd31cb7fb8322bf1499dc002d459'
hash_bytes=lambda d:hashlib.sha256(d).hexdigest()
read=lambda n:json.loads((b/n).read_text())
manifest=read('evidence-sha256.json')
for r in manifest:
    p=b/r['path']; assert p.resolve().is_relative_to(b.resolve())
    d=p.read_bytes(); assert len(d)==r['bytes'] and hash_bytes(d)==r['sha256'],r['path']
assert {r['path'] for r in manifest}=={str(p.relative_to(b)) for p in b.rglob('*') if p.is_file() and p.name!='evidence-sha256.json'}
result=read('result.json'); assert result['result']=='PASS' and result['tested_source']==sha
assert result['project_compiles']==53 and result['leaf_replays']==52
assert result['inherited_warnings']==44
inventory=read('source-module-inventory.json'); assert len(inventory['compile_order'])==53
assert len(inventory['leaf_replays'])==52 and len(set(inventory['leaf_replays']))==52
source=read('source-receipt.json'); assert source['source_commit']==sha
assert source['ci_commit']==result['ci_commit']
commands=[json.loads(x) for x in (b/'commands.jsonl').read_text().splitlines()]
assert len(commands)==result['commands'] and len({r['attempt_id'] for r in commands})==len(commands)
assert len({(r['lock_device'],r['lock_inode']) for r in commands})==1
for prev,cur in zip(commands,commands[1:]):
    assert prev['end_monotonic_ns']<=cur['lock_acquired_monotonic_ns']<=cur['start_monotonic_ns']
for r in commands:
    assert r['child_reaped'] and r['exit']==0 and r['child_pid']
    p=b/'attempts'/r['attempt_id']; assert json.loads((p/'receipt.json').read_text())==r
    assert (p/'raw.log').read_bytes()==(b/(r['label']+'.log')).read_bytes()
    for s in r['submitted_sources']:
        d=(p/(s['sha256']+'.lean')).read_bytes(); assert len(d)==s['bytes'] and hash_bytes(d)==s['sha256']
        rel=s['path'].split('/source/',1)[1]
        if not rel.startswith('.lake/'):
            assert source['tracked_file_sha256'][rel]==s['sha256']
            assert hash_bytes(subprocess.check_output(['git','show',sha+':'+rel]))==s['sha256']
    if r['label'].startswith(('compile-','checker-','cache-bootstrap-')) or r['label'] in {'recursive-audit','official-cache-get'}:
        assert r['submitted_sources']
for n in inventory['leaf_replays']:
    assert (b/('checker-'+n+'.log')).read_text().strip()=='replaying '+n
assert [r['label'][8:] for r in commands if r['label'].startswith('compile-')]==inventory['compile_order']
assert [r['label'][8:] for r in commands if r['label'].startswith('checker-')]==inventory['leaf_replays']
warnings=read('warning-classification.json'); assert len(warnings)==24
for w in warnings:
    raw=(b/('compile-'+w['module']+'.log')).read_text()
    assert len(re.findall(r'^.+:\d+:\d+: warning:',raw,re.M))==w['count']
assert sum(w['count'] for w in warnings)==44
source_root=commands[0]['cwd']; inherited={w['module'] for w in warnings}
for n in inventory['compile_order']:
    raw=(b/('compile-'+n+'.log')).read_text()
    if n not in inherited:
        assert not raw.strip(), n
        continue
    if n=='LinearDistancePreservers.ConsistentTiebreaking':
        baseline='checkpoints/directed-preservers-20261016/evidence/attempt-002.log'
        old_root='/workspace/plus-six-evidence-publish'
    else:
        baseline='checkpoints/conditional-plus6-preserved-20261015/normal-toolchain-evidence/compile-'+n+'.log'
        old_root='/workspace/plus-six-verification/checkpoint/candidate'
    old=subprocess.check_output(['git','show',sha+':'+baseline],text=True)
    assert raw==old.replace(old_root,source_root), n
objects=read('object-hashes.json')
assert {r['path'] for r in objects}=={'.lake/build/lib/lean/'+n.replace('.','/')+'.olean' for n in inventory['compile_order']}
assert all(re.fullmatch('[0-9a-f]{64}',r['sha256']) for r in objects)
roots=list(csv.DictReader((b/'actual-owner-inventory.tsv').open(),delimiter='\t'))
rows=list(csv.DictReader((b/'recursive-dependencies.tsv').open(),delimiter='\t'))
assert {r['owner'] for r in roots}==set(inventory['leaf_replays'])
assert len(roots)==result['actual_owner_roots'] and len(rows)==result['recursive_constants']
assert {r['name'] for r in roots}<={r['name'] for r in rows}
assert {r['name'] for r in rows if r['kind']=='axiom'}=={'propext','Classical.choice','Quot.sound'}
by_name={r['name']:r for r in rows}; visited=set(); todo=[r['name'] for r in roots]
while todo:
    n=todo.pop()
    if n in visited:continue
    visited.add(n); r=by_name[n]
    for field in ['typeDependencies','bodyDependencies']:
        todo.extend(x for x in r[field].split(',') if x)
assert visited==set(by_name), 'Recursive audit coverage must be exact, not just a root subset'
assert all(r['unsafe']=='false' for r in roots)
a=read('audit-export/manifest.json')
d=b''.join((b/'audit-export'/p['path']).read_bytes() for p in a['parts'])
assert d==(b/'recursive-dependencies.tsv').read_bytes() and len(d)==a['bytes'] and hash_bytes(d)==a['sha256']
print(json.dumps({'PASS':True,'manifest_entries':len(manifest),'commands':len(commands),'result':result},indent=2))
