from pathlib import Path
import subprocess,json,hashlib,collections
root=Path.cwd();base=root/'checkpoints/directed-preservers-20261016';ev=base/'evidence'
source='58116f153e48e57a055767cabfd1bc89f622214d'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd=root):
 r=subprocess.run(cmd,cwd=cwd,text=True,capture_output=True)
 return dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
def save(n,x):(base/n).write_text(json.dumps(x,indent=2)+'\n')
paper=root/'A Note on Distance-Preserving Graph Sparsification'
mods=['DirectedBasics','DirectedTrees','DirectedExact','DirectedComplete','DirectedPreserver']
paths=[paper/'SlackSparsification'/(n+'.lean') for n in mods+['ReachabilityBasics','ReachabilityParameters']]
paths += [paper/'verification/DirectedPreserverAudit.lean',root/'New Results on Linear Size Distance Preservers/LinearDistancePreservers/ConsistentTiebreaking.lean']
paths += [root/'.lake/build/lib/lean/SlackSparsification'/(n+'.olean') for n in mods]
paths += [root/'.lake/build/lib/lean/LinearDistancePreservers/ConsistentTiebreaking.olean']
for p in paths:
 if p.suffix=='.lean':assert subprocess.check_output(['git','show',source+':'+str(p.relative_to(root))])==p.read_bytes()
save('source-object-hashes.json',dict(source_commit=source,files=[dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=sha(p)) for p in paths]))
for n,i in [('DirectedBasics',5),('DirectedTrees',7),('DirectedExact',8),('DirectedComplete',10),('DirectedPreserver',13)]:
 assert (ev/f'attempt-{i:03}.lean').read_bytes()==(paper/'SlackSparsification'/(n+'.lean')).read_bytes()
 assert json.loads((ev/f'attempt-{i:03}.json').read_text())['exit']==0
old=[]
for f in ['checkpoints/plus6-integration-20261016/source-object-hashes.json','checkpoints/subset-plus2-construction-20261015/source-object-hashes.json']:
 old+=json.loads((root/f).read_text())['files']
for row in old:assert sha(root/row['path'])==row['sha256'],row['path']
save('preservation.json',dict(unchanged_prior_entries=old,source_diff=run(['git','diff','cb78525226f60d4bf7f24a997280779eb4d50fde',source,'--name-status']),certified_head=run(['git','rev-parse','HEAD'],Path('/workspace/paper-formalizations')),certified_status=run(['git','status','--short'],Path('/workspace/paper-formalizations'))))
originals=ev/'recovered-originals';originals.mkdir(exist_ok=True);comparison=[]
for r in json.loads((base/'recovered-source-manifest.json').read_text()):
 data=subprocess.check_output(['git','show',r['source_commit']+':'+r['path']]);assert hashlib.sha256(data).hexdigest()==r['sha256']
 (originals/Path(r['path']).name).write_bytes(data)
 comparison.append(dict(path=r['path'],original_sha256=r['sha256'],current_sha256=sha(root/r['path']),identical=data==(root/r['path']).read_bytes()))
save('recovery-comparison.json',comparison)
deps=[]
for p in json.loads((root/'lake-manifest.json').read_text())['packages']:
 cwd=root/'.lake/packages'/p['name'];head=run(['git','rev-parse','HEAD'],cwd);status=run(['git','status','--short'],cwd)
 assert head['stdout'].strip()==p['rev'] and not status['stdout'],p['name']
 deps.append(dict(name=p['name'],expected=p['rev'],head=head,status=status))
save('dependencies.json',deps)
save('environment.json',[run(c) for c in [['date','-u','+%Y-%m-%dT%H:%M:%SZ'],['df','-h','/workspace'],['free','-h'],['cat','/sys/fs/cgroup/memory.max'],['cat','/sys/fs/cgroup/cpu.max'],['ps','-eo','pid,comm'],['/workspace/toolchains/lean-4.34.0-linux/bin/lean','--version'],['/workspace/toolchains/lean-4.34.0-linux/bin/lake','--version']]])
save('toolchain-binary-hashes.json',[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in [Path('/workspace/toolchains/lean-4.34.0-linux/bin')/n for n in ['lean','lake','leanchecker']]])
raw=ev/'recursive-dependencies.tsv';lines=raw.read_bytes().splitlines(keepends=True);chunks=[];out=ev/'dependency-chunks';out.mkdir(exist_ok=True)
for i in range(0,len(lines),400):
 p=out/f'part-{i//400+1:03}.tsv';p.write_bytes(b''.join(lines[i:i+400]));chunks.append(dict(path=str(p.relative_to(ev)),bytes=p.stat().st_size,sha256=sha(p)))
assert b''.join((ev/c['path']).read_bytes() for c in chunks)==raw.read_bytes()
(ev/'dependency-chunk-manifest.json').write_text(json.dumps(dict(raw_sha256=sha(raw),raw_rows=len(lines)-1,reconstruction_exact=True,chunks=chunks),indent=2)+'\n')
rows=(ev/'actual-owner-inventory.tsv').read_text().splitlines()[1:]
save('audit-coverage.json',dict(source_commit=source,owner_counts=dict(collections.Counter(r.split('\t')[0] for r in rows)),recursive_constants=len(lines)-1,opaque_bodies=14,allowed_axioms=['propext','Classical.choice','Quot.sound']))
save('warning-classification.json',dict(inherited_module='LinearDistancePreservers.ConsistentTiebreaking',inherited_warning_count=(ev/'attempt-002.log').read_text().count('warning:'),classification='linter.unusedSectionVars',source_unchanged=True,strict_directed_modules=mods,strict_final_warning_count=0,sequencing_incident='evidence/SEQUENCING_INCIDENT.md'))
print('Final snapshots, unchanged accepted sources/objects, upstream originals and all pins verified.')
