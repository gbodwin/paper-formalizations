from pathlib import Path
import subprocess,json,hashlib,collections
root=Path.cwd();base=root/'checkpoints/plus6-integration-20261016';ev=base/'evidence'
source='c189a4e93786b47c7dbc23146c6b44a5b9cc75dc'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd=root):
 r=subprocess.run(cmd,cwd=cwd,text=True,capture_output=True)
 return dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
def save(n,x):(base/n).write_text(json.dumps(x,indent=2)+'\n')
paper=root/'A Note on Distance-Preserving Graph Sparsification'
paths=[paper/'SlackSparsification/PlusSixIntegration.lean',paper/'SlackSparsification.lean',paper/'verification/PlusSixIntegrationAudit.lean',root/'.lake/build/lib/lean/SlackSparsification/PlusSixIntegration.olean',root/'.lake/build/lib/lean/SlackSparsification.olean']
for p in paths[:3]:assert subprocess.check_output(['git','show',source+':'+str(p.relative_to(root))])==p.read_bytes()
for i,p in [(1,paths[0]),(2,paths[1])]:assert p.read_bytes()==(ev/f'attempt-{i:03}.lean').read_bytes()
save('source-object-hashes.json',dict(source_commit=source,files=[dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=sha(p)) for p in paths]))
old=json.loads((root/'checkpoints/subset-plus2-construction-20261015/source-object-hashes.json').read_text())['files']
old+=json.loads((root/'checkpoints/subset-plus2-cgk13-20261015/supporting-object-hashes.json').read_text())
# The aggregate is intentionally recompiled after adding imports.
old=[row for row in old if row["path"]!=".lake/build/lib/lean/SlackSparsification.olean"]
for row in old:assert sha(root/row['path'])==row['sha256'],row['path']
diff=run(['git','diff','d199b99c6d3902e2b827a2b5c3efef072c2fa88a',source,'--name-status'])
save('preservation.json',dict(source_commit=source,unchanged_prior_entries=old,source_diff=diff,certified_head=run(['git','rev-parse','HEAD'],Path('/workspace/paper-formalizations')),certified_status=run(['git','status','--short'],Path('/workspace/paper-formalizations'))))
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
print('All prior hash entries, nine pins, final snapshots, and dependency chunks reconcile.')
