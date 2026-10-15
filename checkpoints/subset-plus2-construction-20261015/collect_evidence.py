from pathlib import Path
import subprocess,json,hashlib,collections,datetime
root=Path.cwd(); base=root/'checkpoints/subset-plus2-construction-20261015';ev=base/'evidence'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd=root):
 r=subprocess.run(cmd,cwd=cwd,text=True,capture_output=True)
 return dict(command=cmd,exit=r.returncode,stdout=r.stdout,stderr=r.stderr)
def save(name,data): (base/name).write_text(json.dumps(data,indent=2)+'\n')
source_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert source_commit=='3479c6c51ddf7e970f13cb263128fba8fdd36000'
paths=list((root/'A Note on Distance-Preserving Graph Sparsification/SlackSparsification').glob('SubsetPlusTwo*.lean'))
paths += [root/'A Note on Distance-Preserving Graph Sparsification/verification/SubsetPlusTwoConstructionAudit.lean']
paths += list((root/'.lake/build/lib/lean/SlackSparsification').glob('SubsetPlusTwo*.olean'))
save('source-object-hashes.json',dict(source_commit=source_commit,files=[dict(path=str(p.relative_to(root)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(paths)]))
old=[]
for f in ['source-object-hashes.json','supporting-object-hashes.json']:
 for row in json.loads((root/'checkpoints/subset-plus2-cgk13-20261015'/f).read_text()):
  p=root/row['path']; actual=sha(p)
  assert actual==row['sha256'],row['path']
  old.append(dict(path=row['path'],sha256=actual,unchanged=True))
tracked=run(['git','diff','1cb78102a5011809c8da85b23113790bb15935a4','--name-status'])
assert all(line.startswith('A\t') for line in tracked['stdout'].splitlines())
save('preservation.json',dict(previous_checkpoint='1cb78102a5011809c8da85b23113790bb15935a4',source_commit=source_commit,only_additions=tracked,prior_hash_manifest_entries=old,certified_head=run(['git','rev-parse','HEAD'],Path('/workspace/paper-formalizations')),certified_status=run(['git','status','--short'],Path('/workspace/paper-formalizations'))))
deps=[]
for p in json.loads((root/'lake-manifest.json').read_text())['packages']:
 cwd=root/'.lake/packages'/p['name'];head=run(['git','rev-parse','HEAD'],cwd);status=run(['git','status','--short'],cwd)
 assert head['stdout'].strip()==p['rev'] and not status['stdout'],p['name']
 deps.append(dict(name=p['name'],expected=p['rev'],head=head,status=status))
save('dependencies.json',deps)
cmds=[['date','-u','+%Y-%m-%dT%H:%M:%SZ'],['df','-h','/workspace'],['free','-h'],['cat','/sys/fs/cgroup/memory.max'],['cat','/sys/fs/cgroup/cpu.max'],['ps','-eo','pid,comm'],['/workspace/toolchains/lean-4.34.0-linux/bin/lean','--version'],['/workspace/toolchains/lean-4.34.0-linux/bin/lake','--version']]
save('environment.json',[run(c) for c in cmds])
save('toolchain-binary-hashes.json',[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in [Path('/workspace/toolchains/lean-4.34.0-linux/bin')/n for n in ['lean','lake','leanchecker']]])
raw=ev/'recursive-dependencies.tsv';lines=raw.read_bytes().splitlines(keepends=True);chunks=[];out=ev/'dependency-chunks';out.mkdir(exist_ok=True)
for i in range(0,len(lines),400):
 p=out/f'part-{i//400+1:03}.tsv';p.write_bytes(b''.join(lines[i:i+400]));chunks.append(dict(path=str(p.relative_to(ev)),bytes=p.stat().st_size,sha256=sha(p)))
assert b''.join((ev/c['path']).read_bytes() for c in chunks)==raw.read_bytes()
(ev/'dependency-chunk-manifest.json').write_text(json.dumps(dict(raw_sha256=sha(raw),raw_rows=len(lines)-1,reconstruction_exact=True,chunks=chunks),indent=2)+'\n')
rows=(ev/'actual-owner-inventory.tsv').read_text().splitlines()[1:]
save('audit-coverage.json',dict(source_commit=source_commit,owner_counts=dict(collections.Counter(r.split('\t')[0] for r in rows)),recursive_constants=len(lines)-1,opaque_bodies=13,allowed_axioms=['propext','Classical.choice','Quot.sound']))
for module,attempt in [('Packing',2),('Construction',5),('Purchase',9),('Fold',12)]:
 snap=ev/f'attempt-{attempt:03}.lean';src=root/f'A Note on Distance-Preserving Graph Sparsification/SlackSparsification/SubsetPlusTwo{module}.lean'
 assert snap.read_bytes()==src.read_bytes(),module
 assert json.loads((ev/f'attempt-{attempt:03}.json').read_text())['exit']==0
print('Evidence collected: pins, prior hashes, final snapshots, recursive chunk reconstruction all match.')
