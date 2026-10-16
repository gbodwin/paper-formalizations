"""Read-only proof/evidence reconciliation; writes only derived evidence, never runs Lean."""
from pathlib import Path
import json,hashlib,subprocess,fcntl,datetime,re
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
h=lambda b:hashlib.sha256(b).hexdigest()
def save(name,value):(E/name).write_text(json.dumps(value,indent=2)+'\n')
rs=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len({r['attempt_id'] for r in rs})==len(rs)
assert len({(r['lock_device'],r['lock_inode']) for r in rs})==1
assert all(r['child_reaped'] for r in rs)
assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(rs,rs[1:]))
superseded=[];failed=[];warnings=[]
for r in rs:
 if r['exit']!=0:failed.append(dict(id=r['attempt_id'],label=r['label'],exit=r['exit']))
 for s in r['submitted_sources']:
  d=(E/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes()
  assert h(d)==s['sha256'] and len(d)==s['bytes']
  if Path(s['path']).read_bytes()!=d:superseded.append(dict(id=r['attempt_id'],label=r['label'],sha256=s['sha256']))
 raw=(E/'attempts'/r['attempt_id']/'raw.log').read_text()
 warnings += [dict(id=r['attempt_id'],diagnostic=x) for x in raw.splitlines() if re.match(r'^.*:\d+:\d+: warning:',x)]
save('execution-reconciliation.json',dict(attempts=len(rs),failed=failed,unique_ids=True,one_lock_inode=True,nonoverlap=True,all_children_reaped=True,all_snapshot_hashes_verified=True,superseded_sources=superseded,warning_headers=warnings))
parent='99e021fbe4d43d81f38677d0112f31c8146c18d4'
source='d5b3ab4e82bbac197d20a3eef29e89046f0bdd9a'
preserved={}
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',parent,'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners'],cwd=ROOT,text=True).splitlines()
for path in paths:
 if path.endswith('.lean'):
  before=subprocess.check_output(['git','show',parent+':'+path],cwd=ROOT)
  assert (ROOT/path).read_bytes()==before
  preserved[path]=h(before)
old={'sources':preserved}
for row in json.loads((ROOT/'checkpoints/light-eft-native-hosts-20261016/evidence-sha256.json').read_text()):
 d=(ROOT/'checkpoints/light-eft-native-hosts-20261016'/row['path']).read_bytes()
 assert len(d)==row['bytes'] and h(d)==row['sha256']
new_names=['NativeGreedyBlocking','NativeGreedySampling']
new_sources=[]
for name in new_names:
 p=ROOT/'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners'/(name+'.lean')
 assert p.read_bytes()==subprocess.check_output(['git','show',source+':'+str(p.relative_to(ROOT))],cwd=ROOT)
 new_sources.append(dict(module='LightEFTSpanners.'+name,path=str(p.relative_to(ROOT)),sha256=h(p.read_bytes())))
 for label in ['compile-LightEFTSpanners.'+name,'replay-LightEFTSpanners.'+name]:
  r=[r for r in rs if r['label']==label][-1];assert r['exit']==0 and r['submitted_sources'][0]['sha256']==h(p.read_bytes())
order=json.loads((E/'import-order.json').read_text())+['LightEFTSpanners.'+n for n in new_names]
objects=[]
for name in order:
 obj=ROOT/'.lake/build/lib/lean'/Path(*name.split('.')).with_suffix('.olean')
 objects.append(dict(module=name,path=str(obj.relative_to(ROOT)),sha256=h(obj.read_bytes()),bytes=obj.stat().st_size))
audit=[r for r in rs if r['label']=='recursive-audit'][-1];assert audit['exit']==0
for src in new_sources:assert any(s['sha256']==src['sha256'] for s in audit['submitted_sources'])
save('source-object-hashes.json',dict(parent=parent,tested_source=source,preserved_original_modules=len(old['sources']),sources=new_sources,objects=objects,prior_evidence_manifest_verified=True,preserved_source_hashes=preserved))
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
out=[]
for pin in pins:
 d=Path('/workspace/paper-formalizations/.lake/packages')/pin['name']
 rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip();assert rev==pin['rev']
 status=subprocess.check_output(['git','status','--porcelain'],cwd=d,text=True)
 out.append(dict(name=pin['name'],revision=rev,status=status))
save('dependency-pins.json',out)
t=Path('/workspace/toolchains/lean-4.34.0-linux/bin')
save('toolchain-hashes.json',{str(p):h(p.read_bytes()) for p in [t/'lean',t/'leanchecker',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']})
a=B/'audit-export';a.mkdir(exist_ok=True);raw=(E/'recursive-dependencies.tsv').read_bytes();parts=[];buf=b''
def emit(data):
 p=a/('part-%03d.tsv'%len(parts));p.write_bytes(data);parts.append(dict(path=p.name,bytes=len(data),sha256=h(data)))
for row in raw.splitlines(keepends=True):
 if buf and len(buf)+len(row)>200000:emit(buf);buf=b''
 buf+=row
if buf:emit(buf)
(a/'manifest.json').write_text(json.dumps(dict(source='evidence/recursive-dependencies.tsv',bytes=len(raw),sha256=h(raw),reconstruction='Concatenate listed parts as bytes without separators.',parts=parts),indent=2)+'\n')
ps=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
assert not any(line.split()[-1] in ['lean','lake','leanchecker'] for line in ps.splitlines()[1:])
f=open('/tmp/distance-sparsification-single-compiler.lock','a');fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
save('terminal-state.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),compiler_lock_free=True,processes=ps,disk=subprocess.check_output(['df','-h',str(ROOT)],text=True),memory_limit=Path('/sys/fs/cgroup/memory.max').read_text().strip(),cpu_quota=Path('/sys/fs/cgroup/cpu.max').read_text().strip()))
print(json.dumps(dict(receipts=len(rs),failures=len(failed),warning_headers=len(warnings),chunks=len(parts),preserved_modules=len(old['sources']),objects=len(objects),new_modules=len(new_sources))))
