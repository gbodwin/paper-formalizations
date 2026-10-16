from pathlib import Path
import json,hashlib,subprocess,re,fcntl
b=Path('checkpoints/light-eft-continuation-20261016');e=b/'evidence'
h=lambda x:hashlib.sha256(x).hexdigest()
rs=sorted([json.loads(p.read_text()) for p in (e/'attempts').glob('*/receipt.json')],key=lambda r:r['start_monotonic_ns'])
assert len({r['attempt_id'] for r in rs})==len(rs)
assert len({(r['lock_device'],r['lock_inode']) for r in rs})==1
assert all(r['child_reaped'] for r in rs)
assert all(a['end_monotonic_ns']<c['start_monotonic_ns'] for a,c in zip(rs,rs[1:]))
superseded=[];warnings=[]
for r in rs:
 for s in r['submitted_sources']:
  data=(e/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes()
  assert h(data)==s['sha256'] and len(data)==s['bytes']
  if Path(s['path']).read_bytes()!=data:superseded.append({'attempt':r['attempt_id'],'label':r['label'],'sha256':s['sha256']})
 raw=(e/'attempts'/r['attempt_id']/'raw.log').read_text()
 warnings += [{'attempt':r['attempt_id'],'diagnostic':x} for x in raw.splitlines() if re.match(r'^.*:\d+:\d+: warning:',x)]
(e/'execution-reconciliation.json').write_text(json.dumps(dict(attempts=len(rs),failed=sum(r['exit']!=0 for r in rs),unique_ids=True,one_lock_inode=True,nonoverlap=True,all_children_reaped=True,all_snapshot_hashes_verified=True,superseded_source_attempts=superseded,warning_headers=warnings),indent=2)+'\n')
order=json.loads((e/'dependency-order.json').read_text());objects=[]
for n in order:
 p=Path('.lake/build/lib/lean')/Path(*n.split('.')).with_suffix('.olean');objects.append(dict(module=n,path=str(p),sha256=h(p.read_bytes()),bytes=p.stat().st_size))
(e/'object-hashes.json').write_text(json.dumps(objects,indent=2)+'\n')
m=json.loads((e/'source-reconciliation.json').read_text())
for p,d in m['sources'].items():assert h(Path(p).read_bytes())==d
pins=json.loads(Path('lake-manifest.json').read_text())['packages'];out=[]
for p in pins:
 d=Path('/workspace/paper-formalizations/.lake/packages')/p['name']
 rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip();assert rev==p['rev']
 status=subprocess.check_output(['git','status','--porcelain'],cwd=d,text=True)
 out.append(dict(name=p['name'],revision=rev,status=status))
(e/'dependency-pins.json').write_text(json.dumps(out,indent=2)+'\n')
t=Path('/workspace/toolchains/lean-4.34.0-linux/bin')
(e/'toolchain-hashes.json').write_text(json.dumps({str(p):h(p.read_bytes()) for p in [t/'lean',t/'leanchecker',Path('lean-toolchain'),Path('lake-manifest.json')]},indent=2)+'\n')
a=b/'audit-export';a.mkdir(exist_ok=True);raw=(e/'recursive-dependencies.tsv').read_bytes();parts=[];buf=b''
def emit(buf):
 p=a/('part-%03d.tsv'%len(parts));p.write_bytes(buf);parts.append(dict(path=p.name,bytes=len(buf),sha256=h(buf)))
for row in raw.splitlines(keepends=True):
 if buf and len(buf)+len(row)>200000:emit(buf);buf=b''
 buf+=row
if buf:emit(buf)
(a/'manifest.json').write_text(json.dumps(dict(source='evidence/recursive-dependencies.tsv',bytes=len(raw),sha256=h(raw),reconstruction='Concatenate parts in listed order as bytes without separators.',parts=parts),indent=2)+'\n')
f=open('/tmp/distance-sparsification-single-compiler.lock','a');fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
print(json.dumps(dict(receipts=len(rs),warnings=len(warnings),superseded=len(superseded),chunks=len(parts),pins=len(out),lock_free=True)))
