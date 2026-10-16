"""Reconcile the blocked strict preparation. Never invokes Lean or changes proof source."""
from pathlib import Path
import json,hashlib,subprocess,fcntl,datetime,re
ROOT=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent;E=B/'evidence'
PARENT='88fa6ea4990488c2d3af870283ba47d6b35fec85';SOURCE='0c3d4c62ecf5f74c85b6589a0300c999945b8688'
h=lambda d:hashlib.sha256(d).hexdigest()
def save(n,x):(E/n).write_text(json.dumps(x,indent=2)+'\n')
rs=sorted([json.loads(p.read_text()) for p in (E/'attempts').glob('*/receipt.json')],key=lambda x:x['start_monotonic_ns'])
assert len(rs)==19 and sum(r['exit']==0 for r in rs)==18
assert len({r['attempt_id'] for r in rs})==len(rs)
assert len({(r['lock_device'],r['lock_inode']) for r in rs})==1
assert all(r['child_reaped'] for r in rs)
assert all(a['end_monotonic_ns']<b['start_monotonic_ns'] for a,b in zip(rs,rs[1:]))
for r in rs:
 for s in r['submitted_sources']:
  data=(E/'attempts'/r['attempt_id']/(s['sha256']+'.lean')).read_bytes()
  assert len(data)==s['bytes'] and h(data)==s['sha256']
  path=Path(s['path']);assert data==path.read_bytes()
  assert data==subprocess.check_output(['git','show',SOURCE+':'+str(path.relative_to(ROOT))],cwd=ROOT)
 assert '-j1' in r['argv'] and '-DwarningAsError=true' in r['argv'] and '-DautoImplicit=false' in r['argv']
assert rs[-1]['label']=='dependency-LightEFTSpanners.TreePruning' and rs[-1]['exit']!=0
raw=(E/'attempts'/rs[-1]['attempt_id']/'raw.log').read_text()
assert 'hKG' in raw and 'not explicitly referenced' in raw
warnings=[dict(id=r['attempt_id'],line=line) for r in rs for line in (E/'attempts'/r['attempt_id']/'raw.log').read_text().splitlines() if re.match(r'^.*:\d+:\d+: warning:',line)]
save('execution-reconciliation.json',dict(attempts=len(rs),successful=18,failed=1,unique_ids=True,one_lock_inode=True,nonoverlap=True,all_children_reaped=True,source_snapshots_match_frozen_commit=True,warning_headers=warnings,blocker=rs[-1]['attempt_id'],classification='inherited unused-variable linter promoted to error by strict warning policy'))
objects=[]
for x in json.loads((E/'reused-objects.json').read_text()):
 data=(ROOT/x['path']).read_bytes();assert h(data)==x['sha256'] and len(data)==x['bytes'];objects.append(x)
for r in rs:
 if r['exit']!=0:continue
 mod=r['label'].removeprefix('dependency-');p=ROOT/'.lake/build/lib/lean'/Path(*mod.split('.')).with_suffix('.olean');data=p.read_bytes();objects.append(dict(module=mod,path=str(p.relative_to(ROOT)),sha256=h(data),bytes=len(data)))
sources=json.loads((E/'source-graph.json').read_text())
for row in sources:
 data=(ROOT/row['path']).read_bytes();assert h(data)==row['sha256']
 assert data==subprocess.check_output(['git','show',PARENT+':'+row['path']],cwd=ROOT)
save('source-object-hashes.json',dict(tested_source=SOURCE,parent=PARENT,all_486_closure_sources_unchanged=True,objects=objects,sources=sources,full_aggregate_compiled=False,full_replay=False,full_audit=False,ci_triggered=False))
old=ROOT/'checkpoints/light-eft-native-residual-20261016'
for row in json.loads((old/'evidence-sha256.json').read_text()):
 data=(old/row['path']).read_bytes();assert len(data)==row['bytes'] and h(data)==row['sha256']
original=json.loads(subprocess.check_output(['git','show',PARENT+':Light Edge Fault Tolerant Graph Spanners/verification/statement-map.json'],cwd=ROOT))
current=json.loads((ROOT/'Light Edge Fault Tolerant Graph Spanners/verification/statement-map.json').read_text())
assert [{k:v for k,v in x.items() if k!='current_native_coverage'} for x in current]==original
pins=json.loads((ROOT/'lake-manifest.json').read_text())['packages'];assert len(pins)==9
out=[]
for pin in pins:
 p=Path('/workspace/paper-formalizations/.lake/packages')/pin['name'];rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip();assert rev==pin['rev'];out.append(dict(name=pin['name'],rev=rev,status=subprocess.check_output(['git','status','--porcelain'],cwd=p,text=True)))
save('dependency-pins.json',out)
t=Path('/workspace/toolchains/lean-4.34.0-linux/bin');save('toolchain-hashes.json',{str(p):h(p.read_bytes()) for p in [t/'lean',t/'leanchecker',ROOT/'lean-toolchain',ROOT/'lake-manifest.json']})
ps=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True);assert not any(x.split()[-1] in ['lean','lake','leanchecker'] for x in ps.splitlines()[1:])
with open('/tmp/distance-sparsification-single-compiler.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 save('terminal-state.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),compiler_lock_free=True,processes=ps,disk=subprocess.check_output(['df','-h',str(ROOT)],text=True),memory_limit=Path('/sys/fs/cgroup/memory.max').read_text().strip(),cpu_quota=Path('/sys/fs/cgroup/cpu.max').read_text().strip()))
print(json.dumps(dict(receipts=len(rs),strict_success=18,strict_failure=1,preserved_closure_sources=len(sources),objects=len(objects),prior_evidence_preserved=True)))
