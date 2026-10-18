"""Metadata/source hashing only. Never executes Lean/checkers or changes pins."""
from pathlib import Path
import datetime, hashlib, json, subprocess, shutil
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
BASE='b9a834db12a89733f2aa6156877298c5ddc368a4'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
assert git('branch','--show-current').decode().strip()=='light-eft-spanners-checkpoints'
subprocess.run(['git','merge-base','--is-ancestor',BASE,'HEAD'],cwd=ROOT,check=True)
graph=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/frozen-graph.json'
rows=json.loads(graph.read_text());assert len(rows)==486
queries=''.join(SOURCE+':'+r['path']+'\n' for r in rows)
result=subprocess.run(['git','cat-file','--batch'],input=queries.encode(),stdout=subprocess.PIPE,check=True,cwd=ROOT).stdout
position=0
for r in rows:
 stop=result.index(b'\n',position);header=result[position:stop].split()
 assert header[1]==b'blob',header
 size=int(header[2]);b=result[stop+1:stop+1+size];position=stop+size+2
 assert len(b)==size and sha(b)==r['sha256']==sha((ROOT/r['path']).read_bytes()),r['path']
assert position==len(result)
pins=[]
for name in ['lean-toolchain','lake-manifest.json']:
 b=(ROOT/name).read_bytes();assert b==git('show',SOURCE+':'+name)
 pins.append(dict(path=name,bytes=len(b),sha256=sha(b)))
interfaces=json.loads((HERE/'interfaces.json').read_text())
assert interfaces['mathematical_source']==SOURCE
for row in interfaces['interfaces']:
 p=ROOT/row['path'];b=p.read_bytes();assert sha(b)==row['source_sha256']
 assert row['declaration'] in b.decode().splitlines()[row['line']-1]
assert git('diff','--name-only')==b''
assert git('diff','--cached','--name-only')==b''
for path in git('diff','--name-only',BASE,'HEAD').decode().splitlines():
 assert path.startswith('checkpoints/light-eft-theorem13-integration-plan-20261018/'),path
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  name=(p/'comm').read_text().strip()
  if name in {'lean','leanchecker','lake','leantar'}:active.append(dict(pid=int(p.name),name=name))
 except OSError:pass
assert not active,active
lock=Path('/tmp/distance-sparsification-single-compiler.lock')
lock_observation=dict(path=str(lock),exists=lock.exists(),created_or_acquired=False,continuity_claim=False)
if lock.exists():
 st=lock.stat();lock_observation.update(device=st.st_dev,inode=st.st_ino)
else:lock_observation['note']='Historical lock absent in this session. No free-inode or historical continuity claim.'
memory=dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
r=dict(kind='read-only source analysis and metadata reconciliation; no proof execution',
 observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 branch=git('branch','--show-current').decode().strip(),observed_head=git('rev-parse','HEAD').decode().strip(),
 starting_head=BASE,mathematical_source=SOURCE,verified_source_hashes=len(rows),
 frozen_graph_path=str(graph.relative_to(ROOT)),frozen_graph_sha256=sha(graph.read_bytes()),
 exact_source_interfaces=len(interfaces['interfaces']),pin_bindings=pins,
 dependency_revision_pins=[dict(name=p['name'],revision=p['rev']) for p in json.loads((ROOT/'lake-manifest.json').read_text())['packages']],
 existing_tracked_changes=[],prior_proofs_and_evidence_unchanged=True,
 untracked_status=git('status','--porcelain=v1').decode().splitlines(),
 lock=lock_observation,active_compilers=active,compiler_or_checker_invocations=0,
 disk_free_bytes=shutil.disk_usage(ROOT).free,host_mem_available_kib=int(memory['MemAvailable'].split()[0]),
 cgroup_memory_max=Path('/sys/fs/cgroup/memory.max').read_text().strip(),
 proposed_lemma_status='planning only; not implemented or Lean-checked')
(HERE/'preservation.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['observed_utc','branch','observed_head','verified_source_hashes','exact_source_interfaces','lock','active_compilers','compiler_or_checker_invocations']},indent=2))
