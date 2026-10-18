"""Read-only environment/input checks; writes only this preparation checkpoint."""
from pathlib import Path
import datetime, hashlib, json, os, re, shutil, subprocess, sys
ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
BASE='aafb18253721ed2af3403a8904da61cd13357b95'
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
assert git('branch','--show-current').strip()=='light-eft-spanners-checkpoints'
assert git('diff','--name-only')=='' and git('diff','--cached','--name-only')==''
graph=ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/frozen-graph.json'
rows=json.loads(graph.read_text());assert len(rows)==486
assert all(sha(ROOT/r['path'])==r['sha256'] for r in rows)
for pin in ['lean-toolchain','lake-manifest.json']:
 assert (ROOT/pin).read_text()==git('show',SOURCE+':'+pin)
draft=HERE/'staged/LightEFTSpanners/SuppliedForestGoodEvent.lean'
assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial)\b',draft.read_text())
modules=['LightEFTSpanners.'+m for m in ['VotingOutput','VotingOutputWeight','ForestComponentPacking','ConstructedVotingHosts','ConnectivityOptimum']]
lookup={r['module']:r for r in rows};seen=set();todo=modules[:]
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);todo.extend(lookup[m]['project_imports'])
old=ROOT/'checkpoints/light-eft-audit-adapter-review-20261018'
old_plan=json.loads((old/'PLAN.json').read_text())
run=old/'executions/cece4176767e4d6cba0bcef97e5da486'
inventory=run/'inputs.jsonl'
bound={}
for line in inventory.open():
 row=json.loads(line)
 if row['role']=='project_object':bound[row['path']]=row
project_objects=Path(old_plan['retained_root'])/'objects'
bindings=[]
for m in sorted(seen):
 p=project_objects/Path(*m.split('.')).with_suffix('.olean')
 row=bound[str(p)];actual=sha(p);assert actual==row['sha256'],str(p)
 st=p.stat()
 bindings.append(dict(module=m,path=str(p),bytes=st.st_size,sha256=actual,prior_identity=row['identity'],current_identity=[st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns]))
save('accepted-imports.json',dict(mathematical_source=SOURCE,direct_imports=modules,
 frozen_light_eft_import_closure=len(seen),bindings=bindings,
 accepted_full_input_inventory=dict(path=str(inventory.relative_to(ROOT)),sha256=sha(inventory)),
 note='196 LightEFT project objects rehashed here. Other transitive accepted library objects remain covered by preserved input inventory, not freshly rehashed in this preparation. No imported object was recompiled.'))
# Observations only: no acquisition and no file creation at the lock path.
sys.path.insert(0,str(ROOT/'checkpoints/light-eft-finitelaw-admission3-chain-20261017'))
from pilot_accounting import VisibleAccounting
try:account=VisibleAccounting().sample()
except Exception as exc:account=dict(failure=repr(exc),partial=getattr(exc,'partial',None))
old_receipt=json.loads((run/'attempt/receipt.json').read_text())
self_pid=os.getpid();ancestors=set();cursor=self_pid
while cursor:
 ancestors.add(cursor)
 try:cursor=int((Path('/proc')/str(cursor)/'stat').read_text().split(') ',1)[1].split()[1])
 except (OSError,IndexError,ValueError):break
processes=[];compilers=[];workers=[];lock_fds=[];fd_errors=[]
for p in sorted(Path('/proc').iterdir(),key=lambda p:int(p.name) if p.name.isdigit() else -1):
 if not p.name.isdigit():continue
 try:
  comm=(p/'comm').read_text().strip();fields=(p/'stat').read_text().split(') ',1)[1].split()
  row=dict(pid=int(p.name),ppid=int(fields[1]),state=fields[0],comm=comm,ancestor=int(p.name) in ancestors)
  processes.append(row)
  if comm in {'lean','leanchecker','lake','leantar'} and row['state']!='Z':compilers.append(row)
  if not row['ancestor'] and comm in {'codex','python','python3','python3.12'} and row['state']!='Z':workers.append(row)
  try:
   for f in (p/'fd').iterdir():
    try:
     target=os.readlink(f)
     if target in ['/tmp/distance-sparsification-single-compiler.lock','/tmp/distance-sparsification-single-compiler.lock (deleted)']:
      lock_fds.append(dict(pid=int(p.name),fd=f.name,target=target))
    except OSError:pass
  except OSError as exc:fd_errors.append(dict(pid=int(p.name),error=repr(exc)))
 except (OSError,IndexError,ValueError):pass
assert not compilers and not workers,(compilers,workers)
lock=Path('/tmp/distance-sparsification-single-compiler.lock');assert not lock.exists()
namespaces={}
for ns in ['mnt','pid','cgroup','ipc','user']:
 try:namespaces[ns]=os.readlink('/proc/self/ns/'+ns)
 except OSError as exc:namespaces[ns]=repr(exc)
pid1_ns={}
for ns in ['mnt','pid']:
 try:pid1_ns[ns]=os.readlink('/proc/1/ns/'+ns)
 except OSError as exc:pid1_ns[ns]=repr(exc)
btime=int(next(s.split()[1] for s in Path('/proc/stat').read_text().splitlines() if s.startswith('btime ')))
start=int(Path('/proc/1/stat').read_text().split(') ',1)[1].split()[19])
pid1_start=datetime.datetime.fromtimestamp(btime+start/os.sysconf('SC_CLK_TCK'),datetime.timezone.utc).isoformat()
state=dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 starting_head=BASE,observed_head=git('rev-parse','HEAD').strip(),branch=git('branch','--show-current').strip(),
 mathematical_source=SOURCE,source_hashes_preserved=486,frozen_graph_sha256=sha(graph),
 pin_hashes={p:sha(ROOT/p) for p in ['lean-toolchain','lake-manifest.json']},
 draft=dict(path=str(draft.relative_to(ROOT)),bytes=draft.stat().st_size,sha256=sha(draft),compiled=False,promoted=False),
 processes=processes,visible_ordinary_worker_candidates=workers,active_compilers=compilers,
 disk_free_bytes=shutil.disk_usage(ROOT).free,visible_accounting=account,
 boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),observer_namespaces=namespaces,pid1_namespace_observations=pid1_ns,pid1_start_utc=pid1_start,
 lock=dict(path=str(lock),exists=False,created=False,acquired=False,historical_identity_continuity=False,
  current_tmp_identity=[Path('/tmp').stat().st_dev,Path('/tmp').stat().st_ino],
  visible_matching_open_descriptors=lock_fds,fd_scan_permission_errors=fd_errors,
  visible_kernel_locks=Path('/proc/locks').read_text(),
  qualification='Only readable processes/FDs/current visible lock table inspected; inaccessible namespaces and FDs are not proven idle.'),
 prior_audit=dict(created_utc=old_receipt['created_utc'],supervisor_pid=old_receipt['supervisor_pid'],
 child_pid=old_receipt['child_pid'],lock=old_receipt['lock'],cgroup_namespace=old_receipt['admission']['namespace'],
 historical_pids_currently_exist={str(pid):Path('/proc',str(pid)).exists() for pid in [old_receipt['supervisor_pid'],old_receipt['child_pid']]}),
 runtime_state_conclusion='Current PID1 began after historical audit; no continuous process/ownership epoch is established. Cgroup namespace text matches the old receipt, which does not establish lock/mount continuity. Workspace source/object hashes persist.',
 compiler_invocations=0,lock_operations=0,new_lemma_status='staged proof draft, uncompiled and unverified')
save('environment.json',state)
save('supervisor-bindings.json',[dict(path=str(p.relative_to(ROOT)),sha256=sha(p)) for p in [
 ROOT/'scripts/LightEFTExactSupervisor.py',ROOT/'scripts/LightEFTSequential.py',ROOT/'scripts/LightEFTCgroup.py',
 ROOT/'scripts/LightEFTProcessLifecycle.py',ROOT/'scripts/LightEFTResolveCheckerTarget.lean',
 ROOT/'checkpoints/light-eft-finitelaw-admission3-chain-20261017/pilot_runner.py',
 ROOT/'checkpoints/light-eft-finitelaw-admission3-chain-20261017/pilot_child.py',
 ROOT/'checkpoints/light-eft-finitelaw-admission3-chain-20261017/pilot_accounting.py',
 old/'shared_preservation.py',ROOT/'checkpoints/light-eft-clean-context-preparation-20261018/clean_contract.py']])
print(json.dumps(dict(source_hashes_preserved=486,accepted_import_objects_rehashed=len(bindings),
 draft_sha256=sha(draft),active_compilers=compilers,ordinary_worker_candidates=workers,
 lock_exists=lock.exists(),readable_lock_descriptor_matches=lock_fds,fd_permission_errors=len(fd_errors),
 disk_free_bytes=state['disk_free_bytes'],visible_headroom=account.get('headroom'),host_available=account.get('system_available'),compiler_invocations=0),indent=2))
