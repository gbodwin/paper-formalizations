"""Run only after a recorded refused memory admission and no live compiler.
Verified per-file advisory cache release; no file deletion or limit change.
"""
from pathlib import Path
import json,hashlib,os,subprocess,fcntl,datetime,uuid,shutil,time
B=Path(__file__).resolve().parent;ROOT=B.parents[1];E=B/'evidence/startup-capacity'
rows=[json.loads(x) for x in (E/'memory-admissions.jsonl').read_text().splitlines()]
assert rows and not rows[-1]['admitted']
def observation():return dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),memory_current=int(Path('/sys/fs/cgroup/memory.current').read_text()),memory_max=int(Path('/sys/fs/cgroup/memory.max').read_text()),memory_stat=Path('/sys/fs/cgroup/memory.stat').read_text(),processes=subprocess.check_output(['ps','-eo','pid,ppid,rss,stat,comm'],text=True))
before=observation();assert not any(x.split()[-1] in ['lean','lake','leanchecker'] for x in before['processes'].splitlines()[1:])
lock=open('/tmp/distance-sparsification-single-compiler.lock','r')
lock_requested_utc=datetime.datetime.now(datetime.timezone.utc).isoformat();lock_requested_monotonic_ns=time.monotonic_ns()
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
lock_evidence=dict(path='/tmp/distance-sparsification-single-compiler.lock',operation='LOCK_EX | LOCK_NB',pid=os.getpid(),fd=lock.fileno(),device=os.fstat(lock.fileno()).st_dev,inode=os.fstat(lock.fileno()).st_ino,requested_utc=lock_requested_utc,requested_monotonic_ns=lock_requested_monotonic_ns,acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),acquired_monotonic_ns=time.monotonic_ns(),acquired=True)

ref=E/'refused-admissions'/rows[-1]['admission_id'];ref.mkdir(parents=True,exist_ok=True)
(ref/'admission.json').write_text(json.dumps(rows[-1],indent=2)+'\n');shutil.copy2(E/'fresh-build-state.json',ref/'build-state.json')
label=rows[-1]['label'];sources=[]
if label.startswith('fresh-compile-'):
 target=label.removeprefix('fresh-compile-');graph=json.loads((E/'source-graph.json').read_text());sources=[ROOT/r['path'] for r in graph if r['module']==target]
else:sources=list(B.glob('*.lean'))
for p in sources:
 d=p.read_bytes();sha=hashlib.sha256(d).hexdigest();(ref/(sha+'.lean')).write_bytes(d)
checkpoints=['light-eft-linked-rowticks-pilot-20261017','light-eft-sample-values-pilot-20261017','light-eft-sample-row-values-pilot-20261017','light-eft-record-values-pilot-20261017','light-eft-record-row-values-pilot-20261017','light-eft-record-row-steps-pilot-20261017','light-eft-rows-steps-pilot-20261017','light-eft-accurate-trace-pilot-20261017','light-eft-approved-history-pilot-20261017','light-eft-valid-schedule-resumed-20261017','light-eft-candidates-selected-pilot-20261017','light-eft-host-successes-pilot-20261016','light-eft-edge-membership-contains-pilot-20261016','light-eft-edge-membership-steps-pilot-20261016','light-eft-membership-contains-pilot-20261016','light-eft-membership-steps-pilot-20261016']
actions=[]
for name in checkpoints:
 entries=json.loads((ROOT/'checkpoints'/name/'evidence/source-object-provenance.json').read_text())
 for entry in entries:
  p=Path(entry['object_path']);assert p.is_relative_to(ROOT/'.lake') and p.suffix=='.olean' and not p.is_relative_to(ROOT/'.lake/linked-scan-pilot')
  with p.open('rb') as f:
   initial=os.fstat(f.fileno());sha=hashlib.file_digest(f,'sha256').hexdigest();assert sha==entry['object_sha256']
   os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)
   final=os.fstat(f.fileno());assert (initial.st_ino,initial.st_size,initial.st_mtime_ns)==(final.st_ino,final.st_size,final.st_mtime_ns)
  actions.append(dict(path=str(p),sha256_verified_before_advice=sha,bytes=initial.st_size,operation='POSIX_FADV_DONTNEED on read-only descriptor',inode_size_mtime_unchanged=True))
after=observation();lock_evidence.update(held_through_advice=True,advice_completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),advice_completed_monotonic_ns=time.monotonic_ns());assert (os.fstat(lock.fileno()).st_dev,os.fstat(lock.fileno()).st_ino)==(lock_evidence['device'],lock_evidence['inode']);fcntl.flock(lock,fcntl.LOCK_UN);lock.close();lock_evidence.update(released_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),released_monotonic_ns=time.monotonic_ns(),released=True);record=dict(lock=lock_evidence,refused_admission=rows[-1],before=before,after=after,actions=actions,qualification='Inactive prior task-created object files only; hashes verified against preserved provenance. No deletion, file writes, global cache drop, memory/security setting changes, process interference or gate weakening. Observations are not reservations.')
p=E/('cache-recovery-'+uuid.uuid4().hex+'.json');p.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(dict(record=str(p),files=len(actions),verified_bytes=sum(x['bytes'] for x in actions),before_headroom=before['memory_max']-before['memory_current'],after_headroom=after['memory_max']-after['memory_current']),indent=2))
