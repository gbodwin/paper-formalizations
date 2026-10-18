"""Offline evidence reconciliation only: never spawns a fixture or Lean process."""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, subprocess

B=Path(__file__).resolve().parent
R=B.parents[1]
OLD=R/'checkpoints/light-eft-batch343-with-aggregate-20261018'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def save(name, data): (B/name).write_text(json.dumps(data,indent=2)+'\n')

before=load(B/'preservation-before.json')
root=R/'.lake/light-eft-batch100-entries72-171-20261017-ee496fe7834c4e86994b3933112caff7'
members=sorted(str(p.relative_to(R)) for name in ['objects','resolutions'] for p in (root/name).rglob('*') if p.is_file())
assert members==sorted(row['path'] for row in before['bindings'])
for row in before['bindings']:
    p=R/row['path'];s=p.stat()
    assert [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]==row['identity'],str(p)
    assert s.st_size==row['bytes'] and sha(p)==row['sha256'],str(p)
core=root/'objects/LightEFTSpanners/CorePartitionBudget.olean'
assert core.stat().st_size==83848 and sha(core)=='1767dd8c642b0f2f8bf31119c76e9ce8a9a8464bd46eca8534175e2b21fcd233'
oldmanifest=load(OLD/'evidence-sha256.json')
assert len(oldmanifest)==1269
for row in oldmanifest:
    p=OLD/row['path']
    assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],str(p)
original=load(OLD/'attempts/138-LightEFTSpanners.CorePartitionBudget-replay/receipt.json')
saved=load(B/'saved-mixed-snapshot.json')
assert saved['stop_decision_sample']==original['stop_decision_sample']
assert original['state']=='failed' and original['exit']==0
assert saved['attempt_id']==original['attempt_id']

receipts=[];leases=[]
for suite in ['memory-reread-fixtures','whole-process-fixtures','effective-reread-fixtures']:
    for p in (B/suite).rglob('receipt.json'):
        row=load(p);row['_path']=str(p.relative_to(B));receipts.append(row)
        folder=p.parent.parent if suite=='whole-process-fixtures' else p.parent
        lease=load(folder/'lease.json');leases.append(lease)
        assert lease['state']=='released' and lease['kernel_echild_at_release']
        assert row['direct_reaped'] and row['direct_wait_owner']=='runner wait4'
        source=folder/'submitted.py'
        assert sha(source)==row['submitted_source_sha256']
        for name,h in row['harness_hashes'].items():
            snapshot=B/'harness-snapshots'/(h+'.py')
            assert sha(snapshot)==h, (name,h)
        assert row['compiler_or_checker'] is False and row['fixture_only'] is True
assert len(receipts)==66
assert len({row['attempt_id'] for row in receipts})==len(receipts)
assert {(row['lock']['device'],row['lock']['inode']) for row in receipts}=={(33,3849)}
receipts.sort(key=lambda row:row['started_ns'])
assert all(a['ended_ns']<b['started_ns'] for a,b in zip(receipts,receipts[1:]))
leases.sort(key=lambda row:row['acquired_ns'])
assert all(a['released_ns']<b['acquired_ns'] for a,b in zip(leases,leases[1:]))
failed=[row for row in receipts if row.get('passed') is False]
assert len(failed)==2 and {r['case'] for r in failed}=={'fresh_gone','grace_expiry'}
final_new=list(B.glob('memory-reread-results-*.json'));assert len(final_new)==1
new_results=load(final_new[0])['cases']
whole=load(B/'whole-process-fixture-results.json')['cases']
effective=load(B/'effective-reread-fixture-results.json')['cases']
assert [len(x) for x in [new_results,whole,effective]]==[18,14,12]
for result in new_results+whole+effective:
    assert result['passed']
    row=load(B/result['receipt'])
    assert row['state']=='finished' or (row['state']=='failed' and 'child_exit' in result)
    assert row['kernel_no_children_verified']
for row in load(B/'unchanged-controls.json'):
    p=R/row['name'] if row['name'].startswith('scripts/') else B/row['name']
    assert sha(p)==row['sha256']
    if not row['name'].startswith('test_') and not row['name'].startswith('scripts/'):
        assert p.read_bytes()==(OLD/row['name']).read_bytes()
assert not subprocess.check_output(['git','diff','95b0256dfdf05bf415248c764510701f1b7d5dfc','--',
    'Light Edge Fault Tolerant Graph Spanners','lean-toolchain','lake-manifest.json','scripts/LightEFTProcessLifecycle.py'],cwd=R)

active=[]
for p in Path('/proc').iterdir():
    if not p.name.isdigit():continue
    try:
        comm=(p/'comm').read_text().strip();s=(p/'stat').read_text();state=s[s.rfind(')')+2:].split()[0]
        if state!='Z' and comm in ('lean','lake','leanchecker','leantar','strace'):active.append({'pid':int(p.name),'comm':comm})
    except (FileNotFoundError,PermissionError,ProcessLookupError):pass
assert not active
lockpath=Path('/tmp/distance-sparsification-single-compiler.lock')
with lockpath.open('r+') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    s=os.fstat(lock.fileno());assert(s.st_dev,s.st_ino)==(33,3849)
    fcntl.flock(lock,fcntl.LOCK_UN)
summary={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope':'offline read-only content/receipt checks; no Lean, fixture invocation, advice, or full frozen-input pass',
    'base_commit':before['base_commit'],'frozen_source_commit':before['source_commit'],
    'new_final_regressions_passed':18,'retained_whole_process_passed':14,'retained_effective_reread_passed':12,
    'total_final_regressions_passed':44,'total_fixture_attempts_including_preserved_failed_attempts':66,
    'preserved_failed_fixture_setup_attempts':[{'case':row['case'],'receipt':row['_path'],'failure':row['failure']} for row in failed],
    'all_unique_attempt_ids':True,'one_universal_lock_inode':True,'all_attempts_and_leases_nonoverlapping':True,
    'all_direct_children_owned_wait4_reaped':True,'all_leases_kernel_echild_at_release':True,
    'root_object_count':417,'root_resolution_count':346,'unchanged_root_bindings':len(members),
    'original_evidence_manifest_entries_verified':len(oldmanifest),'original_evidence_manifest_sha256':sha(OLD/'evidence-sha256.json'),
    'original_CorePartitionBudget_replay_still_rejected':True,'core_object_bytes':core.stat().st_size,'core_object_sha256':sha(core),
    'core_replay_attempt_id':original['attempt_id'],'active_compiler_checker_tracer':active,
    'lock_free':True,'lock_device':33,'lock_inode':3849,'no_production_continuation':True}
save('reconciliation.json',summary)
print(json.dumps(summary,indent=2))
