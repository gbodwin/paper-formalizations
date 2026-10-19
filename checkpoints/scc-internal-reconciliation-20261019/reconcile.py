"""Read-only reconciliation of preserved evidence; never invokes Lean/checkers."""
from pathlib import Path
import csv, datetime, fcntl, hashlib, io, json, os, re, shutil, subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'checkpoints/scc-internal-20261016'
SOURCE = 'b2f6cbd033c8aa87597f09d11aa7f3655f1e245d'
EVIDENCE = '5b6873aa7061149b187bb5e8e7999181fff5b40d'
BASE = 'b3ea492e33df053dd186d0fe1d7c7499909c2fb0'
MODULE = 'A Note on Distance-Preserving Graph Sparsification/SlackSparsification/SCCInternal.lean'
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT)
def bound(p, item):
    b = p.read_bytes()
    assert sha(b) == item['sha256'], str(p)
    if 'bytes' in item: assert len(b) == item['bytes'], str(p)
    return b

manifest = json.loads((OLD / 'evidence-sha256.json').read_text())
for row in manifest: bound(OLD / row['path'], row)
chunks = json.loads((OLD / 'audit-export/manifest.json').read_text())
reconstructed = b''.join(bound(OLD/'audit-export'/r['path'],r) for r in chunks['parts'])
assert len(reconstructed) == chunks['bytes'] and sha(reconstructed) == chunks['sha256']
assert reconstructed == (ROOT / chunks['source']).read_bytes()

records = [json.loads(s) for s in (OLD/'evidence/commands.jsonl').read_text().splitlines()]
assert len(records) == len({r['attempt_id'] for r in records}) == 4
previous = 0
for r in records:
    d = OLD/'evidence/attempts'/r['attempt_id']
    assert json.loads((d/'receipt.json').read_text()) == r
    assert r['child_reaped'] and r['state'] == 'finished-lock-held'
    assert (r['lock_device'],r['lock_inode']) == (33,3849)
    assert previous < r['lock_acquired_monotonic_ns'] <= r['start_monotonic_ns'] <= r['end_monotonic_ns']
    previous = r['end_monotonic_ns']
    for s in r['submitted_sources']:
        bound(d/(s['sha256']+'.lean'),s)
        bound(OLD/'evidence/sources'/(s['sha256']+'.lean'),s)
assert [r['exit'] for r in records] == [1,0,0,0]
assert [r['label'] for r in records] == ['compile-SCCInternal','compile-SCCInternal','replay-SCCInternal','audit-SCCInternal']
assert all(option in records[1]['argv'] for option in ['-j1','-DautoImplicit=false','-DwarningAsError=true'])
assert records[2]['argv'] == ['/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker','-v','SlackSparsification.SCCInternal']
source_bytes = git('show',SOURCE+':'+MODULE)
assert sha(source_bytes) == '07755149fd36fc495bc55900e98bf4358ee098aba1b2f0b21f459e367e8323ed'
assert (ROOT/MODULE).read_bytes() == source_bytes
assert all(r['submitted_sources'][0]['sha256'] == sha(source_bytes) for r in records[1:3])
assert not re.search(rb'\b(sorry|admit|axiom)\b',source_bytes)

bindings = json.loads((OLD/'evidence/source-toolchain-object-hashes.json').read_text())
current_bindings = []
for row in bindings:
    p = Path(row['path'])
    if not p.is_absolute():
        # Objects are at the original execution worktree; source at frozen worktree.
        p = Path('/workspace/plus-six-evidence-publish')/p if row['path'].startswith('.lake/') else ROOT/p
    observed = sha(p.read_bytes()) if p.is_file() else None
    current_bindings.append(dict(row,observed_path=str(p),observed_sha256=observed,matches=observed==row['sha256']))
target = [r for r in current_bindings if r['path'].endswith('/SCCInternal.olean')]
assert len(target)==1 and target[0]['matches']
assert all(r['matches'] for r in current_bindings)

inventory = list(csv.DictReader(io.StringIO((OLD/'evidence/actual-owner-inventory.tsv').read_text()),delimiter='\t'))
closure = list(csv.DictReader(io.StringIO(reconstructed.decode()),delimiter='\t'))
names = {r['name'] for r in closure}
assert len(inventory)==223 and len(closure)==len(names)==18871
assert sum(r['owner']=='SlackSparsification.SCCInternal' for r in inventory)==9
assert all(r['unsafe']=='false' for r in inventory)
todo = [r['name'] for r in inventory]; seen=set(); lookup={r['name']:r for r in closure}
while todo:
    n=todo.pop()
    if n in seen: continue
    seen.add(n); r=lookup[n]
    todo += [s for k in ['typeDependencies','bodyDependencies'] for s in r[k].split(',') if s]
assert seen==names
axioms=sorted(r['name'] for r in closure if r['kind']=='axiom')
assert axioms==['Classical.choice','Quot.sound','propext']
assert sum(r['kind']=='opaque' for r in closure)==14
assert git('diff','--name-only',SOURCE,EVIDENCE,'--','A Note on Distance-Preserving Graph Sparsification','New Results on Linear Size Distance Preservers','lake-manifest.json','lean-toolchain')==b''
changed=git('diff','--name-only','11690f560db73f1f05ef121d5687a1e088168482',EVIDENCE).decode().splitlines()
assert all(p in [MODULE,'A Note on Distance-Preserving Graph Sparsification/verification/SCCInternalAudit.lean'] or p.startswith('checkpoints/scc-internal-20261016/') for p in changed)
lock=Path('/tmp/distance-sparsification-single-compiler.lock')
lock_observation = dict(path=str(lock), exists=lock.exists(), historical_device=33, historical_inode=3849, acquired=False)
if lock.exists():
    st = lock.stat()
    matches = []
    for line in Path('/proc/locks').read_text().splitlines():
        fields = line.split()
        for field in fields:
            if field.count(':') == 2:
                try:
                    major, minor, inode = field.split(':')
                    if int(major,16)==os.major(st.st_dev) and int(minor,16)==os.minor(st.st_dev) and int(inode)==st.st_ino:
                        matches.append(line)
                except ValueError:
                    pass
    lock_observation.update(device=st.st_dev,inode=st.st_ino,uid=st.st_uid,mode=oct(st.st_mode & 0o777),observed_locks=matches)
lock_observation['note']='Read-only current observation; no lock acquisition/replacement. Current inode is distinct from historical execution; no continuity claim.'
active=[]
for p in Path('/proc').iterdir():
    if not p.name.isdigit(): continue
    try:
        comm=(p/'comm').read_text().strip(); stat=(p/'stat').read_text().split(') ',1)[1].split()[0]
        if comm in {'lean','leanchecker','lake','leantar'} and stat!='Z': active.append({'pid':int(p.name),'comm':comm})
    except (OSError,IndexError): pass
assert not active
meminfo=Path('/proc/meminfo').read_text()
pins=[]
for p in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
    checkout=Path('/workspace/paper-formalizations/.lake/packages')/p['name']
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=checkout,text=True).strip()
    assert actual==p['rev']
    pins.append(dict(name=p['name'],expected=p['rev'],observed=actual))
result=dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),kind='source/log/hash reconciliation only; no fresh Lean execution or CI',tested_source=SOURCE,original_evidence_commit=EVIDENCE,accepted_predecessor=BASE,manifest_entries=len(manifest),chunks=len(chunks['parts']),reconstruction_bytes=len(reconstructed),reconstruction_sha256=sha(reconstructed),receipts=records,source_sha256=sha(source_bytes),source_bytes=len(source_bytes),bindings=current_bindings,roots=len(inventory),new_owner_roots=9,recursive_closure=len(closure),closure_edges_reconciled=True,opaque_bodies=14,axioms=axioms,original_diagnostics_preserved=True,prior_checkpoint_preserved=True,lock=lock_observation,active_compilers=active,disk_free_bytes=shutil.disk_usage(ROOT).free,mem_available_kib=int(re.search(r'MemAvailable:\s+(\d+)',meminfo)[1]),fresh_compiler_invocations=0,independent_review_of_new_endpoint='pending; this reconciliation does not grant acceptance')
result['installed_dependency_pins']=pins
result['memory_limit_bytes']=int(Path('/sys/fs/cgroup/memory.max').read_text())
(HERE/'reconciliation.json').write_text(json.dumps(result,indent=2)+'\n')
result['remote_checkpoint_before'] = git('ls-remote','origin','refs/heads/checkpoint/scc-internal-20261016').decode().strip()
result['warning_classification'] = dict(successful_compile_actual_warnings=len(re.findall(r'^.*?:[0-9]+:[0-9]+: warning:',(OLD/'evidence/compile-SCCInternal.log').read_text(),re.M)),failed_attempt='Subtype/Fintype cardinality elaboration mismatch; preserved proof repair, not mathematical counterexample')
assert result['warning_classification']['successful_compile_actual_warnings']==0
for prev in ['scc-internal-reconciliation-20261018','scc-internal-resume-20261018','scc-internal-confirmation-20261018']:
    p=ROOT/'checkpoints'/prev/'manifest.json'
    if p.exists():
        assert p.read_bytes()==git('show','HEAD:'+str(p.relative_to(ROOT)))
(HERE/'reconciliation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['observed_utc','tested_source','original_evidence_commit','manifest_entries','chunks','roots','recursive_closure','axioms','lock','active_compilers','disk_free_bytes','mem_available_kib','memory_limit_bytes','fresh_compiler_invocations','remote_checkpoint_before','warning_classification']},indent=2))
