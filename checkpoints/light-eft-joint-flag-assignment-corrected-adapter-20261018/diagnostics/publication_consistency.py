"""Local publication consistency only; no compiler, common lock or runtime inventory."""
from pathlib import Path
import hashlib, json, os, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
DRAFT = ROOT/'checkpoints/light-eft-joint-flag-assignment-corrected-draft-20261018'
SOURCE = '7a4ab29cebfdd86808d4d6708411967fdb4a3bd4'
IMPLEMENTATION = '154e108179324f74f163049f2fe450be5522d616'
FAILED = 'a76e0478e7618284d1a978c4bba0672f885afcdf'
def guard(event,args):
    if event=='subprocess.Popen':
        assert args[0]=='git' and args[1][0]=='git' and args[1][1] in ['show','ls-tree','diff','status']
    if event in ['fcntl.flock','os.fork','os.posix_spawn']: raise AssertionError('No runtime activation')
    if event=='open' and isinstance(args[0],(str,bytes,os.PathLike)):
        p=os.path.abspath(os.fsdecode(args[0]))
        assert p!='/tmp/distance-sparsification-single-compiler.lock' and not p.startswith(('/proc/','/sys/'))
sys.addaudithook(guard)
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def binding(row):
    p=Path(row['path']);b=p.read_bytes();st=p.stat()
    assert len(b)==row['bytes'] and sha(b)==row['sha256']
    assert [st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns]==row['identity']

manifest=load(DRAFT/'manifest.json')
for row in manifest['entries']:
    p=DRAFT/row['path'];b=p.read_bytes()
    assert len(b)==row['bytes'] and sha(b)==row['sha256']
    assert b==git('show',SOURCE+':'+str(p.relative_to(ROOT)))
assert (DRAFT/'manifest.json').read_bytes()==git('show',SOURCE+':'+str((DRAFT/'manifest.json').relative_to(ROOT)))
old=ROOT/'checkpoints/light-eft-joint-flag-assignment-draft-20261018'
same=[]
for name in ['project-dependency-bindings.json','project-dependency-bindings.jsonl','accepted-preservation-bindings.json','mathlib-interface-bindings.json']:
    assert (DRAFT/name).read_bytes()==(old/name).read_bytes();same.append(name)
plan=load(DRAFT/'focused-validation-plan.json');prior=load(old/'focused-validation-plan.json')
assert plan['resource_profile']==prior['resource_profile']
assert plan['focused_audit_expectations']==prior['focused_audit_expectations']
assert plan['stage_order']==prior['stage_order']
for c,p in zip(plan['commands'],prior['commands']):
    assert c['visible_admission_bytes']==p['visible_admission_bytes'] and c['executed'] is False
    assert c['argv'][0]==p['argv'][0]
    if c['stage']!='replay':assert c['argv'][1:6]==p['argv'][1:6]
assert not Path(plan['future_work_root']).exists() and not Path(plan['future_evidence_root']).exists()
assert not (HERE/'production-invocation-claimed.json').exists()
policy=load(HERE/'accepted-preservation-policy.json')
for row in policy['objects']:
    for key in ['source','object']:binding(row[key])
assert policy['objects']==load(old/'accepted-preservation-bindings.json')['objects']
assert policy['reviewed_draft_commit']==SOURCE
release=load(HERE/'released-lock.json');ref=release['receipt'];body=(ROOT/ref['path']).read_bytes()
assert body==git('show',FAILED+':'+ref['path'])
assert len(body)==719 and sha(body)=='06054c674a4566e9b344b7fd4c4c12f646c1c2a7a6b74b315538ef4d34e21aa1'
assert release['released_epoch']==json.loads(body)['epoch']=='9dd0d7e576bc4fb7b7fa05d4413d4bff'
assert release['identity']['device']==33 and release['identity']['inode']==3258
assert release['identity']['directory_identity']==[33,1]
assert json.loads(body)['state']=='released' and json.loads(body)['kernel_echild']
failed_dir=ROOT/'checkpoints/light-eft-joint-flag-assignment-result-20261018'
failed_manifest=load(failed_dir/'bundle-manifest.json')
for row in failed_manifest['entries']:
    b=(ROOT/row['path']).read_bytes()
    assert len(b)==row['bytes'] and sha(b)==row['sha256']
    assert b==git('show',FAILED+':'+row['path'])
assert (failed_dir/'bundle-manifest.json').read_bytes()==git('show',FAILED+':'+str((failed_dir/'bundle-manifest.json').relative_to(ROOT)))
result_dirs=list((HERE/'test-evidence').glob('*/result.json'));assert len(result_dirs)==1
tests=load(result_dirs[0]);assert tests['tests']==35 and tests['successful'] and tests['failures']==tests['errors']==0
check=load(HERE/'small-binding-check.json')
assert check['implementation_commit']==IMPLEMENTATION and check['draft_commit']==SOURCE
assert all(check[k]==0 for k in ['Lean_invocations','common_lock_acquisitions','real_inventory_scans','production_attempts','resource_or_ownership_probes'])
assert check['common_lock_opened'] is False and check['fresh_paths_and_claim_absent']
for p in HERE.glob('*.py'):
    assert p.read_bytes()==git('show',IMPLEMENTATION+':'+str(p.relative_to(ROOT)))
for n in ['released-lock.json','accepted-preservation-policy.json']:
    assert (HERE/n).read_bytes()==git('show',IMPLEMENTATION+':'+str((HERE/n).relative_to(ROOT)))
allowed=[str(p.relative_to(ROOT))+'/' for p in [HERE,DRAFT]]
changed=git('diff','--name-status',FAILED,IMPLEMENTATION).decode().splitlines()
assert all(row.startswith('A\t') and any(row[2:].startswith(p) for p in allowed) for row in changed)
assert git('diff','--name-only')==b''
untracked=git('status','--porcelain','--untracked-files=normal').decode().splitlines()
caches=[row[3:] for row in untracked if row.startswith('?? ') and '__pycache__' in row]
assert len(caches)==7
result=dict(kind='Publication consistency; no Lean execution or new mathematical acceptance',
    source_commit=SOURCE,implementation_commit=IMPLEMENTATION,accepted_failed_evidence=FAILED,
    source_sha256=plan['source']['sha256'],source_bytes=plan['source']['bytes'],
    corrected_draft_payloads=len(manifest['entries']),unchanged_binding_files=same,
    preserved_failed_payloads=len(failed_manifest['entries']),accepted_pairs_unchanged=3,
    preserved_cache_directories=caches,synthetic_tests=35,failures=0,errors=0,
    fresh_work_evidence_claim_absent=True,controls_unchanged=True,
    release=release,Lean_invocations=0,common_lock_opened=False,lock_acquisitions=0,
    real_inventory_scans=0,production_attempts=0)
(HERE/'publication-consistency.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
