"""Export and reconcile completed evidence only; never launches Lean or acquires a lock."""
from pathlib import Path
import csv, datetime, hashlib, json, re, shutil, subprocess

REPO = Path('/workspace/light-eft-verification')
OUT = Path(__file__).resolve().parent
ADAPTER = REPO/'checkpoints/light-eft-supplied-forest-probability-adapter-20261018'
EVIDENCE = REPO/'checkpoints/light-eft-supplied-forest-probability-draft-20261018/future-validation-evidence'
WORK = REPO/'.lake/supplied-forest-probability-4c8d7848fa3c4b09bd648c9c587a0f83'
SOURCE = '88d297fa58a15406aac6e7c0ea3c85f65965d19a'
IMPLEMENTATION = 'b6483cccabdf4afdbb8004a768afe8ea9ed0ff32'

def digest(data): return hashlib.sha256(data).hexdigest()
def load(path): return json.loads(path.read_bytes())
def save(path, data): path.write_text(json.dumps(data, indent=2)+'\n')
def binding(path):
    b = path.read_bytes()
    return dict(path=str(path), bytes=len(b), sha256=digest(b))

result = load(EVIDENCE/'result.json')
assert result['accepted'] and not result['synthetic_fixture'] and not result['preservation_failed']
assert result['result']['preserved']
assert load(OUT/'invocation-result.json') == result
lease = load(EVIDENCE/'lease.json')
assert lease['state']=='released' and lease['kernel_echild']
assert (lease['device'],lease['inode'])==(33,3258)
assert lease['prior_released_epoch']=='7d164441f8ac44d9b9c316cdd79869f3'
plans=load(ADAPTER/'concrete-plan-preview.json')
stages=[]
previous=lease['acquired_ns']
for plan in plans:
    stage=plan['stage']; receipt=load(EVIDENCE/stage/'receipt.json')
    assert receipt['source_commit']==SOURCE and receipt['wrapper_commit']==IMPLEMENTATION
    assert receipt['argv']==plan['argv'] and receipt['environment']==plan['env']
    assert receipt['planned_source_bindings']==plan['source_bindings']
    assert receipt['working_directory']==plan['cwd']
    assert receipt['exit']==0 and receipt['state']=='finished'
    assert all(receipt[k] for k in ['direct_reaped','all_descendants_gone','kernel_no_children_verified','waitid_wait4_status_match','between_child_preservation_passed','preexec_binding_verified','kernel_limits_verified'])
    assert previous < receipt['started_ns'] < receipt['ended_ns'] < lease['release_ns']
    previous=receipt['ended_ns']
    for source in receipt['submitted_sources']:
        b=(EVIDENCE/stage/source['snapshot']).read_bytes()
        assert len(b)==source['bytes'] and digest(b)==source['sha256']
    for name,row in receipt['completed_logs'].items():
        b=(EVIDENCE/stage/name).read_bytes()
        assert len(b)==row['bytes'] and digest(b)==row['sha256']
    raw=(EVIDENCE/stage/'raw.log').read_text()
    diagnostics=re.findall(r'^(?:.*:\d+:\d+: )?(?:warning|error):.*$',raw,re.M)
    assert not diagnostics
    admission=receipt['preexec_admission']
    stages.append(dict(stage=stage,attempt_id=receipt['attempt_id'],child_pid=receipt['child_pid'],
        supervisor_pid=receipt['supervisor_pid'],exit=0,started_ns=receipt['started_ns'],ended_ns=receipt['ended_ns'],
        created_utc=receipt['created_utc'],ended_utc=receipt['ended_utc'],
        wait4_maxrss_kib=receipt['wait4_maxrss_kib'],sampled_rss_peak_bytes=receipt['sampled_rss_peak_bytes'],
        sampled_vm_peak_bytes=receipt['sampled_vm_peak_bytes'],disk_admission_bytes=receipt['disk_admission_bytes'],
        preexec_visible_headroom_bytes=admission['headroom'],
        raw_log=binding(EVIDENCE/stage/'raw.log'),lean_warnings=0,lean_errors=0,
        diagnostics_classification='Allocator options/statistics are informational; replay announcement and audit PASS are informational.',
        argv=receipt['argv'],environment=receipt['environment'],working_directory=receipt['working_directory'],
        sources=receipt['submitted_sources'],kernel_limits=receipt['handshake']['limits'],
        memory_policy=receipt['memory_policy'],reaped_and_kernel_echild=True))
assert [x['stage'] for x in stages]==['compile','resolve','replay','audit']
assert len({x['attempt_id'] for x in stages})==4

artifacts=OUT/'artifacts'; artifacts.mkdir(exist_ok=False)
copies=[]
for source in sorted(WORK.rglob('*')):
    if not source.is_file(): continue
    assert not source.is_symlink()
    target=artifacts/source.relative_to(WORK); target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
    assert source.read_bytes()==target.read_bytes()
    copies.append(dict(original=binding(source),preserved=binding(target)))
save(OUT/'artifact-bindings.json',copies)
object_path=WORK/'objects/LightEFTSuppliedForestProbabilityStage/PolynomialFailureProbability.olean'
assert binding(object_path)['sha256']=='0716fe2cc66dd6657243cfe6d5d34fb83722f59818d0cdb1838be0bf2d981eeb'

interfaces=['LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests',
 'LightEFTSpanners.SampledGreedy.polynomial_inaccurate_probability',
 'LightEFTSpanners.FiniteProbability.Law.prob_mono']
with (WORK/'audit/ci-evidence/recursive-dependencies.tsv').open() as f:
    nodes=list(csv.DictReader(f,delimiter='\t'))
names={x['name'] for x in nodes}
assert len(nodes)==len(names)==51084 and set(interfaces)<=names
save(OUT/'required-interface-rows.json',[x for x in nodes if x['name'] in interfaces])
audit=result['result']['audit']
assert audit['new_owner_roots']==1 and audit['recursive_constants']==51084 and audit['opaque_bodies']==44
assert audit['strict_findings']==0 and audit['recursive_types_and_bodies']
assert len(audit['project_imports'])==214
assert sorted(audit['axioms'])==['Classical.choice','Quot.sound','propext']
save(OUT/'audit-summary.json',audit)

# Validate all existing row-aligned exports against the untouched raw source.
chunk_index=[]
for path in sorted(EVIDENCE.rglob('manifest.json')):
    manifest=load(path)
    assert {'source','bytes','sha256','parts'}<=set(manifest)
    data=b''.join((path.parent/x['path']).read_bytes() for x in manifest['parts'])
    for x in manifest['parts']:
        b=(path.parent/x['path']).read_bytes(); assert len(b)==x['bytes'] and digest(b)==x['sha256']
    assert len(data)==manifest['bytes'] and digest(data)==manifest['sha256']
    assert data==Path(manifest['source']).read_bytes()
    chunk_index.append(dict(manifest=str(path.relative_to(REPO)),source=manifest['source'],
        bytes=len(data),sha256=digest(data),parts=len(manifest['parts']),reconstruction_verified=True))

# Receipts and decision samples get their own readable, ordered exports as well.
exports=OUT/'receipt-exports';exports.mkdir(exist_ok=False)
for stage in ['compile','resolve','replay','audit']:
    for name in ['receipt.json','samples.jsonl']:
        source=EVIDENCE/stage/name; data=source.read_bytes(); directory=exports/(stage+'-'+name)
        directory.mkdir();parts=[];buffer=bytearray()
        def flush():
            if not buffer:return
            path=directory/('part-%04d.txt'%len(parts));b=bytes(buffer);path.write_bytes(b)
            parts.append(dict(path=path.name,bytes=len(b),sha256=digest(b)));buffer.clear()
        for line in data.splitlines(keepends=True):
            if buffer and len(buffer)+len(line)>200000:flush()
            buffer.extend(line)
        flush()
        assert b''.join((directory/x['path']).read_bytes() for x in parts)==data
        manifest=dict(source=str(source),bytes=len(data),sha256=digest(data),row_aligned=True,target_bytes=200000,parts=parts)
        save(directory/'manifest.json',manifest)
        chunk_index.append(dict(manifest=str((directory/'manifest.json').relative_to(REPO)),source=str(source),
            bytes=len(data),sha256=digest(data),parts=len(parts),reconstruction_verified=True))
save(OUT/'chunk-index.json',chunk_index)

accepted=load(ADAPTER/'accepted-object-supplement.json')
accepted_binding=result['result']['signature_supplement']['accepted_object_binding']
assert binding(Path(accepted_binding['path']))=={k:accepted_binding[k] for k in ['path','bytes','sha256']}
tool_inputs=[]
with (EVIDENCE/'inputs.jsonl').open() as f:
    for line in f:
        x=json.loads(line)
        if x.get('path') in ['/workspace/toolchains/lean-4.34.0-linux/bin/lean','/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker']:
            tool_inputs.append(x)
save(OUT/'execution-summary.json',dict(status='All reviewed adapter gates passed; pending independent result review',
    source_commit=SOURCE,implementation_commit=IMPLEMENTATION,target='LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability',
    new_object=binding(object_path),accepted_dependency_unchanged=accepted_binding,toolchain=(REPO/'lean-toolchain').read_text().strip(),
    tool_inputs=tool_inputs,stages=stages,audit={k:v for k,v in audit.items() if k!='project_imports'},
    project_import_count=214,dependency_count=213,required_interfaces_reachable=interfaces,
    lease=lease,no_retry=True,failed_attempts_this_invocation=0,provenance_qualification=result['result']['signature_supplement']['qualification']))
processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
assert not [row for row in processes.splitlines()[1:] if row.split()[-1] in ['lean','lake','leanchecker','leantar','strace'] and not row.split()[2].startswith('Z')]
(OUT/'final-idle-processes.txt').write_text(processes)
save(OUT/'final-idle.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),active_compiler_checker_extractor_tracer_count=0,lease_state=lease['state'],kernel_echild=lease['kernel_echild']))
print(json.dumps(dict(stages=4,all_exit_zero=True,recursive_constants=51084,export_manifests_verified=len(chunk_index),
    chunks=sum(x['parts'] for x in chunk_index),raw_artifacts_copied=len(copies),idle=True)))
