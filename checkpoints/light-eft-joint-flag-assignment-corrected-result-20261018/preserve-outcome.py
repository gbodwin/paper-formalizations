"""Preserve/reconcile the one completed attempt. No compiler, retry or lock API."""
from pathlib import Path
import datetime, hashlib, json, re, shutil, subprocess, sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
ADAPTER = ROOT/'checkpoints/light-eft-joint-flag-assignment-corrected-adapter-20261018'
DRAFT = ROOT/'checkpoints/light-eft-joint-flag-assignment-corrected-draft-20261018'
EVIDENCE = DRAFT/'future-validation-evidence'
SOURCE = '7a4ab29cebfdd86808d4d6708411967fdb4a3bd4'
IMPLEMENTATION = '154e108179324f74f163049f2fe450be5522d616'
sys.path.insert(0,str(ADAPTER))
from focused_audit import chunk, verify_chunks, validate
from contracts import warning_lines

def sha(b): return hashlib.sha256(b).hexdigest()
def load(p): return json.loads(p.read_text())
def save(name,data): (HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def binding(p):
    p=Path(p);b=p.read_bytes();s=p.stat()
    return dict(path=str(p),bytes=len(b),sha256=sha(b),identity=[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns])

plan=load(DRAFT/'focused-validation-plan.json')
WORK=Path(plan['future_work_root'])
result=load(EVIDENCE/'result.json');invocation=load(HERE/'invocation-result.json')
assert result==invocation
lease=load(EVIDENCE/'lease.json')
preview=load(ADAPTER/'concrete-plan-preview.json')
checks=dict(result_matches_invocation=True,not_synthetic=result.get('synthetic_fixture') is False,
    preservation_passed=result.get('preservation_failed') is False,
    clean_release=lease.get('state')=='released' and lease.get('kernel_echild') is True and not lease.get('release_errors'),
    exact_released_inode=(lease.get('device'),lease.get('inode'))==(33,3258),
    exact_prior_epoch=lease.get('prior_released_epoch')=='9dd0d7e576bc4fb7b7fa05d4413d4bff')
receipts=[];commands=[];diagnostics=[];previous=0;ids=set()
header=re.compile(r'^(.+?):(\d+):(\d+): (warning|error)(\([^)]*\))?: (.*)$',re.M)
for p in preview:
    stage=p['stage'];folder=EVIDENCE/stage;rp=folder/'receipt.json';r=load(rp) if rp.exists() else None
    commands.append(dict(stage=stage,argv=p['argv'],environment=p['env'],working_directory=p['cwd'],
        submitted_sources=p['source_bindings'],receipt_present=r is not None,
        child_pid=r.get('child_pid') if r else None,status='not run after first failure' if r is None else r.get('state'),
        exit=r.get('exit') if r else None))
    if r is None:continue
    ids.add(r['attempt_id'])
    rc=dict(stage=stage,attempt_id=r['attempt_id'],receipt=binding(rp),
        source_commit=r.get('source_commit'),wrapper_commit=r.get('wrapper_commit'),
        state=r.get('state'),exit=r.get('exit'),child_pid=r.get('child_pid'),supervisor_pid=r.get('supervisor_pid'),
        started_ns=r.get('started_ns'),ended_ns=r.get('ended_ns'),created_utc=r.get('created_utc'),ended_utc=r.get('ended_utc'),
        direct_reaped=r.get('direct_reaped'),all_descendants_gone=r.get('all_descendants_gone'),
        kernel_no_children_verified=r.get('kernel_no_children_verified'),waitid_wait4_status_match=r.get('waitid_wait4_status_match'),
        preexec_binding_verified=r.get('preexec_binding_verified'),between_child_preservation_passed=r.get('between_child_preservation_passed'),
        kernel_limits_verified=r.get('kernel_limits_verified'),cleanup_errors=r.get('cleanup_errors'),failure=r.get('failure'),
        disk_admission_bytes=r.get('disk_admission_bytes'),preexec_disk_bytes=r.get('preexec_disk_bytes'),
        admission=r.get('admission'),preexec_admission=r.get('preexec_admission'),
        kernel_limits=r.get('handshake',{}).get('limits'),memory_policy=r.get('memory_policy'),
        wait4_maxrss_kib=r.get('wait4_maxrss_kib'),sampled_rss_peak_bytes=r.get('sampled_rss_peak_bytes'),
        sampled_vm_peak_bytes=r.get('sampled_vm_peak_bytes'),outputs_after=r.get('outputs_after'))
    receipts.append(rc)
    checks[stage+'_exact_command']=r['source_commit']==SOURCE and r['wrapper_commit']==IMPLEMENTATION and r['argv']==p['argv'] and r['environment']==p['env'] and r['working_directory']==p['cwd'] and r['planned_source_bindings']==p['source_bindings']
    checks[stage+'_inside_lease_nonoverlap']=lease['acquired_ns']<=r['started_ns']<r['ended_ns']<=lease['release_ns'] and previous<r['started_ns']
    previous=r['ended_ns']
    checks[stage+'_owned_children_reaped']=all(r.get(k) is True for k in ['direct_reaped','all_descendants_gone','kernel_no_children_verified','waitid_wait4_status_match']) and not r.get('cleanup_errors')
    for row in r.get('submitted_sources',[]):
        data=(folder/row['snapshot']).read_bytes()
        assert len(data)==row['bytes'] and sha(data)==row['sha256']
        assert binding(row['path'])=={k:row[k] for k in ['path','bytes','sha256','identity']}
    for name,row in r.get('completed_logs',{}).items():assert binding(folder/name)==row
    raw=(folder/'raw.log').read_text() if (folder/'raw.log').exists() else ''
    found=[]
    for match in header.finditer(raw):
        path,line,column,severity,code,message=match.groups()
        kind='elaboration' if severity=='error' else 'warning'
        if message.startswith('unexpected token '):kind='parser'
        if message.startswith('automatically included section variable(s) unused'):kind='promoted_unused_section_variables'
        if message.startswith('This simp argument is unused:'):kind='promoted_unused_simp_argument'
        found.append(dict(stage=stage,path=path,line=int(line),column=int(column),severity=severity,code=code,
            classification=kind,message=message,raw_header=match.group(0)))
    diagnostics.extend(found)
    rc['raw_diagnostics']=binding(folder/'raw.log') if (folder/'raw.log').exists() else None
    rc['anchored_diagnostic_headers']=len(found)
    rc['reviewed_warning_error_classifier_matches']=warning_lines(raw)
checks['unique_attempt_UUIDs']=len(ids)==len(receipts)

inputs={r['path']:r for r in map(json.loads,(EVIDENCE/'inputs.jsonl').read_text().splitlines())}
preserved=load(ADAPTER/'accepted-preservation-policy.json')['objects']
for row in preserved:
    for key in ['source','object']:
        expected=row[key]
        assert inputs[expected['path']]==expected and binding(expected['path'])==expected
checks['all_six_preservation_only_bindings_unchanged']=True
for key in ['source','audit','resolver']:assert binding(plan[key]['path'])==plan[key]
deps=load(DRAFT/'project-dependency-bindings.json')['dependencies']
assert len(deps)==77
for row in deps:
    for key in ['source','object']:assert binding(row[key]['path'])==row[key]
checks['all_77_dependency_bindings_unchanged']=True

artifacts=HERE/'partial-artifacts';artifacts.mkdir(exist_ok=False);copies=[];tree=[]
for p in sorted(WORK.rglob('*')):
    assert not p.is_symlink()
    tree.append(dict(path=str(p.relative_to(WORK)),kind='directory' if p.is_dir() else 'file'))
    if p.is_file():
        dest=artifacts/p.relative_to(WORK);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
        assert p.read_bytes()==dest.read_bytes();copies.append(dict(original=binding(p),copy=binding(dest)))
save('partial-artifact-bindings.json',copies)
save('work-tree.json',dict(root=str(WORK),entries=tree,produced_files=len(copies)))

# Preserve existing successful-driver exports as-is; export every other raw
# runtime file and every work output exactly once into additional readable chunks.
existing=[];excluded={'exports','input-export','excluded-initial-export','excluded-final-export'}
for mp in sorted(EVIDENCE.rglob('manifest.json')):
    m=load(mp)
    if 'parts' not in m:continue
    verify_chunks(mp.parent,Path(m['source']))
    existing.append(dict(manifest=str(mp.relative_to(ROOT)),source=m['source'],bytes=m['bytes'],sha256=m['sha256'],parts=len(m['parts']),reconstruction_verified=True))
save('driver-export-index.json',existing)
export=HERE/'available-exports';export.mkdir(exist_ok=False);index=[]
sources=[(p,Path('runtime')/p.relative_to(EVIDENCE)) for p in sorted(EVIDENCE.rglob('*')) if p.is_file() and p.relative_to(EVIDENCE).parts[0] not in excluded]
sources += [(p,Path('work')/p.relative_to(WORK)) for p in sorted(WORK.rglob('*')) if p.is_file()]
for source,rel in sources:
    dest=export/rel;m=chunk(source,dest,target=200000);verify_chunks(dest,source)
    index.append(dict(source=str(source),manifest=str((dest/'manifest.json').relative_to(ROOT)),bytes=m['bytes'],sha256=m['sha256'],parts=len(m['parts']),reconstruction_verified=True))
save('available-export-index.json',index)
audit=None
if (EVIDENCE/'audit/receipt.json').exists() and load(EVIDENCE/'audit/receipt.json').get('exit')==0:
    audit=validate(WORK/'audit/ci-evidence',{r['module']:r['object'] for r in deps},(EVIDENCE/'audit/raw.log').read_text())
if result.get('accepted'):
    from scope import verify_receipts
    verify_receipts(EVIDENCE,lease,preview and [dict(stage=p['stage'],module=plan['module'],argv=p['argv'],env=p['env'],sources=[r['path'] for r in p['source_bindings']],source_bindings=p['source_bindings'],cwd=p['cwd']) for p in preview],
        {r['module']:dict(r['object'],module=r['module']) for r in deps},IMPLEMENTATION)
    checks['successful_four_stage_receipts_reverified']=True
    checks['audit_output_revalidated']=audit==result['result']['audit']
save('diagnostic-classification.json',dict(method='Anchored source:line:column severity headers, including coded errors; raw logs and reviewed classifier matches retained separately',
    headers=diagnostics,errors=sum(x['severity']=='error' for x in diagnostics),warnings=sum(x['severity']=='warning' for x in diagnostics),
    elaboration_errors=sum(x['classification']=='elaboration' for x in diagnostics),
    parser_errors=sum(x['classification']=='parser' for x in diagnostics),
    promoted_linter_errors=sum(x['classification'].startswith('promoted_') for x in diagnostics)))
save('commands.json',dict(one_approved_attempt=True,no_automatic_retry=True,stages=commands))
save('execution-summary.json',dict(source_commit=SOURCE,implementation_commit=IMPLEMENTATION,accepted_by_adapter=result.get('accepted'),
    independent_review='pending; no new mathematical acceptance claimed',result=result,checks=checks,stages=receipts,
    new_source=plan['source'],audit=audit,accepted_pairs_unchanged=preserved,dependency_count=77,
    expected_imports=78,required_roots=16,required_interfaces=8,lease=lease,lease_receipt=binding(EVIDENCE/'lease.json'),
    driver_export_manifests=len(existing),driver_export_chunks=sum(x['parts'] for x in existing),
    available_export_manifests=len(index),available_export_chunks=sum(x['parts'] for x in index),all_exports_reconstructed=True))
processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
active=[x for x in processes.splitlines()[1:] if x.split()[-1] in ['lean','lake','leanchecker','leantar','strace'] and not x.split()[2].startswith('Z')]
assert not active
(HERE/'final-idle-processes.txt').write_text(processes)
save('final-idle.json',dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),active_compilers=active,
    lease_state=lease['state'],kernel_echild=lease.get('kernel_echild'),no_post_release_lock_acquisition=True))
print(json.dumps(dict(adapter_accepted=result.get('accepted'),stages=[(r['stage'],r['exit']) for r in receipts],
    reconciliation_checks_all_passed=all(checks.values()),diagnostic_errors=sum(x['severity']=='error' for x in diagnostics),
    diagnostic_warnings=sum(x['severity']=='warning' for x in diagnostics),audit=audit,
    available_exports=len(index),available_chunks=sum(x['parts'] for x in index),
    driver_exports=len(existing),driver_chunks=sum(x['parts'] for x in existing),
    work_files_preserved=len(copies),clean_release=checks['clean_release'],idle=True),indent=2))
