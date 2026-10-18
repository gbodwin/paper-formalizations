"""Reconcile/export the completed failed attempt; never launches Lean or takes a lock."""
from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess,sys
ROOT=Path('/workspace/light-eft-verification')
HERE=Path(__file__).resolve().parent
ADAPTER=ROOT/'checkpoints/light-eft-joint-flag-assignment-adapter-20261018'
DRAFT=ROOT/'checkpoints/light-eft-joint-flag-assignment-draft-20261018'
EVIDENCE=DRAFT/'future-validation-evidence'
WORK=ROOT/'.lake/joint-flag-assignment-76a78fe87ed74ab395396879287c05bb'
SOURCE='33e162e467cea919ee60d2c17e1f13d8586caba3'
IMPLEMENTATION='41f4e793e8d56f754c152964b5af9c2445f2706e'
sys.path.insert(0,str(ADAPTER))
from focused_audit import chunk,verify_chunks
def sha(data):return hashlib.sha256(data).hexdigest()
def load(path):return json.loads(path.read_bytes())
def save(name,data):(HERE/name).write_text(json.dumps(data,indent=2)+'\n')
def binding(path):
 data=path.read_bytes();s=path.stat()
 return dict(path=str(path),bytes=len(data),sha256=sha(data),identity=[s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns])

result=load(EVIDENCE/'result.json');assert result==load(HERE/'invocation-result.json')
assert result['accepted'] is False and result['synthetic_fixture'] is False and not result['preservation_failed']
assert result['stages']==[] and result.get('failure')
receipt=load(EVIDENCE/'compile/receipt.json');lease=load(EVIDENCE/'lease.json')
plan=load(ADAPTER/'concrete-plan-preview.json')[0]
assert receipt['stage']=='compile' and receipt['state']=='failed' and receipt['exit']==1
assert receipt['source_commit']==SOURCE and receipt['wrapper_commit']==IMPLEMENTATION
assert receipt['argv']==plan['argv'] and receipt['environment']==plan['env']
assert receipt['working_directory']==plan['cwd'] and receipt['planned_source_bindings']==plan['source_bindings']
assert receipt['supervisor_pid']==lease['supervisor_pid']
assert all(receipt[k] for k in ['direct_reaped','all_descendants_gone','kernel_no_children_verified',
 'waitid_wait4_status_match','between_child_preservation_passed','preexec_binding_verified','kernel_limits_verified'])
assert not receipt.get('cleanup_errors') and not receipt.get('memory_stop_attempted') and not receipt.get('stop_decision_errors')
assert lease['state']=='released' and lease['kernel_echild'] and not lease.get('release_errors')
assert (lease['device'],lease['inode'])==(33,3258) and lease['directory_identity']==[33,1]
assert lease['prior_released_epoch']=='f9446665c62e4e5c90b1578b930dd6ec'
assert lease['acquired_ns']<=receipt['started_ns']<receipt['ended_ns']<=lease['release_ns']
assert receipt['terminal_confirmation']['terminal'] and receipt['terminal_confirmation']['pid']==receipt['child_pid'] and receipt['terminal_confirmation']['status']==1
assert receipt['runtime_wall_started_ns']<=receipt['preexec_verified_ns']<=receipt['terminal_confirmation']['finished_ns']<receipt['runtime_wall_started_ns']+90*10**9
for row in receipt['submitted_sources']:
 data=(EVIDENCE/'compile'/row['snapshot']).read_bytes();assert len(data)==row['bytes'] and sha(data)==row['sha256']
 assert binding(Path(row['path']))=={k:row[k] for k in ['path','bytes','sha256','identity']}
for name,row in receipt['completed_logs'].items():assert binding(EVIDENCE/'compile'/name)==row
assert [p.parent.name for p in EVIDENCE.glob('*/receipt.json')]==['compile']
for stage in ['resolve','replay','audit']:assert not (EVIDENCE/stage).exists()
assert receipt['outputs_after']=={'new_objects':[],'resolution':[]}

inputs={row['path']:row for row in map(json.loads,(EVIDENCE/'inputs.jsonl').read_text().splitlines())}
policy=load(ADAPTER/'accepted-preservation-policy.json');preserved=[]
for row in policy['objects']:
 for key in ['source','object']:
  expected=row[key];assert inputs[expected['path']]==expected and binding(Path(expected['path']))==expected
 preserved.append(row)
assert len(preserved)==3
source_bindings=load(DRAFT/'draft-bindings.json')
for key in ['source','audit','resolver']:assert binding(Path(source_bindings[key]['path']))==source_bindings[key]

rawpath=EVIDENCE/'compile/raw.log';raw=rawpath.read_text()
regex=re.compile(r'^(.+?):(\d+):(\d+): (warning|error)(\([^)]*\))?: (.*)$',re.M)
diagnostics=[]
for match in regex.finditer(raw):
 path,line,column,severity,code,message=match.groups()
 kind='elaboration'
 if message.startswith('automatically included section variable(s) unused'):kind='promoted_unused_section_variables'
 if message.startswith('This simp argument is unused:'):kind='promoted_unused_simp_argument'
 diagnostics.append(dict(path=path,line=int(line),column=int(column),severity=severity,code=code,classification=kind,message=message,raw_header=match.group(0)))
assert len(diagnostics)==13 and all(x['severity']=='error' for x in diagnostics)
counts={kind:sum(x['classification']==kind for x in diagnostics) for kind in ['elaboration','promoted_unused_section_variables','promoted_unused_simp_argument']}
assert counts=={'elaboration':4,'promoted_unused_section_variables':4,'promoted_unused_simp_argument':5}
save('diagnostic-classification.json',dict(raw=binding(rawpath),method='Anchored source:line:column severity headers including coded error(...); hints/notes/allocator text are not counted',headers=diagnostics,
 error_diagnostics=13,unpromoted_warning_diagnostics=0,class_counts=counts,strict_warningAsError=True))

work_tree=[];artifacts=HERE/'partial-artifacts';artifacts.mkdir(exist_ok=False);copies=[]
for path in sorted(WORK.rglob('*')):
 assert not path.is_symlink()
 work_tree.append(dict(path=str(path.relative_to(WORK)),kind='directory' if path.is_dir() else 'file'))
 if path.is_file():
  dest=artifacts/path.relative_to(WORK);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(path,dest)
  assert path.read_bytes()==dest.read_bytes();copies.append(dict(original=binding(path),copy=binding(dest)))
assert not copies
save('work-tree.json',dict(root=str(WORK),entries=work_tree,produced_files=0,new_object=None,resolution=None,audit_exports=None))
save('partial-artifact-bindings.json',copies)

exports=HERE/'available-exports';exports.mkdir(exist_ok=False);index=[]
for source in sorted(p for p in EVIDENCE.rglob('*') if p.is_file()):
 directory=exports/source.relative_to(EVIDENCE);manifest=chunk(source,directory,target=200000)
 verify_chunks(directory,source)
 index.append(dict(source=str(source),manifest=str((directory/'manifest.json').relative_to(ROOT)),bytes=manifest['bytes'],sha256=manifest['sha256'],parts=len(manifest['parts']),reconstruction_verified=True))
save('available-export-index.json',index)
commands=[dict(stage=p['stage'],argv=p['argv'],environment=p['env'],working_directory=p['cwd'],submitted_sources=p['source_bindings'],executed=p['stage']=='compile',status='failed' if p['stage']=='compile' else 'skipped after first failure') for p in load(ADAPTER/'concrete-plan-preview.json')]
save('commands.json',dict(approved_one_attempt=True,no_automatic_retry=True,stages=commands,
 invocation='python3 -B checkpoints/light-eft-joint-flag-assignment-result-20261018/invoke-once.py > checkpoints/light-eft-joint-flag-assignment-result-20261018/invocation-raw.log 2>&1',
 postprocess='python3 -B checkpoints/light-eft-joint-flag-assignment-result-20261018/preserve-failure.py > checkpoints/light-eft-joint-flag-assignment-result-20261018/preserve-failure-attempt-1.log 2>&1'))
summary=dict(outcome='COMPILE FAILED; first-failure stop, no retry; no theorem acceptance',source_commit=SOURCE,implementation_commit=IMPLEMENTATION,
 target='LightEFTJointFlagSamplingStage.JointAssignmentLaw',source_bindings=source_bindings,
 attempt_id=receipt['attempt_id'],child_pid=receipt['child_pid'],supervisor_pid=receipt['supervisor_pid'],exit=1,
 source_commit_receipt=receipt['source_commit'],argv=receipt['argv'],environment=receipt['environment'],cwd=receipt['working_directory'],
 compile_receipt=binding(EVIDENCE/'compile/receipt.json'),raw_diagnostics=binding(rawpath),error_diagnostics=13,elaboration_errors=4,promoted_linter_errors=9,unpromoted_warnings=0,
 kernel_limits=receipt['handshake']['limits'],memory_policy=receipt['memory_policy'],wait4_maxrss_kib=receipt['wait4_maxrss_kib'],sampled_rss_peak_bytes=receipt['sampled_rss_peak_bytes'],sampled_vm_peak_bytes=receipt['sampled_vm_peak_bytes'],
 preexec_visible_headroom_bytes=receipt['preexec_admission']['headroom'],disk_admission_bytes=receipt['disk_admission_bytes'],preexec_disk_bytes=receipt['preexec_disk_bytes'],
 preservation_passed=receipt['between_child_preservation_passed'],three_accepted_pairs_unchanged=preserved,dependencies=77,
 resolution='NOT RUN',singleton_replay='NOT RUN',recursive_audit='NOT RUN',required_roots_and_interfaces='planned 16/eight; no executed root or recursive acceptance result',
 new_object=None,lease=lease,lease_receipt=binding(EVIDENCE/'lease.json'),no_cleanup_errors=True,all_children_reaped=True,
 signature_qualification=receipt['signature_supplement']['qualification'],export_manifests=len(index),export_chunks=sum(x['parts'] for x in index),all_available_exports_reconstructed=True)
save('execution-summary.json',summary)
processes=subprocess.check_output(['ps','-eo','pid,ppid,stat,comm'],text=True)
assert not [x for x in processes.splitlines()[1:] if x.split()[-1] in ['lean','lake','leanchecker','leantar','strace'] and not x.split()[2].startswith('Z')]
(HERE/'final-idle-processes.txt').write_text(processes)
save('final-idle.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),active_compiler_checker_extractor_tracer_count=0,lease_state=lease['state'],kernel_echild=lease['kernel_echild']))
print(json.dumps(dict(outcome='compile failed, no retry',error_diagnostics=13,promoted_linter_errors=9,elaboration_errors=4,
 available_export_manifests=len(index),chunks=sum(x['parts'] for x in index),all_reconstructed=True,accepted_pairs_unchanged=3,clean_ECHILD_release=True,idle=True)))
