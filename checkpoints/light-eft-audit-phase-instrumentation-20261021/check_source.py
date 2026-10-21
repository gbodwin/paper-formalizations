"""Exact additive instrumentation, finite logs and existing spec semantics only."""
from pathlib import Path
import ast,copy,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parent;R=H.parents[1];sys.path.insert(0,str(H))
from instrument import AUDIT,PHASES,instrument,uninstrument
from phase_report import MAX_BYTES
BASE='7a7993f5c3a9c1efad1a7b8ca6c2a6c51031d03c'
git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
base=git('show',BASE+':'+AUDIT).decode();actual=(R/AUDIT).read_text()
assert actual==instrument(base) and uninstrument(actual)==base
for namespace in ['LightEFTAuditCollision','LightEFTAuditText']:
    def block(text):return text.split('namespace '+namespace,1)[1].split('end '+namespace,1)[0]
    assert block(base)==block(actual)
labels=['frontend-ready']+re.findall(r'LightEFTAuditTiming.mark "([a-z-]+)"',actual)
assert tuple(labels)==PHASES and len(labels)==len(set(labels))==16 and MAX_BYTES<=2048
assert all(not any(token in label for token in ['COLLISION','collision-']) for label in labels)
assert actual.count('IO.monoMsNow')==2 and actual.count('out.flush')==base.count('out.flush')+2
new_helper=actual.split('namespace LightEFTAuditTiming',1)[1].split('end LightEFTAuditTiming',1)[0]
assert new_helper.count('IO.monoMsNow')==1 and new_helper.count('IO.getStdout')==1
assert all(text not in new_helper for text in ['IO.getEnv','IO.FS.','unsafe','partial','while ','for ','getEnv','getUsedConstants'])
names=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
       'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']
def row(path):
    raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
bound=0;changed=[]
for i,name in enumerate(names):
    rel='checkpoints/'+name+'/ci-spec.json';before=json.loads(git('show',BASE+':'+rel));after=json.loads((R/rel).read_text());expected=copy.deepcopy(before)
    if i==1:expected['sources']['audit']=row(AUDIT)
    expected['engine_files']=[row(r['path']) for r in before['engine_files']]
    assert after==expected,'Unexpected source/spec/resource/path-set delta: '+rel
    source=after['sources'];source=list(source.values()) if isinstance(source,dict) else source
    for b in [*source,*after['dependencies'],*after['engine_files']]:
        assert all(b[k]==row(b['path'])[k] for k in ['path','bytes','sha256']);bound+=1
    if before!=after:changed.append(rel)
assert len(changed)==4 and 'checkpoints/'+names[0]+'/ci-spec.json' not in changed
allowed={AUDIT,*changed};paths=set(git('diff','--name-only',BASE).decode().splitlines())|set(git('ls-files','--others','--exclude-standard').decode().splitlines())
assert all(path in allowed or path.startswith(str(H.relative_to(R))+'/') for path in paths),paths-allowed
for p in H.glob('*.py'):ast.parse(p.read_text())
git('diff','--check',BASE)
print(json.dumps(dict(status='PASS_EXACT_SOURCE_ONLY',baseline=BASE,audit_sha256=row(AUDIT)['sha256'],
    phases=len(labels),max_additional_stdout_bytes=MAX_BYTES,hot_loop_clock_reads=0,
    exact_inverse_restores_entire_audit=True,collision_and_cache_namespaces='byte-identical',
    production_binding_rows=bound,changed_specifications=changed,
    limits_checks_outputs_workflows_runtime_engines='unchanged',Lean_elaboration='not attempted',
    performance='unknown; instrumentation overhead unmeasured',compiler_push_CI=False),indent=2))
