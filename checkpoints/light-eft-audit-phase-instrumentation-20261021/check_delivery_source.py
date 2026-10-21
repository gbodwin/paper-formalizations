"""Exact e90f172f channel-only repair; no native execution or runtime gate."""
from pathlib import Path
import ast,copy,hashlib,json,subprocess,sys
H=Path(__file__).resolve().parent;R=H.parents[1];sys.path.insert(0,str(H))
from instrument import AUDIT,CHANNEL_SCOPE,CHANNEL_END,PHASES
from phase_report import MAX_BYTES
BASE='e90f172f653b90817418c7712432818fb2f34062'
IMPORTS='import Lean\nimport LightEFTJointFlagSamplingStage.JointAssignmentLaw\n\n'

def repair(old):
    assert old.startswith(IMPORTS) and 'stderrAsMessages' not in old
    prefix,rest=old.split('namespace LightEFTAuditCollision\n',1)
    assert prefix.count('IO.getStdout')==2
    prefix=prefix.replace('IO.getStdout','IO.getStderr')
    return prefix.replace(IMPORTS,IMPORTS+CHANNEL_SCOPE,1)+'namespace LightEFTAuditCollision\n'+rest+CHANNEL_END

def unrepair(new):
    assert new.startswith(IMPORTS+CHANNEL_SCOPE) and new.endswith(CHANNEL_END)
    text=new[len(IMPORTS+CHANNEL_SCOPE):-len(CHANNEL_END)]
    prefix,rest=text.split('namespace LightEFTAuditCollision\n',1)
    assert prefix.count('IO.getStderr')==2
    return IMPORTS+prefix.replace('IO.getStderr','IO.getStdout')+'namespace LightEFTAuditCollision\n'+rest

def validate_delivery(new,old):
    assert new==repair(old) and unrepair(new)==old,'Repair exceeds two getters and standalone restored scope'
    assert new.index(CHANNEL_SCOPE)<new.index('run_cmd do\n')
    assert new.count('set_option stderrAsMessages false\n')==1
    assert new.count('IO.getStderr')==2 and new.count('IO.getStdout')==old.count('IO.getStdout')-2
    assert new.endswith(CHANNEL_END)

def launcher_contract(runner,pilot):
    tree=ast.parse(runner)
    calls=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)
           and isinstance(n.func.value,ast.Name) and n.func.value.id=='subprocess' and n.func.attr=='Popen']
    assert len(calls)==1
    kwargs={k.arg:ast.unparse(k.value) for k in calls[0].keywords}
    assert kwargs.get('stdout')=='log' and kwargs.get('stderr')=='subprocess.STDOUT','Missing raw-log stderr merge'
    assert "with (evidence/'raw.log').open('xb') as log:" in runner
    p=ast.parse(pilot)
    assert any(isinstance(n,ast.Call) and ast.unparse(n.func)=='os.execve' for n in ast.walk(p))
    assert not any(isinstance(n,ast.Call) and ast.unparse(n.func) in ['os.dup2','os.close_range','os.closerange'] for n in ast.walk(p))
    assert 'sys.stderr =' not in pilot and 'sys.stdout =' not in pilot

def main():
    git=lambda *a:subprocess.check_output(['git','-C',str(R),*a])
    old=git('show',BASE+':'+AUDIT).decode();new=(R/AUDIT).read_text();validate_delivery(new,old)
    names=['light-eft-paid-focused-adapter-20261020','light-eft-joint-flag-ci-extension-revision-20261019',
           'light-eft-canonical-output-adapter-20261020','light-eft-paid-joint-bridge-ci-adapter-20261020','light-eft-fair-bit-batch-ci-adapter-20261021']
    def row(path):
        raw=(R/path).read_bytes();return dict(path=path,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
    bound=0;changed=[]
    for index,name in enumerate(names):
        rel='checkpoints/'+name+'/ci-spec.json';before=json.loads(git('show',BASE+':'+rel));after=json.loads((R/rel).read_text());expected=copy.deepcopy(before)
        if index==1:expected['sources']['audit']=row(AUDIT)
        expected['engine_files']=[row(r['path']) for r in before['engine_files']]
        assert after==expected,'Changed production scope, engine paths or contract: '+rel
        sources=after['sources'];sources=list(sources.values()) if isinstance(sources,dict) else sources
        for b in [*sources,*after['dependencies'],*after['engine_files']]:
            assert all(b[k]==row(b['path'])[k] for k in ['path','bytes','sha256']);bound+=1
        if before!=after:changed.append(rel)
    assert len(changed)==4
    allowed={AUDIT,*changed};paths=set(git('diff','--name-only',BASE).decode().splitlines())|set(git('ls-files','--others','--exclude-standard').decode().splitlines())
    assert all(p in allowed or p.startswith(str(H.relative_to(R))+'/') for p in paths)
    engine=R/'checkpoints/light-eft-joint-flag-assignment-corrected-adapter-20261018'
    runner=(engine/'child_runner.py').read_text();pilot=(engine/'pilot_child.py').read_text()
    for name in ['child_runner.py','pilot_child.py']:
        assert (engine/name).read_bytes()==git('show',BASE+':'+str((engine/name).relative_to(R)))
    launcher_contract(runner,pilot)
    for p in H.glob('*.py'):ast.parse(p.read_text())
    git('diff','--check',BASE)
    print(json.dumps(dict(status='PASS_SOURCE_DELIVERY_REPAIR_ONLY',baseline=BASE,audit_sha256=row(AUDIT)['sha256'],
        production_binding_rows=bound,runtime_changes='two stdout-to-stderr getters; standalone named section option and restored end',
        phases=len(PHASES),max_diagnostic_bytes=MAX_BYTES,collision_stdout='unchanged',
        stderr_merge='unchanged child_runner stderr=STDOUT to raw.log; pilot execve preserves descriptors',
        scope_restore='named section restores caller options on normal end; no forced global true',
        native_delivery='unqualified; no compiler run',limits_checks_exports_workflows='unchanged',compiler_push_CI=False),indent=2))

if __name__=='__main__':main()
