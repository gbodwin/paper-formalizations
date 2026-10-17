"""Exactly one traced compilation; stop regardless of compiler outcome."""
from pathlib import Path
import datetime,json,subprocess,shutil,traceback
import pilot_runner as p
import pid_observations as observations
import trace_supervisor
BASE=Path(__file__).resolve().parent
if __name__=='__main__':
    with (BASE/'invocation-claimed.json').open('x') as f:json.dump({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'one_traced_compile_only':True},f)
    state={'source_commit':p.SOURCE,'scope':'COMPILE_ONLY_NO_RESOLVER_OR_CHECKER','no_retry':True}
    try:
        original=subprocess.check_output(['git','show',p.SOURCE+':'+str(p.PROJECT_SOURCE.relative_to(p.REPO))],cwd=p.REPO)
        if original!=p.PROJECT_SOURCE.read_bytes():raise RuntimeError('Source differs from frozen production')
        if p.PILOT.exists() or p.EVIDENCE.exists():raise RuntimeError('Fresh-path collision')
        p.PILOT.mkdir();p.OUT.mkdir();p.OBJECT.parent.mkdir();state['initial_outputs']=[]
        observations.snapshot('compile-before.json',admit=True)
        plan={'stage':'compile','source':str(p.PROJECT_SOURCE),'argv':p.stage_argv('compile'),'env':p.environment('compile'),'cwd':str(p.PILOT),'inputs':None,'object_bindings':[]}
        try:receipt=trace_supervisor.run(plan,p.EVIDENCE/'compile');state.update(status='traced-compilation-exit-zero',attempt_id=receipt['attempt_id'])
        finally:observations.snapshot('compile-after.json')
    except BaseException as exc:state.update(status='stopped-first-failure',failure=repr(exc));traceback.print_exc()
    finally:
        state['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        if p.OUT.exists():
            state['terminal_objects']=p.object_inventory()
            if state['terminal_objects']:shutil.copytree(p.OUT,BASE/'preserved-outputs')
        with (BASE/'chain-result.json').open('w') as f:json.dump(state,f,indent=2);f.write('\n')
    raise SystemExit(0 if state.get('status')=='traced-compilation-exit-zero' else 1)
