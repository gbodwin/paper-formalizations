"""One finite compile -> official resolution -> singleton replay chain; no retries."""
from pathlib import Path
import datetime,hashlib,json,shutil,subprocess,traceback
import pilot_runner as p
import pid_observations as observations
BASE=Path(__file__).resolve().parent

def save(data):
    temp=BASE/'chain-result.tmp';temp.write_text(json.dumps(data,indent=2)+'\n');temp.replace(BASE/'chain-result.json')

def main():
    with (BASE/'invocation-claimed.json').open('x') as f:
        json.dump({'one_finite_chain':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},f)
    state={'frozen_production':p.SOURCE,'stages':[],'status':'preparing','no_retries':True}
    save(state)
    try:
        original=subprocess.check_output(['git','show',p.SOURCE+':'+str(p.PROJECT_SOURCE.relative_to(p.REPO))],cwd=p.REPO)
        if original!=p.PROJECT_SOURCE.read_bytes():raise RuntimeError('Project source differs from frozen production')
        if p.PILOT.exists() or p.EVIDENCE.exists():raise RuntimeError('Fresh path collision; do not retry')
        p.PILOT.mkdir();p.OUT.mkdir();p.OBJECT.parent.mkdir()
        state['initial_project_output_files']=[str(x) for x in p.OUT.rglob('*') if x.is_file()]
        if state['initial_project_output_files']:raise RuntimeError('Nonempty output root')
        for stage in ['compile','resolve','replay']:
            state['status']='running-'+stage;save(state)
            observations.snapshot(stage+'-before.json',admit=True)
            source=p.RESOLVER if stage=='resolve' else p.PROJECT_SOURCE
            plan={'stage':stage,'source':str(source),'argv':p.stage_argv(stage),'env':p.environment(stage),'cwd':str(p.PILOT),'inputs':None,'object_bindings':[] if stage=='compile' else p.object_inventory()}
            try:
                receipt=p._run(plan,p.PILOT,p.EVIDENCE/stage)
            finally:
                observations.snapshot(stage+'-after.json')
            state['stages'].append({'stage':stage,'attempt_id':receipt['attempt_id'],'exit':receipt['exit'],'receipt':str((p.EVIDENCE/stage/'receipt.json').relative_to(BASE))})
            if stage=='compile':
                if not p.OBJECT.is_file():raise RuntimeError('Compile succeeded without target object')
                state['fresh_objects']=p.object_inventory()
            if stage=='resolve':state['official_resolution']=p.verify_resolution()
            if stage=='replay' and (p.EVIDENCE/stage/'raw.log').read_text().strip()!='replaying '+p.MODULE:
                raise RuntimeError('Unexpected singleton replay diagnostic')
            save(state);print(stage+' PASS',flush=True)
        state['status']='bounded-three-stage-chain-passed'
    except BaseException as exc:
        state['failure']=repr(exc);state['status']='stopped-first-failure';traceback.print_exc()
    finally:
        if p.OUT.exists():
            state['terminal_objects']=p.object_inventory()
            if state['terminal_objects']:shutil.copytree(p.OUT,BASE/'preserved-outputs')
        if p.RESOLUTION.exists():shutil.copy2(p.RESOLUTION,BASE/'official-resolution.json')
        state['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save(state)
    return 0 if state['status']=='bounded-three-stage-chain-passed' else 1

if __name__=='__main__':raise SystemExit(main())
