"""Conjoin mandatory job statuses and exact commit outputs; never transfers objects."""
from pathlib import Path
import json, os, re, sys
from workflow_identity import ROOT,exact_controls,head,identity,require

def aggregate(needs,commit):
    require(isinstance(commit,str) and re.fullmatch('[0-9a-f]{40}',commit) is not None,'Invalid event commit')
    require(isinstance(needs,dict) and set(needs)=={'check','focused'},'Both mandatory jobs required')
    for name in ['check','focused']:
        row=needs[name]
        require(isinstance(row,dict) and row.get('result')=='success','Mandatory '+name+' job did not succeed')
        require(isinstance(row.get('outputs'),dict) and row['outputs'].get('validated_commit')==commit,
                'Mandatory '+name+' exact commit output differs/missing')
    return dict(accepted=True,commit=commit,full_required=True,focused_required=True,
                qualification='Job-status conjunction only; complete artifacts and independent result review still required')

def destination(env,prefix):
    for name in ['GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT']:
        require(env.get(name,'').isdecimal() and int(env[name])>0,'Invalid run identity')
    temp=Path(env['RUNNER_TEMP'])
    require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(),'Invalid runner temporary root')
    root=temp/(prefix+'-'+env['GITHUB_RUN_ID']+'-'+env['GITHUB_RUN_ATTEMPT'])
    root.mkdir(mode=0o700,exist_ok=False)
    return root

def main():
    env=dict(os.environ);mode=sys.argv[1]
    if mode=='aggregate':
        root=destination(env,'light-eft-combined-acceptance')
        record=dict(accepted=False,commit=env.get('GITHUB_SHA'),run_id=env['GITHUB_RUN_ID'],
                    run_attempt=env['GITHUB_RUN_ATTEMPT'])
        try:
            record['needs']=json.loads(env['LIGHTEFT_NEEDS_JSON'])
            record['controls']=exact_controls()
            require(head()==env.get('GITHUB_SHA') and env.get('GITHUB_JOB')=='acceptance','Aggregation checkout/job differs')
            require(env.get('GITHUB_ACTIONS')=='true' and env.get('GITHUB_REPOSITORY')=='gbodwin/paper-formalizations' and
                    env.get('GITHUB_WORKFLOW')=='Lean' and env.get('GITHUB_WORKFLOW_SHA')==env.get('GITHUB_SHA') and
                    env.get('GITHUB_WORKFLOW_REF')=='gbodwin/paper-formalizations/.github/workflows/lean.yml@'+env.get('GITHUB_REF',''),
                    'Aggregation caller workflow differs')
            record.update(aggregate(record['needs'],env['GITHUB_SHA']))
        except BaseException as e:
            record['failure']=repr(e);raise
        finally:(root/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    elif mode=='mark':
        controls=exact_controls();commit=head();ci=identity(env,commit)
        require(sys.argv[2]==env['LIGHTEFT_VALIDATION_ROLE'],'Mark role differs')
        with open(env['GITHUB_OUTPUT'],'a') as f:f.write('commit='+commit+'\n')
        print(json.dumps(dict(status='COMPLETED_JOB_BODY_COMMIT_MARKER',CI_identity=ci,controls=controls)))
    elif mode=='summary':
        root=destination(env,'light-eft-focused-summary')
        record=dict(accepted=False,commit=env.get('GITHUB_SHA'))
        try:
            record['outcomes']=json.loads(env['LIGHTEFT_FOCUSED_OUTCOMES'])
            record['controls']=exact_controls();record['CI_identity']=identity(env,head())
            record['qualification']='Focused job evidence only; full validation and final aggregation are mandatory'
        except BaseException as e:record['failure']=repr(e);raise
        finally:(root/'workflow-summary.json').write_text(json.dumps(record,indent=2)+'\n')
    else:raise ValueError('Unknown finite status operation')

if __name__=='__main__':main()
