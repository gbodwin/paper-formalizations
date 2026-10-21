"""Exact ordinary-event binding and staged contracts; no dispatch-only admission gate."""
import collections, re
from pathlib import Path
import importlib.util
_fixture_spec=importlib.util.spec_from_file_location('_decoder_serialization_prerequisite',Path(__file__).with_name('ci_text_fixture.py'))
_fixture_module=importlib.util.module_from_spec(_fixture_spec);_fixture_spec.loader.exec_module(_fixture_module)
fixture_contract=_fixture_module.contract;fixture_sources=_fixture_module.validate_sources
fixture_log=_fixture_module.validate_log;fixture_receipt=_fixture_module.receipt_prerequisite

STAGES=('compile','resolve','replay','audit')
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
TARGET='LightEFTJointFlagSamplingStage.JointAssignmentLaw'
QUALIFICATION='NEWLY_OBSERVED_CI_INPUTS; neither historical preservation nor authenticated dependency provenance'

def ci_identity(env,head):
    require(env.get('GITHUB_ACTIONS')=='true','Not a GitHub Actions environment')
    require(env.get('GITHUB_REPOSITORY')=='gbodwin/paper-formalizations','Wrong repository')
    require(re.fullmatch('[0-9a-f]{40}',head or '') is not None and env.get('GITHUB_SHA')==head,'Exact event SHA differs from checked-out HEAD')
    require(env.get('GITHUB_RUN_ID','').isdecimal() and int(env['GITHUB_RUN_ID'])>0,'Valid CI run ID required')
    require(env.get('GITHUB_RUN_ATTEMPT','').isdecimal() and int(env['GITHUB_RUN_ATTEMPT'])>0,'Valid CI run attempt required')
    require(env.get('GITHUB_EVENT_NAME') in ['push','pull_request','workflow_dispatch'],'Unreviewed trigger')
    require(env.get('LEAN_NUM_THREADS')=='1','Reviewed job-wide worker setting required')
    require(env.get('GITHUB_REF')!='refs/heads/light-eft-spanners-checkpoints','Ignored checkpoint branch is not the publication route')
    role=env.get('LIGHTEFT_VALIDATION_ROLE')
    paths={'full':'.github/workflows/lean.yml','focused':'.github/workflows/light-eft-fair-bit-focused.yml'}
    require(role in paths and env.get('GITHUB_JOB')=='check','Unreviewed validation role/job')
    require(env.get('LIGHTEFT_EXPECTED_SOURCE')==head,'Scheduled exact source differs')
    repo=env['GITHUB_REPOSITORY'];ref=env.get('GITHUB_REF','')
    require(env.get('GITHUB_WORKFLOW')=='Lean' and env.get('GITHUB_WORKFLOW_SHA')==head and
        env.get('GITHUB_WORKFLOW_REF')==repo+'/.github/workflows/lean.yml@'+ref,'Exact caller workflow differs')
    require(env.get('LIGHTEFT_JOB_WORKFLOW_REPOSITORY')==repo and env.get('LIGHTEFT_JOB_WORKFLOW_PATH')==paths[role] and
        env.get('LIGHTEFT_JOB_WORKFLOW_SHA')==head,'Actual job workflow repository/path/SHA differs')
    require(env.get('LIGHTEFT_JOB_WORKFLOW_REF') in [repo+'/'+paths[role]+'@'+ref,repo+'/'+paths[role]+'@'+head],
        'Actual job workflow ref differs')
    return {k:env.get(k) for k in ['GITHUB_SHA','GITHUB_REF','GITHUB_EVENT_NAME','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_WORKFLOW','GITHUB_WORKFLOW_SHA','GITHUB_WORKFLOW_REF','GITHUB_ACTOR','GITHUB_REPOSITORY','LEAN_NUM_THREADS','GITHUB_JOB','LIGHTEFT_VALIDATION_ROLE','LIGHTEFT_EXPECTED_SOURCE','LIGHTEFT_JOB_WORKFLOW_REF','LIGHTEFT_JOB_WORKFLOW_SHA','LIGHTEFT_JOB_WORKFLOW_PATH','LIGHTEFT_JOB_WORKFLOW_REPOSITORY']}

def require(condition,message):
    if not condition:raise ValueError(message)

def scope_contract(spec):
    fixture_contract(spec)
    rows=spec['dependencies']
    require(len(rows)==len({r['module'] for r in rows})==77,'Exactly 77 distinct dependencies required')
    require(collections.Counter(r['module'].split('.')[0] for r in rows)=={'LightEFTSpanners':70,'LightSpanners':7},'Dependency namespace scope differs')
    require(spec['target']==TARGET and spec['project_imports']==78 and spec['required_public_roots']==16 and spec['required_interfaces']==8,'Exact staged audit scope differs')
    require(spec['private_identity_helper_required'] is True,'Private helper cannot be omitted')
    require(spec['expected_owner_declarations']==43,'Exact 43-owner contract differs')
    require(spec['resource_gates_GiB']==[3,3,4,4],'Admission gates differ')
    require(len(spec['pins'])==9 and spec['toolchain']=='leanprover/lean4:v4.34.0','Toolchain/dependency pins differ')

def plans(root,tool,work,spec,roots,source_commit):
    fixture_sources(root,spec)
    root,tool,work=map(str,[root,tool,work]);source={k:root+'/'+v['path'] for k,v in spec['sources'].items()}
    env=dict(LANG='C.UTF-8',LC_ALL='C.UTF-8',LEAN_NUM_THREADS='1',LEAN_SYSROOT=tool,LEAN_PATH=':'.join(map(str,roots)),
        LEAN_SRC_PATH=':'.join([root+'/'+spec['staged_root'],root+'/Light Edge Fault Tolerant Graph Spanners',root+'/An Alternate Proof of Near-Optimal Light Spanners',tool+'/src/lean']),
        MIMALLOC_ARENA_RESERVE='128MiB',MIMALLOC_VERBOSE='1',LIGHTEFT_SOURCE_COMMIT=source_commit,
        LIGHTEFT_HARNESS_COMMIT=source_commit,LIGHTEFT_FROZEN_SOURCE_COMMIT=spec['frozen_project_source_commit'])
    target=work+'/objects/'+TARGET.replace('.','/')+'.olean'
    argvs=[[tool+'/bin/lean',*FLAGS,'--root='+root+'/'+spec['staged_root'],'-o',target,source['source']],
           [tool+'/bin/lean',*FLAGS,source['resolver']],[tool+'/bin/leanchecker','-v',TARGET],
           [tool+'/bin/lean',*FLAGS,source['audit']]]
    roles=[['source'],['resolver','serialization_fixture','original_resolver','source'],['source'],['audit','source']];result=[]
    for stage,argv,role in zip(STAGES,argvs,roles,strict=True):
        e=env.copy()
        if stage=='resolve':e.update(LIGHTEFT_CHECKER_TARGET=TARGET,LIGHTEFT_CHECKER_RESOLUTION_FILE=work+'/resolution.json')
        if stage=='replay':e.pop('MIMALLOC_VERBOSE');e.update(LEAN_NUM_THREADS='1',LEAN_STACK_SIZE_KB='65536')
        result.append(dict(stage=stage,module=TARGET,argv=argv,env=e,sources=[source[k] for k in role],cwd=work+'/audit' if stage=='audit' else work))
    return result

def private_helper(inventory,target=TARGET):
    suffix='.LightEFTSpanners.JointFlagSampling.retainInstanceArguments'
    found=[r for r in inventory if r['name'].endswith(suffix)]
    require(len(found)==1,'Missing/duplicate private identity actual-owner root')
    r=found[0]
    require(r['name'].startswith('_private.') and r['owner']==target and r['kind']=='theorem','Wrong helper privacy/owner/kind')
    require(r['unsafe']=='false' and r['partial']=='false','Unsafe/partial helper')
    return r['name']

