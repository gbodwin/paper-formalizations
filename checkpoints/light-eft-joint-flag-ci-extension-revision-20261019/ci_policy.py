"""Exact ordinary-event binding and staged contracts; no dispatch-only admission gate."""
import collections, re

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
    return {k:env.get(k) for k in ['GITHUB_SHA','GITHUB_REF','GITHUB_EVENT_NAME','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_WORKFLOW','GITHUB_WORKFLOW_SHA','GITHUB_WORKFLOW_REF','GITHUB_ACTOR','GITHUB_REPOSITORY','LEAN_NUM_THREADS']}

def require(condition,message):
    if not condition:raise ValueError(message)

def scope_contract(spec):
    rows=spec['dependencies']
    require(len(rows)==len({r['module'] for r in rows})==77,'Exactly 77 distinct dependencies required')
    require(collections.Counter(r['module'].split('.')[0] for r in rows)=={'LightEFTSpanners':70,'LightSpanners':7},'Dependency namespace scope differs')
    require(spec['target']==TARGET and spec['project_imports']==78 and spec['required_public_roots']==16 and spec['required_interfaces']==8,'Exact staged audit scope differs')
    require(spec['private_identity_helper_required'] is True,'Private helper cannot be omitted')
    require(spec['resource_gates_GiB']==[3,3,4,4],'Admission gates differ')
    require(len(spec['pins'])==9 and spec['toolchain']=='leanprover/lean4:v4.34.0','Toolchain/dependency pins differ')

def plans(root,tool,work,spec,roots,source_commit):
    root,tool,work=map(str,[root,tool,work]);source={k:root+'/'+v['path'] for k,v in spec['sources'].items()}
    env=dict(LANG='C.UTF-8',LC_ALL='C.UTF-8',LEAN_NUM_THREADS='1',LEAN_SYSROOT=tool,LEAN_PATH=':'.join(map(str,roots)),
        LEAN_SRC_PATH=':'.join([root+'/'+spec['staged_root'],root+'/Light Edge Fault Tolerant Graph Spanners',root+'/An Alternate Proof of Near-Optimal Light Spanners',tool+'/src/lean']),
        MIMALLOC_ARENA_RESERVE='128MiB',MIMALLOC_VERBOSE='1',LIGHTEFT_SOURCE_COMMIT=source_commit,
        LIGHTEFT_HARNESS_COMMIT=source_commit,LIGHTEFT_FROZEN_SOURCE_COMMIT=spec['frozen_project_source_commit'])
    target=work+'/objects/'+TARGET.replace('.','/')+'.olean'
    argvs=[[tool+'/bin/lean',*FLAGS,'--root='+root+'/'+spec['staged_root'],'-o',target,source['source']],
           [tool+'/bin/lean',*FLAGS,source['resolver']],[tool+'/bin/leanchecker','-v',TARGET],
           [tool+'/bin/lean',*FLAGS,source['audit']]]
    roles=[['source'],['resolver','source'],['source'],['audit','source']];result=[]
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

