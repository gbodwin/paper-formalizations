"""Finite corollary scope and command translation; unchanged ordinary CI identity."""
import collections, re

STAGES=('compile','resolve','replay','audit')
FLAGS=['-j1','-s65536','-M5120','-DautoImplicit=false','-DwarningAsError=true']
TARGET='LightEFTJointFlagOutputStage.PolynomialActualFailureProbability'
QUALIFICATION='NEWLY_OBSERVED_CI_INPUTS; neither historical preservation nor authenticated dependency provenance'
COUNTS={'LightEFTActualSuppliedForestProbabilityStage':1,'LightEFTJointFlagSamplingStage':1,'LightEFTSpanners':304,'LightEFTSuppliedForestProbabilityStage':1,'LightEFTSuppliedForestStage':1,'LightSpanners':56}
NAME_HASH='f21106d5d3ee2aa8a853edbfa31079e10a979aef10792cec0fd66f4459784311'
SOURCE_PATH='checkpoints/light-eft-joint-flag-output-draft-20261019/staged/LightEFTJointFlagOutputStage/PolynomialActualFailureProbability.lean'
SOURCE_SHA='caa89c0d197131ffdc8405e63bfd56dfbc08468e8bec760f33736d1b4f08adf1'

def require(condition,message):
    if not condition:raise ValueError(message)

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

def scope_contract(spec):
    import hashlib
    from probability_plan import REQUIRED_ROOTS,REQUIRED_INTERFACES
    require(spec['accepted_source_base']=='f8a2476ef4a910f0b0225ade418ab174f98d8e21' and spec['source_transfer_commit']=='00a555ff9406bdc0a94da8338edb71c7818224d5','Exact preserved source authority differs')
    require(spec['sources']['source']=={'path':SOURCE_PATH,'bytes':3567,'sha256':SOURCE_SHA},'Preserved theorem source changed')
    rows=spec['dependencies'];names=[r['module'] for r in rows]
    require(len(rows)==len(set(names))==364,'Exactly364 distinct dependency names required')
    require(spec['dependency_count']==364 and spec['namespace_counts']==COUNTS and spec['ordered_names_sha256']==NAME_HASH,'Dependency metadata contradicts finite scope')
    require(collections.Counter(n.split('.')[0] for n in names)==COUNTS,'Dependency namespace scope differs')
    require(hashlib.sha256(('\n'.join(sorted(names))+'\n').encode()).hexdigest()==NAME_HASH,'Exact dependency-name set differs')
    require(spec['target']==TARGET and TARGET not in names and spec['project_imports']==365,'Exact singleton scope differs')
    require(spec['required_public_roots']==1 and spec['required_interfaces']==6,'Exact root/interface scope differs')
    require(tuple(spec['audit_roots'])==REQUIRED_ROOTS and tuple(spec['reachable_interfaces'])==REQUIRED_INTERFACES,'Exact required root/interface names differ')
    require(spec['expected_owner_declarations'] is None,'Generated owner census must be observed, not guessed')
    require(spec['resource_gates_GiB']==[3,3,4,4],'Admission gates differ')
    require(len(spec['pins'])==9 and spec['toolchain']=='leanprover/lean4:v4.34.0','Toolchain/dependency pins differ')
    from ci_handoff_contract import CONTRACT
    require(spec.get('object_admission')==CONTRACT,'Finite same-run handoff/admission contract differs')
    require(spec.get('stage_order')==['context-replay:'+m for m in CONTRACT['replay_order']]+list(STAGES),'Admission/corollary schedule differs')

def plans(root,tool,work,spec,roots,source_commit):
    root,tool,work=map(str,[root,tool,work]);source={k:root+'/'+v['path'] for k,v in spec['sources'].items()}
    source_roots=list(dict.fromkeys([spec['staged_root'],*spec['staged_dependency_source_roots'],'Light Edge Fault Tolerant Graph Spanners','An Alternate Proof of Near-Optimal Light Spanners']))
    env=dict(LANG='C.UTF-8',LC_ALL='C.UTF-8',LEAN_NUM_THREADS='1',LEAN_SYSROOT=tool,LEAN_PATH=':'.join(map(str,roots)),
        LEAN_SRC_PATH=':'.join([root+'/'+p for p in source_roots]+[tool+'/src/lean']),
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
