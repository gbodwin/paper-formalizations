"""Three finite singleton replays in the current CI input context; no retry."""
from pathlib import Path
import json
from contracts import bind,require
from ci_handoff_contract import CONTRACT
from package_selection import selected_path
from output_guards import live_empty_generated,live_absent_resolution

COMPLETION_FLAGS=('direct_reaped','all_descendants_gone','kernel_no_children_verified',
    'waitid_wait4_status_match','kernel_limits_verified','between_child_preservation_passed','preexec_binding_verified')

def singleton_selection(roots,module,expected):
    matches=[]
    for root in map(Path,roots):
        for p in root.rglob('*.olean'):
            name='.'.join(p.relative_to(root).with_suffix('').parts)
            if name==module or name.startswith(module+'.'):matches.append((name,str(p)))
    require(matches==[(module,str(expected))],'Admission target prefix is missing/shadowed/nonunique')
    require(selected_path(roots,module)==Path(expected),'Admission target masked by first package marker')
    bind(expected)
    return dict(target=module,object=str(expected),prefix_matches=matches)

def replay_plans(root,repo,tool,spec,ordinary_plans,roots):
    result=[];template=ordinary_plans[2]
    require(template['stage']=='replay','Missing reviewed replay command template')
    for i,row in enumerate(CONTRACT['static_objects']):
        module=row['module'];work=Path(root)/'admission'/('%02d'%i)/'work'
        replay_roots=[work/'objects',*roots[1:]]
        env=dict(template['env'],LEAN_PATH=':'.join(map(str,replay_roots)))
        source=str(Path(repo)/row['source']['path'])
        p=dict(stage='replay',module=module,argv=[str(Path(tool)/'bin/leanchecker'),'-v',module],
            env=env,sources=[source],source_bindings=[bind(source)],cwd=str(work))
        result.append(dict(plan=p,work=work,roots=replay_roots,evidence=Path(root)/'runtime/admission'/('%02d'%i)))
    require([r['plan']['module'] for r in result]==CONTRACT['replay_order'],'Context replay schedule differs')
    return result

def context_type(ci_context,module,expected):
    class AdmissionContext(ci_context):
        def verify(self,compiled):
            require(not compiled and not self.target.exists(),'Admission cannot compile a corollary object')
            super().verify(False)
            live_empty_generated(self.objects,self.target)
            live_absent_resolution(self.work)
            self.admission_selection=singleton_selection(self.roots,module,expected)

        def before_child(self,plan,record,save_receipt):
            super().before_child(plan,record,save_receipt)
            require(plan['stage']=='replay' and plan['module']==module and plan['argv'][-2:]==['-v',module],'Wrong admission replay')
            record.update(context_admission_module=module,context_admission_selection=self.admission_selection,
                context_qualification=CONTRACT['context_qualification'])
            spec=record['output_guard_spec']
            spec['admission_only']=dict(module=module,object=str(expected))
            spec['protected'][str(expected)]=dict(self.inputs[str(expected)])
            save_receipt()

        def after_child(self,plan,record,save_receipt):
            self.verify(False)
            if record.get('exit')==0 and 'failure' not in record:
                require((self.stage_evidence/'raw.log').read_text().strip()=='replaying '+module,'Not exact admission singleton replay diagnostic')
                require(not self.new and not self.resolved,'Admission emitted unexpected objects/resolution')
                self.seen.append(plan)
            record['between_child_preservation_passed']=True;save_receipt()

    return AdmissionContext

def execute_sequence(admissions,run_admission,commands,run_corollary,finish,progress=None):
    require([a['plan']['module'] for a in admissions]==CONTRACT['replay_order'],'Missing/reordered/extra admission replay')
    require([p['stage'] for p in commands]==CONTRACT['corollary_stages'],'Missing/reordered/extra corollary stage')
    accepted=[]
    for a in admissions:
        r=run_admission(a)
        require(r.get('state')=='finished' and r.get('exit')==0 and not r.get('failure') and not r.get('cleanup_errors'),'Admission replay failed')
        require(all(r.get(k) is True for k in COMPLETION_FLAGS),'Admission replay lifecycle/preservation incomplete')
        accepted.append(dict(module=a['plan']['module'],stage='replay',attempt_id=r['attempt_id']))
        if progress is not None:progress(accepted)
    stages=[]
    for p in commands:
        r=run_corollary(p)
        stages.append(dict(stage=p['stage'],attempt_id=r['attempt_id']))
    return dict(admission_replays=accepted,stages=stages,result=finish())

def verify_schedule(records,lease,identity):
    require(len(records)==7,'Exactly three admission and four corollary receipts required')
    seen=set();previous=0
    for r in records:
        require(r.get('state')=='finished' and r.get('exit')==0 and not r.get('failure') and not r.get('cleanup_errors'),'Failed finite CI schedule receipt')
        require(r.get('source_commit')==r.get('wrapper_commit')==identity['GITHUB_SHA'] and r.get('CI_identity')==identity,'Finite receipt CI/source identity differs')
        require(r['attempt_id'] not in seen,'Repeated finite CI attempt UUID');seen.add(r['attempt_id'])
        require(lease['acquired_ns']<=r['started_ns']<r['ended_ns']<=lease['release_ns'] and previous<r['started_ns'],'Admission/corollary overlap or outside one lease')
        previous=r['ended_ns']
    require([r.get('context_admission_module') for r in records[:3]]==CONTRACT['replay_order'],'Admission receipt module order differs')
    require([r['stage'] for r in records]==['replay']*3+CONTRACT['corollary_stages'],'Finite receipt stage order differs')
    require(all(r.get('context_qualification')==CONTRACT['context_qualification'] for r in records[:3]),'Current-context qualification missing')
    return True
