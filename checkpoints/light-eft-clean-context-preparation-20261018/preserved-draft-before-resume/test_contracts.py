"""Synthetic/static contracts only: no child, retrieval, extraction or cache advice."""
from pathlib import Path
import ast,copy,hashlib,json,os,unittest
from unittest.mock import patch
import clean_contract as c
import audit_data
import describe

A=Path(__file__).resolve().parent


def start_facts(ctx):
    return {'root':str(ctx.root),'root_preexisted':False,'input_context':ctx.input_id,'output_context':ctx.output_id,
            'project_object_files':[],'resolution_files':[],'symlinks':[],'historical_inputs':[],
            'search_paths':ctx.searches(),'pins':c.PLAN['pins']}


def accounting():
    return {'qualification':'PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN','headroom':8*1024**3,
            'system_available':9*1024**3,'identities':['synthetic bounded view'],
            'nodes':[{'path':'/synthetic','limit':str(16*1024**3),'oom':{'oom':0},'pids_events':{'max':0}}]}


def frame(model,index=None):
    index=model.position if index is None else index;ctx=model.ctx;step=model.steps[index]
    module=step['module'];stage=step['stage'];n=index+1;pid=60000+n;attempt='%032x'%n
    identity={k:v for k,v in {'pid':pid,'stat_pid':pid,'status_pid':pid,'tgid':pid,'ppid':42,'sid':pid,'pgid':pid,'start_ticks':100000+n}.items()}
    r={'fixture_only':True,'stage':stage,'module':module,'state':'finished','exit':0,'attempt_id':attempt,
       'source_commit':c.SOURCE,'argv':c.command(ctx,step),'environment':ctx.environment(module,stage),
       'clean_input_context':ctx.input_id,'clean_output_context':ctx.output_id,
       'submitted_source_sha256':c.PLAN['resolver_source_sha256'] if stage=='resolve' else step['source_sha256'],
       'supervisor_profile':c.profile(stage),'deadline_seconds':90,'child_pid':pid,'supervisor_pid':42,
       'child_identity':identity,'terminal_confirmation':{'terminal':True,'pid':pid,'pid_requested':pid,'status':0,'code':os.CLD_EXITED},
       'direct_reaped':True,'kernel_no_children_verified':True,'all_descendants_gone':True,'direct_wait_owner':'runner wait4','waitid_wait4_status_match':True,
       'handshake':{'pid':pid,'ppid':42,'sid':pid,'pgid':pid,'limits':c.limits(stage),'lock_inheritable':True,'lock_device':33,'lock_inode':3849,'lock_fd':3},
       'lock':{'device':33,'inode':3849,'fd':3,'outer_acquired_ns':1},'started_ns':n*10,'ended_ns':n*10+2,
       'admission':accounting(),'preexec_admission':accounting(),'disk_admission_bytes':3*1024**3,'disk_preexec_bytes':3*1024**3,
       'decision_log_bytes':1000,'canonical_input_inventory':{'sha256':'1'*64}}
    f={'receipt':r,'preservation':{'input_context':ctx.input_id,'all_paths_attempted':True,'paths_checked':500,'input_count':500,'before_sha256':'1'*64,'after_sha256':'1'*64},
       'runtime_samples':[{'visible_headroom':2*1024**3,'host_available':4*1024**3,'shared_mm_rss':1024**3,'anon_growth_by_cgroup':{'/synthetic':100}}]}
    if stage=='compile':
        f['output']={'path':ctx.object(module),'module':module,'source_sha256':step['source_sha256'],
            'sha256':hashlib.sha256(('SYNTHETIC ONLY '+module).encode()).hexdigest(),'context':ctx.output_id,
            'producer_attempt':attempt,'fresh':True,'regular':True,'symlink':False}
    elif stage=='resolve':
        obj=model.provisional_objects[module];expected=[{'module':module,'object':obj['path']}]
        f['resolution']={'target':module,'count':1,'resolved':expected,'path':ctx.resolution(module),
                         'context':ctx.output_id,'fresh':True,'object_sha256':obj['sha256']};f['search_hits']=copy.deepcopy(expected)
    elif stage=='replay':
        f['resolution']=copy.deepcopy(model.provisional_resolutions[module]);f['object_sha256']=model.provisional_objects[module]['sha256'];f['raw_output']='replaying '+module+'\n'
    return f


def complete_model():
    model=c.DryRunLedger(c.CleanContext('ab'*16))
    while model.position<len(model.steps):model.consume(frame(model))
    return model


def audit_fixture(model):
    ctx=model.ctx;owner=c.GRAPH[0]['module'];name='_private.SYNTHETIC.0.root'
    data={'actual-owner-inventory.tsv':('owner\tname\tkind\tunsafe\tpartial\n'+owner+'\t'+name+'\topaque\tfalse\tfalse\n').encode(),
          'recursive-dependencies.tsv':('name\towner\tkind\ttypeDependencies\tbodyDependencies\tunsafe\tpartial\n'+
              name+'\t'+owner+'\topaque\tpropext\tNat.rec\tfalse\tfalse\n'+
              'propext\tInit.Core\taxiom\t\t\tfalse\tfalse\nNat.rec\tInit.Prelude\trecursor\t\tNat\tfalse\tfalse\n'+
              'Nat\tInit.Prelude\tinductive\t\tNat.zero\tfalse\tfalse\nNat.zero\tInit.Prelude\tconstructor\t\tNat\tfalse\tfalse\n').encode(),
          'import-closure-loaded.txt':('\n'.join(r['module'] for r in c.GRAPH)+'\nInit.Core\nInit.Prelude\n').encode(),
          'strict-violations.txt':b'\n',
          'raw.log':b'DIAGNOSTIC ONLY: 1 actual-owner project declarations, 1 covered declarations; 5 recursively visited constants, 1 opaque bodies; axioms [propext]\n'}
    files={};chunks={}
    for n,b in data.items():
        files[n]={'data':b,'path':str(ctx.work/'ci-evidence'/n) if n!='raw.log' else str(ctx.evidence/'audit/raw.log'),
                  'producer_attempt':model.receipts[-1]['attempt_id'],'context':ctx.output_id,'fresh':True,'regular':True,'symlink':False}
        chunks[n]=[{'data':b,'sha256':hashlib.sha256(b).hexdigest()}]
    final={'all_paths_attempted':True,'matching':True,'paths_checked':500,'input_count':500,
           'before_sha256':'1'*64,'after_sha256':'1'*64,'input_context':ctx.input_id}
    return final,files,chunks


def artifact_fixture():
    provenance={'official_archives':3808,'official_origin_receipts_complete':True,'toolchain_distribution_authenticated':True,
                'extractor_member_authenticated':True,'source_to_key_pins':c.PLAN['pins'],'label':'SYNTHETIC REVIEW METADATA ONLY'}
    files=[{'relative_path':'mathlib/lib/lean/Mathlib/Test.olean','sha256':'2'*64,'regular':True,'symlink':False}]
    spec={'status':'REVIEWED_ARTIFACT','pins':c.PLAN['pins'],'toolchain':c.PLAN['toolchain'],'lake_manifest_sha256':c.PLAN['lake_manifest_sha256'],
          'artifact_sha256':'3'*64,'bytes':100,'files':files,'provenance':provenance}
    authority={'artifact_sha256':'3'*64,'bytes':100,'files_sha256':c.digest(files),'provenance_sha256':c.digest(provenance),
               'file_count':1,'independent_review_commit':'4'*40,'scope':'SYNTHETIC AUTHORITY; NOT PRODUCTION'}
    return spec,authority


class DisabledAndContext(unittest.TestCase):
    def test_all_execution_approval_spellings_rejected(self):
        for args in [['--execute'],['--execute-reviewed-clean'],['--execute-reviewed-clean','a13f2738bd4e9f3a2e6de291c2f40e636fec3406'],
                     ['--approval','FORGED'],['--force'],['--artifact','missing.json'],['--execute','--approved=true']]:
            with self.assertRaises(c.ProductionDisabled):describe.main(args)
    def test_describe_only(self):self.assertEqual(describe.main(['--describe']),0)
    def test_empty_initial_ledgers(self):
        model=c.DryRunLedger(c.CleanContext('01'*16));self.assertFalse(model.accepted_objects);self.assertFalse(model.provisional_objects);self.assertFalse(model.provisional_resolutions)
    def test_exact_finite_schedule(self):
        s=c.schedule();counts={k:sum(r['stage']==k for r in s) for k in ['compile','resolve','replay','audit']}
        self.assertEqual(counts,{'compile':486,'resolve':485,'replay':485,'audit':1});self.assertEqual(len(s),1457)
    def test_aggregate_prefix_replay_forbidden(self):
        ctx=c.CleanContext('02'*16)
        for stage in ['resolve','replay']:
            with self.assertRaises(c.Rejected):c.command(ctx,{'module':'LightEFTSpanners','stage':stage,'source_sha256':c.GRAPH[-1]['sha256']})
    def test_fresh_roots_and_no_old_search(self):
        ctx=c.CleanContext('03'*16);ctx.validate_start(start_facts(ctx))
        self.assertTrue(all(str(ctx.root) in p for p in ctx.searches()));self.assertFalse(Path(str(ctx.root)).exists())
    def test_old_project_root_rejected(self):
        ctx=c.CleanContext('04'*16);f=start_facts(ctx);f['root']='/workspace/light-eft-verification/.lake/old'
        with self.assertRaises(c.Rejected):ctx.validate_start(f)
    def test_old_dependency_root_rejected(self):
        ctx=c.CleanContext('05'*16);f=start_facts(ctx);f['search_paths'].append('/workspace/paper-formalizations/.lake/packages/mathlib/.lake/build/lib/lean')
        with self.assertRaises(c.Rejected):ctx.validate_start(f)
    def test_seeded_project_or_resolution_rejected(self):
        ctx=c.CleanContext('06'*16)
        for key in ['project_object_files','resolution_files']:
            f=start_facts(ctx);f[key]=['historical']
            with self.assertRaises(c.Rejected):ctx.validate_start(f)
    def test_wrong_pins_rejected(self):
        ctx=c.CleanContext('07'*16);f=start_facts(ctx);f['pins']={}
        with self.assertRaises(c.Rejected):ctx.validate_start(f)
    def test_input_output_contexts_not_interchangeable(self):
        ctx=c.CleanContext('08'*16);f=start_facts(ctx);f['input_context']=ctx.output_id
        with self.assertRaises(c.Rejected):ctx.validate_start(f)


class ArtifactContracts(unittest.TestCase):
    def test_real_authority_unavailable(self):
        spec,_=artifact_fixture()
        with self.assertRaises(c.Rejected):c.validate_artifact_consistency(spec,c.PLAN['reviewed_artifact_authority'])
    def test_metadata_positive_control_grants_no_execution(self):
        s,a=artifact_fixture();r=c.validate_artifact_consistency(s,a);self.assertFalse(r['production_enabled']);self.assertFalse(r['authentication_performed_here'])
    def test_wrong_hash(self):
        s,a=artifact_fixture();s['artifact_sha256']='f'*64
        with self.assertRaises(c.Rejected):c.validate_artifact_consistency(s,a)
    def test_wrong_pin(self):
        s,a=artifact_fixture();s['pins']={}
        with self.assertRaises(c.Rejected):c.validate_artifact_consistency(s,a)
    def test_forged_provenance(self):
        s,a=artifact_fixture();s['provenance']['official_origin_receipts_complete']=False
        with self.assertRaises(c.Rejected):c.validate_artifact_consistency(s,a)
    def test_historical_artifact_path(self):
        s,a=artifact_fixture();s['files'][0]['relative_path']='/workspace/paper-formalizations/.lake/old.olean';a['files_sha256']=c.digest(s['files'])
        with self.assertRaises(c.Rejected):c.validate_artifact_consistency(s,a)
    def test_dependency_artifact_cannot_seed_project(self):
        s,a=artifact_fixture();s['files'][0]['relative_path']='mathlib/lib/lean/LightEFTSpanners/Hidden.olean';a['files_sha256']=c.digest(s['files'])
        with self.assertRaises(c.Rejected):c.validate_artifact_consistency(s,a)


class StageContracts(unittest.TestCase):
    def model(self):return c.DryRunLedger(c.CleanContext('09'*16))
    def test_partial_failed_object_never_accepted_and_no_retry(self):
        m=self.model();f=frame(m);f['receipt']['state']='failed';f['receipt']['exit']=1
        with self.assertRaises(c.Rejected):m.consume(f)
        self.assertFalse(m.accepted_objects);self.assertFalse(m.provisional_objects);self.assertEqual(len(m.quarantined_outputs),1)
        with self.assertRaises(c.Rejected):m.consume(frame(m))
    def test_duplicate_stage(self):
        m=self.model();f=frame(m);m.consume(f)
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_wrong_source_hash(self):
        m=self.model();f=frame(m);f['receipt']['submitted_source_sha256']='f'*64
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_unowned_zero_exit(self):
        m=self.model();f=frame(m);f['receipt']['terminal_confirmation']['pid']+=1
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_unsafe_old_object_path(self):
        m=self.model();f=frame(m);f['output']['path']='/workspace/light-eft-verification/.lake/old.olean'
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_incomplete_stage_preservation(self):
        m=self.model();f=frame(m);f['preservation']['all_paths_attempted']=False
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_wrong_resolution(self):
        m=self.model();m.consume(frame(m));f=frame(m);f['resolution']['resolved'][0]['object']+='wrong'
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_stale_resolution(self):
        m=self.model();m.consume(frame(m));f=frame(m);f['resolution']['fresh']=False
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_shadowed_resolution(self):
        m=self.model();m.consume(frame(m));f=frame(m);f['search_hits'].append({'module':m.steps[m.position]['module']+'.extra','object':'shadow'})
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_object_hash_mismatch_in_resolution(self):
        m=self.model();m.consume(frame(m));f=frame(m);f['resolution']['object_sha256']='f'*64
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_resource_profile_mix(self):
        m=self.model();f=frame(m);f['receipt']['handshake']['limits']=c.limits('audit')
        with self.assertRaises(c.Rejected):m.consume(f)
    def test_bounded_accounting_not_full_ancestor_gate(self):
        now=accounting();c.validate_accounting(now,now,3*1024**3)
        self.assertIn('UNKNOWN',now['qualification'])


class FinalContracts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.template=complete_model()
    def model(self):return copy.deepcopy(self.template)
    def test_all_fresh_stages_then_audit_and_final_promote_model_only(self):
        m=self.model();self.assertFalse(m.accepted_objects);p,f,k=audit_fixture(m);r=m.finalize(p,f,k)
        self.assertEqual(len(m.accepted_objects),486);self.assertEqual(len(m.accepted_resolutions),485)
        self.assertFalse(r['actual_clean_validation_performed']);self.assertFalse(r['production_enabled'])
    def test_final_preservation_failure(self):
        m=self.model();p,f,k=audit_fixture(m);p['matching']=False
        with self.assertRaises(c.Rejected):m.finalize(p,f,k)
        self.assertFalse(m.accepted_objects)
    def test_stale_audit_output(self):
        m=self.model();p,f,k=audit_fixture(m);f['raw.log']['producer_attempt']='old'
        with self.assertRaises(c.Rejected):m.finalize(p,f,k)
    def test_missing_module_in_full_audit(self):
        m=self.model();p,f,k=audit_fixture(m);name='import-closure-loaded.txt';data=f[name]['data'].split(b'\n',1)[1];f[name]['data']=data;k[name]=[{'data':data,'sha256':hashlib.sha256(data).hexdigest()}]
        with self.assertRaises(c.Rejected):m.finalize(p,f,k)
    def test_private_generated_omission(self):
        m=self.model();p,f,k=audit_fixture(m);name='recursive-dependencies.tsv';extra=('generated\t'+c.GRAPH[0]['module']+'\tdefinition\t\t\tfalse\tfalse\n').encode();f[name]['data']+=extra;k[name]=[{'data':f[name]['data'],'sha256':hashlib.sha256(f[name]['data']).hexdigest()}]
        with self.assertRaises(c.Rejected):m.finalize(p,f,k)
    def test_bad_chunk_blocks_acceptance(self):
        m=self.model();p,f,k=audit_fixture(m);k['raw.log'][0]['data']+=b'wrong';k['raw.log'][0]['sha256']=hashlib.sha256(k['raw.log'][0]['data']).hexdigest()
        with self.assertRaises(c.Rejected):m.finalize(p,f,k)
        self.assertFalse(m.accepted_objects)
    def test_historical_audit_counts_not_acceptance(self):
        m=self.model();p,f,k=audit_fixture(m);n='raw.log';data=f[n]['data'].replace(b'1 actual-owner',b'8950 actual-owner');f[n]['data']=data;k[n]=[{'data':data,'sha256':hashlib.sha256(data).hexdigest()}]
        with self.assertRaises(c.Rejected):m.finalize(p,f,k)


class StaticSafety(unittest.TestCase):
    def test_core_has_no_child_network_extractor_or_advice_API(self):
        forbidden={'subprocess','urllib','socket','tarfile','ctypes','requests'}
        for name in ['clean_contract.py','audit_data.py','describe.py']:
            tree=ast.parse((A/name).read_text())
            for node in ast.walk(tree):
                if isinstance(node,ast.Import):self.assertFalse(forbidden & {a.name.split('.')[0] for a in node.names})
                if isinstance(node,ast.ImportFrom):self.assertNotIn((node.module or '').split('.')[0],forbidden)
    def test_referenced_supervisors_byte_unchanged(self):
        data=json.loads((A/'supervisor-bindings.json').read_text());R=A.parents[1]
        for key in ['ordinary','audit']:
            for r in data[key]['files']:self.assertEqual(hashlib.sha256((R/r['repository_path']).read_bytes()).hexdigest(),r['sha256'])
    def test_unavailable_descriptor_unchanged(self):
        R=A.parents[1];data=json.loads((R/'scripts/LightEFTDependencyArtifact.json').read_text());self.assertEqual(data['status'],'UNAVAILABLE_REVIEW_REQUIRED')
        for r in json.loads((A/'unchanged-production-bindings.json').read_text()):self.assertEqual(hashlib.sha256((R/r['repository_path']).read_bytes()).hexdigest(),r['sha256'])


if __name__=='__main__':unittest.main(verbosity=2)
