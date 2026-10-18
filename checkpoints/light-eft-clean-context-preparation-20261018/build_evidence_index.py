"""Offline source/log/hash index of previously reviewed incremental executions.

Does not run Lean, checkers, network tools, extraction or cache advice. Historical
retained paths below are evidence references only, never clean executor inputs.
"""
from pathlib import Path
import hashlib,json,subprocess

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
SOURCE='78cb40c7837db049d645d73696f2e0b724ce8a3b'
UMBRELLA='4bc6d398cee4e65c1550a585fff6778381262bdf'
AUDIT='c7f33d7ece117ddc7d20e4f7a5dad2f870e9d41f'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def binding(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}
def commit(p):
    return subprocess.check_output(['git','log','-1','--format=%H','--',str(p.relative_to(ROOT))],cwd=ROOT,text=True).strip()

def build():
    graph=load(A/'frozen-graph.json');names={r['module'] for r in graph};selected={};excluded=[]
    final_dir=ROOT/'checkpoints/light-eft-resume206-reviewed-reread-20261018'
    hashes=load(final_dir/'source-toolchain-object-hashes.json')
    objects={}
    for r in graph:
        suffix='/'+r['module'].replace('.','/')+'.olean'
        rows=[x for x in hashes['final_objects'] if x['path'].endswith(suffix)]
        assert len(rows)==1
        obj=rows[0];assert sha(Path(obj['path']).read_bytes())==obj['sha256']
        objects[r['module']]=obj
    publications={}
    for folder in sorted((ROOT/'checkpoints').glob('light-eft-*')):
        result=folder/'batch-result.json'
        if not result.exists():continue
        data=load(result)
        for s in data.get('stages',[]):
            if s.get('module') not in names or not s.get('receipt'):continue
            p=folder/s['receipt']
            if not p.exists():continue
            r=load(p)
            if not (s.get('state')=='finished' and s.get('exit')==0 and r.get('state')=='finished' and r.get('exit')==0):
                excluded.append(dict(module=s['module'],stage=s.get('stage'),receipt=binding(p),state=r.get('state'),exit=r.get('exit')));continue
            key=(s['module'],s['stage']);assert key not in selected,key
            selected[key]=(p,r)
            if folder.name not in publications:
                pub=folder/'PUBLICATION.json';pd=load(pub)
                publications[folder.name]={'publication':binding(pub),'publication_commit':commit(pub),'result_commit':pd.get('result_commit'),'report':str((folder/'REPORT.md').relative_to(ROOT))}
    finite='LightEFTSpanners.FiniteLaw'
    for stage,folder in [('compile','light-eft-finitelaw-admission3-chain-20261017'),('resolve','light-eft-finitelaw-exit-transition-20261017'),('replay','light-eft-finitelaw-finite-recovery-20261017')]:
        p=ROOT/'checkpoints'/folder/'evidence'/stage/'receipt.json';assert (finite,stage) not in selected
        selected[finite,stage]=(p,load(p))
        publications[folder]={'receipt_commit':commit(p),'report':str((ROOT/'checkpoints'/folder/'REPORT.md').relative_to(ROOT))}
    assert len(selected)==1456 # 485 triples and one aggregate compilation.
    receipt_ids=set();rows=[];aggregate=None
    for row in graph:
        module=row['module'];stages={};obj=objects[module]
        for stage in (['compile'] if module=='LightEFTSpanners' else ['compile','resolve','replay']):
            p,r=selected[module,stage]
            assert r['source_commit']==SOURCE and r['state']=='finished' and r['exit']==0
            assert r['attempt_id'] not in receipt_ids;receipt_ids.add(r['attempt_id'])
            assert r['direct_reaped'] and r['all_descendants_gone'] and r['kernel_no_children_verified']
            assert r['lock']['device']==33 and r['lock']['inode']==3849
            assert r['submitted_source_sha256']==('9f2a3d83e0b90d75a7e0ddc3693f09e27d50040bc8fc65a2b5b9df4eb1797caf' if stage=='resolve' else row['sha256'])
            if stage=='compile':
                outputs=r.get('output_delta',r.get('output_inventory_after',[]));produced=[o for o in outputs if o['path'].endswith('/'+module.replace('.','/')+'.olean')]
                assert len(produced)==1 and produced[0]['sha256']==obj['sha256']
                assert '-DwarningAsError=true' in r['argv'] and '-j1' in r['argv']
                resolved_path=produced[0]['path']
            elif stage=='resolve':
                if 'official_resolution' in r:
                    res=r['official_resolution'];assert res['target']==module and res['count']==1
                    assert len(res['resolved'])==1 and res['resolved'][0]['module']==module
                    resolved_path=res['resolved'][0]['object']
                else:
                    assert module==finite
                    assert (p.parent/'raw.log').read_text()=='PASS: official checker resolution is exactly [LightEFTSpanners.FiniteLaw]\n'
                    resolved_path=r['object_bindings_before'][0]['path']
            else:
                assert r['argv']==['/workspace/toolchains/lean-4.34.0-linux/bin/leanchecker','-v',module]
                assert (p.parent/'raw.log').read_text()=='replaying '+module+'\n'
                if 'official_resolution' in r:
                    res=r['official_resolution'];assert res['target']==module and res['count']==1 and res['resolved']==[{'module':module,'object':res['resolved'][0]['object']}]
                    resolved_path=res['resolved'][0]['object']
                elif module==finite:resolved_path=r['object_bindings_before'][0]['path']
                # Earlier replays can rely on the immediately preceding exact
                # resolution and preserved object bindings, not a new preflight.
            assert sha(Path(resolved_path).read_bytes())==obj['sha256'],(module,stage,resolved_path)
            raw=p.parent/'raw.log';raw_binding=binding(raw)
            if 'completed_logs' in r:
                assert raw_binding['sha256']==r['completed_logs']['raw.log']['sha256']
            stages[stage]={'receipt':binding(p),'raw_diagnostics':raw_binding,'attempt_id':r['attempt_id'],'source_commit':r['source_commit'],'submitted_source_sha256':r['submitted_source_sha256'],'object_path_at_stage':resolved_path,'object_sha256':obj['sha256'],'retained_path_same_as_stage':resolved_path==obj['path'],'exit':0,'publication_group':p.relative_to(ROOT).parts[1]}
        entry={'module':module,'source_path':row['path'],'source_sha256':row['sha256'],'retained_object_path':obj['path'],'object_sha256':obj['sha256'],'stages':stages}
        if module=='LightEFTSpanners':aggregate=entry
        else:rows.append(entry)
    assert len(rows)==485 and aggregate is not None
    shards=[];catalog=[];out=A/'chain-index-parts';out.mkdir(exist_ok=True)
    for start in range(0,len(rows),50):
        batch=rows[start:start+50];p=out/('part-%02d.json'%(start//50));p.write_text(json.dumps(batch,indent=2)+'\n');shards.append(binding(p))
        catalog.extend({'module':x['module'],'source_sha256':x['source_sha256'],'object_sha256':x['object_sha256'],'part':str(p.relative_to(ROOT))} for x in batch)
    auditdir=ROOT/'checkpoints/light-eft-full-audit-result-20261018';actual=load(auditdir/'actual-result.json')
    auditindex=load(auditdir/'evidence-source-index.json')
    for b in auditindex['repository_sources']:
        p=ROOT/b['repository_path'];assert binding(p)['sha256']==b['sha256']
    execution=ROOT/actual['execution_path'];execution_manifest=load(execution/'evidence-sha256.json')
    assert len(execution_manifest)==244
    for b in execution_manifest:
        p=execution/b.get('path',b.get('repository_path',''));assert p.is_file(),str(p)
        assert sha(p.read_bytes())==b['sha256'],str(p)
    reconstructions=[];chunk_count=0
    for p in sorted((execution/'audit-export').glob('*/manifest.json')):
        m=load(p);parts=[]
        for b in m['parts']:
            raw=(p.parent/b['path']).read_bytes()
            assert len(raw)==b['bytes'] and sha(raw)==b['sha256']
            parts.append(raw);chunk_count+=1
        raw=b''.join(parts)
        assert len(raw)==m['bytes'] and sha(raw)==m['sha256'] and raw==Path(m['source']).read_bytes()
        reconstructions.append({'manifest':binding(p),'bytes':len(raw),'sha256':sha(raw),'parts':len(parts)})
    assert len(reconstructions)==5 and chunk_count==216
    index={'as_of_utc_date':'2026-10-18','kind':'offline reconciliation of reviewed incremental evidence; no fresh execution','source_commit':SOURCE,'ordinary_chain_count':485,'stage_counts':{'ordinary_compile':485,'exact_resolution':485,'singleton_replay':485,'aggregate_compile':1},'review_authority':{'ordinary_final_binding_commit':UMBRELLA,'reported_review':'Parent reports all 485 qualified chains accepted; predecessor qualifications and failed attempts remain historical. This index is source/log/hash reconciliation, not a new acceptance or clean validation.'},'source_graph':binding(A/'frozen-graph.json'),'prior_final_hash_inventory':binding(final_dir/'source-toolchain-object-hashes.json'),'publication_groups':publications,'parts':shards,'ordinary_modules':catalog,'aggregate_compile_only':aggregate,'excluded_failed_or_unqualified_stage_records':excluded,'full_audit':{'binding_commit':AUDIT,'result':binding(auditdir/'actual-result.json'),'report':str((auditdir/'REPORT.md').relative_to(ROOT)),'execution_path':actual['execution_path'],'execution_manifest':binding(execution/'evidence-sha256.json'),'counts':actual['audit_counts'],'review_status':'Independent review verified the 244-entry manifest, 216 ordered chunks and all complete reconstructed exports. The worker locally rehashed all 244 execution files; this is not independent retrieval of all original execution files. Original reports saying pending remain historical.','review_limitation':'Parent connector could not independently retrieve the complete 30 MB canonical input inventory; verified manifest and matching 83032-binding preservation receipts are retained.','canonical_input_inventory':actual['canonical_inputs']},'clean_context_separation':'All historical roots in this index are evidence references only, prohibited as planned clean object/dependency inputs. No historical object or resolution ledger seeds the new model.','remaining':['Theorem34 replacement scaling','runtime-model qualification','authenticated clean dependencies/toolchain/extractor validation','reviewed production clean executor','exact coordinated CI','website completion','whole-paper acceptance']}
    index['full_audit']['ordered_export_reconstructions']=reconstructions
    index['full_audit']['ordered_chunks_reconciled']=chunk_count
    index['full_audit']['verification_attribution']={
        'worker':{'locally_rehashed_original_execution_files':244},
        'independent_review':{'manifest_entries_verified':244,'ordered_chunks_verified':216,'complete_exports_reconstructed':5,'full_30MB_canonical_inventory_retrieved':False},
        'qualification':'Independent manifest/export review is distinct from local rehashing of all original execution files; no provenance or clean-validation upgrade.'}
    (A/'chain-evidence-index.json').write_text(json.dumps(index,indent=2)+'\n')
    print(json.dumps({'ordinary_chains':485,'successful_stage_receipts':len(receipt_ids),'aggregate_compilations':1,'parts':len(shards),'full_audit_manifest_entries_verified':244,'no_compiler_invocations':True},indent=2))

if __name__=='__main__':build()
