"""Final offline packet/scope checks; never invokes a compiler or executor."""
from pathlib import Path
import ast,datetime,fcntl,hashlib,json,os,re,shutil,subprocess

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='0769579d242f5c8bcd75f2f6333bb57b8d8fc97b'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def binding(p):
    data=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(data),'sha256':sha(data)}
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()

def main():
    assert git('branch','--show-current')=='light-eft-spanners-checkpoints'
    original=load(A/'preserved-draft-before-resume/manifest.json');assert len(original)==9
    for r in original:
        b=(A/'preserved-draft-before-resume'/r['path']).read_bytes()
        assert len(b)==r['bytes'] and sha(b)==r['sha256']
    assert (A/'tests-invocation-01.log').read_bytes()==(A/'preserved-draft-before-resume/tests-invocation-01.log').read_bytes()
    refs=load(A/'supervisor-bindings.json');supervisors=refs['ordinary']['files']+refs['audit']['files']+[refs['shared_lifecycle']]
    production=load(A/'unchanged-production-bindings.json')
    assert len(supervisors)==14 and len(production)==6
    for r in supervisors+production:assert binding(ROOT/r['repository_path'])['sha256']==r['sha256']
    assert load(ROOT/'scripts/LightEFTDependencyArtifact.json')['status']=='UNAVAILABLE_REVIEW_REQUIRED'
    plan=load(A/'PLAN.json');assert plan['production_enabled'] is False and plan['reviewed_artifact_authority'] is None
    assert plan['schedule_counts']=={'compile':486,'resolve':485,'replay':485,'audit':1,'total':1457}
    assert plan['versioncheck']['planned_count']==1 and plan['versioncheck']['separate_from_1457_stages'] is True
    assert not plan['historical_cache_inventories'] and not plan['cache_advice_scopes'] and not plan['retained_seeds']
    assert plan['ordinary_limits']['FSIZE']==16*1024**2 and plan['audit_limits']['FSIZE']==64*1024**2
    assert not list(Path('/workspace/.lake').glob('light-eft-clean-*'))
    def tests(p):
        tree=ast.parse(p.read_text())
        return {n.name+'.'+m.name for n in tree.body if isinstance(n,ast.ClassDef) for m in n.body if isinstance(m,ast.FunctionDef) and m.name.startswith('test_')}
    oldtests=tests(A/'preserved-draft-before-resume/test_contracts.py');newtests=tests(A/'test_contracts.py')
    assert len(oldtests)==40 and len(newtests)==46 and oldtests.issubset(newtests)
    log=(A/'tests-invocation-04.log').read_text()
    assert re.search(r'Ran 46 tests in [\d.]+s\n\nOK\s*$',log)
    assert len(re.findall(r'^test_.* \.\.\. ok$',log,re.M))==46
    source_allowed={str(A.relative_to(ROOT))+'/',
       'Light Edge Fault Tolerant Graph Spanners/README.md',
       'Light Edge Fault Tolerant Graph Spanners/PROOF_COVERAGE.md',
       'Light Edge Fault Tolerant Graph Spanners/verification/statement-map.json',
       'Light Edge Fault Tolerant Graph Spanners/verification/current-exact-source-evidence-20261018.json'}
    changed=subprocess.check_output(['git','diff','--name-only','-z',BASE],cwd=ROOT).decode().split('\0')
    changed=[p for p in changed if p]
    assert all(p.startswith(str(A.relative_to(ROOT))+'/') or p in source_allowed for p in changed)
    assert not any(p.endswith('.lean') for p in changed)
    layers=load(A/'current-layer-reconciliation.json')
    for b in layers['historical_originals']:assert sha((ROOT/b['repository_path']).read_bytes())==b['sha256']
    catalog=load(A/'chain-evidence-index.json')
    assert catalog['ordinary_chain_count']==485 and len(catalog['ordinary_modules'])==485
    assert set(catalog['aggregate_compile_only']['stages'])=={'compile'}
    for b in catalog['parts']:assert sha((ROOT/b['repository_path']).read_bytes())==b['sha256']
    lock=Path('/tmp/distance-sparsification-single-compiler.lock')
    with lock.open() as f:
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(f.fileno())
        assert (st.st_dev,st.st_ino)==(33,3849)
        fcntl.flock(f,fcntl.LOCK_UN)
    active=[]
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():continue
        try:
            comm=(p/'comm').read_text().strip();state=(p/'stat').read_text().split(') ',1)[1].split()[0]
            if comm in {'lean','leanchecker','lake','leantar','strace'} and state!='Z':active.append({'pid':int(p.name),'comm':comm})
        except (OSError,IndexError):pass
    assert not active
    report={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'branch':git('branch','--show-current'),'base_commit':BASE,'head_before_publication':git('rev-parse','HEAD'),'scope':'disabled static/synthetic preparation plus offline historical evidence reconciliation','original_draft_files_preserved':9,'original_test_log_preserved':True,'original_tests':40,'final_tests':46,'original_final_reconciliation_tests':7,'all_defined_tests_passed':True,'unchanged_supervisor_bindings':14,'unchanged_production_bindings':6,'source_graph_nodes':486,'verified_project_import_edges':1107,'planned_stages':1457,'planned_versionchecks_separate':1,'fresh_compiler_checker_versioncheck_invocations':0,'retrieval_extraction_advice_invocations':0,'clean_validation_performed':False,'production_enabled':False,'mathematical_source_edits':0,'website_edits':0,'CI_invocations':0,'changed_tracked_paths':changed,'lock':{'path':str(lock),'device':st.st_dev,'inode':st.st_ino,'free':True},'active_compilers_checkers_tracers':active,'disk_free_bytes':shutil.disk_usage(ROOT).free,'host_mem_available_kib':int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text())[1]),'visible_memory_max_bytes':int(Path('/sys/fs/cgroup/memory.max').read_text()),'accounting_qualification':'PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN; no full-ancestor gate added','independent_review':'pending'}
    (A/'packet-validation.json').write_text(json.dumps(report,indent=2)+'\n')
    implementations=[binding(p) for p in sorted(A.glob('*.py'))]
    (A/'implementation-bindings.json').write_text(json.dumps({'preparation_sources':implementations,'unchanged_supervisor_references':supervisors,'unchanged_production_references':production},indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
