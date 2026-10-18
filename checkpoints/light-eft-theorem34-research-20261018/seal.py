"""Seal research notes and finite experiments; never invokes a compiler."""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,shutil,subprocess

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='fd40832d552e4e9cedb5a5ad604180a73f1e65cb'
def sha(b):return hashlib.sha256(b).hexdigest()
def bind(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}

def main():
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    assert head==BASE
    assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='light-eft-spanners-checkpoints'
    assert not subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT)
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT)
    result=json.loads((A/'experiment-results.json').read_text())
    cases=result['two_block_cases']
    assert sum(c['all_input_fault_sets_connectivity_checked'] for c in cases)==15633
    assert sum(c['all_input_fault_sets_distance_checked'] for c in cases)==75
    assert sum(c['missing_heavy_edges_tested'] for c in cases)==41
    assert len(result['weighted_blowup_quantile_cases'])==176
    source_paths=['Light Edge Fault Tolerant Graph Spanners/CORRECTIONS.md',
       'Light Edge Fault Tolerant Graph Spanners/verification/FOURTH_SOURCE_AND_COMPONENT_AUDIT.md',
       'Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/LargeCloudCertificate.lean',
       'Light Edge Fault Tolerant Graph Spanners/verification/current-exact-source-evidence-20261018.json']
    bound=[bind(ROOT/p) for p in source_paths]
    with open('/tmp/distance-sparsification-single-compiler.lock') as f:
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);st=os.fstat(f.fileno())
        assert (st.st_dev,st.st_ino)==(33,3849)
        fcntl.flock(f,fcntl.LOCK_UN)
    active=[]
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():continue
        try:
            name=(p/'comm').read_text().strip();state=(p/'stat').read_text().split(') ',1)[1].split()[0]
            if name in {'lean','leanchecker','lake','leantar','strace'} and state!='Z':active.append({'pid':int(p.name),'name':name})
        except (OSError,IndexError):pass
    assert not active
    status={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'research_base_commit':BASE,
      'accepted_mathematical_source':'78cb40c7837db049d645d73696f2e0b724ce8a3b',
      'source_reading':{'original':'https://arxiv.org/html/2502.10890v2','sections':['Theorem34 and proof','Definitions5,7,8,15'],
         'representation':'Public primary-source HTML inspected; no fresh PDF-byte authentication is claimed. Previously reviewed PDF hashes remain in the unchanged local source audit.'},
      'unchanged_source_and_scope_bindings':bound,'all_preexisting_tracked_files_unchanged':True,
      'lean_source_edits':0,'compiler_kernel_invocations':0,'cache_retrieval_extraction_advice_invocations':0,'CI_invocations':0,
      'disabled_preparation_untouched':True,'previous_proof_audit_evidence_untouched':True,
      'math_status':{'partial_k_1_construction':'handwritten proof pending review','general_k_repair':'OPEN',
        'old_family_any_certificate_obstruction':'handwritten proof pending review; not a theorem-level counterexample',
        'finite_experiments':'all exact-rational assertions passed; not a formal proof or acceptance'},
      'lock':{'path':'/tmp/distance-sparsification-single-compiler.lock','device':st.st_dev,'inode':st.st_ino,'free':True},
      'active_compilers_checkers_tracers':active,'disk_free_bytes':shutil.disk_usage(ROOT).free,
      'visible_memory_max_bytes':int(Path('/sys/fs/cgroup/memory.max').read_text()),'independent_review':'pending'}
    (A/'preservation.json').write_text(json.dumps(status,indent=2)+'\n')
    rows=[bind(p) for p in sorted(A.rglob('*')) if p.is_file() and p!=A/'manifest.json']
    (A/'manifest.json').write_text(json.dumps({'scope':'Research notes and finite experiments only; no Lean source changes','research_base_commit':BASE,'files':rows,'unchanged_source_reading_bindings':bound,'exclusion':'Only this manifest excludes itself; immutable Git commit binds every file.'},indent=2)+'\n')
    print(json.dumps({'research_files':len(rows),'unchanged_source_reading_bindings':len(bound),'compiler_invocations':0,'general_theorem_repair':'OPEN','lock_free':True,'active_compilers':active},indent=2))

if __name__=='__main__':main()
