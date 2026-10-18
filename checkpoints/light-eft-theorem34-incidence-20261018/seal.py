"""Seal the bounded incidence investigation; never invokes compiler/retrieval."""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,shutil,subprocess

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
OLD=ROOT/'checkpoints/light-eft-theorem34-stretch2-20261018'
BASE='ea8e75d23ee891664949f185cd9081bec90b7f85'
def sha(b):return hashlib.sha256(b).hexdigest()
def bind(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}

def main():
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()==BASE
    assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='light-eft-spanners-checkpoints'
    assert not subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT)
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT)
    old=json.loads((OLD/'manifest.json').read_text());rows=old['files']+old['unchanged_context_bindings'];assert len(rows)==11
    for row in rows:assert bind(ROOT/row['repository_path'])==row
    results=json.loads((A/'experiment-results.json').read_text())
    assert results['pre_experiment_precheck_sha256']==sha((A/'PRECHECK.md').read_bytes())
    expected={'geometries':4,'weighted_cases':15,'point_pair_path_families':2160,'exhaustive_cut_tests':16382,
       'full_graph_forcing_witnesses':588,'targeted_nonforcing_fault_checks':882,'all_pairs_fault_sets':102}
    assert results['summary']==expected
    source_refs=[bind(OLD/'REPORT.md'),bind(OLD/'manifest.json'),
       bind(ROOT/'checkpoints/light-eft-theorem34-research-20261018/REPORT.md'),
       bind(ROOT/'Light Edge Fault Tolerant Graph Spanners/CORRECTIONS.md')]
    with open('/tmp/distance-sparsification-single-compiler.lock') as f:
        fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);s=os.fstat(f.fileno())
        assert (s.st_dev,s.st_ino)==(33,3849)
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
       'prior_review':'Parent reports independent acceptance of handwritten Lemmas E-G and all three regimes/uniform obstruction; not Lean execution',
       'previous_accepted_bindings_verified':11,'prior_sampled_and_exhaustive_labels_unchanged':True,
       'all_preexisting_tracked_files_unchanged':True,'precheck_before_experiments_sha256':results['pre_experiment_precheck_sha256'],
       'unchanged_context_bindings':source_refs,'handwritten_results_pending_review':['actual incidence/residual-forest q-fault certificate and full cost','full-graph one-fault forcing at a>1/2','small-weight robust four-hop alternative and family-scaling obstruction'],
       'finite_experiment_scope':'Exact scopes and helper counts in report/results; only p2 exhaustive cuts and low-weight allpairs through one fault',
       'fixed_stretch2_target':'OPEN','general_Theorem34':'OPEN; no theorem counterexample or narrowed completion scope',
       'compiler_kernel_invocations':0,'denied_retrieval_extraction_advice_invocations':0,'CI_invocations':0,
       'accepted_source_edits':0,'runtime_preparation_changes':0,'website_changes':0,
       'lock':{'path':'/tmp/distance-sparsification-single-compiler.lock','device':s.st_dev,'inode':s.st_ino,'free':True},
       'active_compilers_checkers_tracers':active,'disk_free_bytes':shutil.disk_usage(ROOT).free,
       'visible_memory_max_bytes':int(Path('/sys/fs/cgroup/memory.max').read_text()),'independent_review':'pending'}
    (A/'preservation.json').write_text(json.dumps(status,indent=2)+'\n')
    files=[bind(p) for p in sorted(A.rglob('*')) if p.is_file() and p!=A/'manifest.json']
    manifest={'scope':'Incidence mathematical research and finite evidence only; no Lean acceptance','research_base_commit':BASE,
       'files':files,'unchanged_context_bindings':source_refs,'exclusion':'Only this manifest excludes itself; immutable Git commit binds all files.'}
    (A/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'research_files':len(files),'unchanged_context_bindings':len(source_refs),'previous_bindings_verified':11,
       'precheck_hash_verified':True,'compiler_invocations':0,'fixed_stretch2_repair':'OPEN','lock_free':True,'active_compilers':active},indent=2))

if __name__=='__main__':main()
