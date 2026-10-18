"""Bind one mathematical investigation; no compiler or retrieval interface."""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,shutil,subprocess

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
OLD=ROOT/'checkpoints/light-eft-theorem34-research-20261018'
BASE='682c8809fbf4a92b2f86be08916b0d81b0b1bd2e'
def sha(b):return hashlib.sha256(b).hexdigest()
def bind(p):
    b=p.read_bytes();return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':sha(b)}

def main():
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()==BASE
    assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='light-eft-spanners-checkpoints'
    assert not subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT)
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT)
    old=json.loads((OLD/'manifest.json').read_text());refs=old['files']+old['unchanged_source_reading_bindings']
    assert len(refs)==11
    for r in refs:assert bind(ROOT/r['repository_path'])==r
    results=json.loads((A/'experiment-results.json').read_text())
    assert len(results['cases'])==20 and results['all_cut_types_checked']==110
    assert results['forcing_witnesses_checked']==176 and results['all_pairs_fault_sets_checked']==1278
    sources=[bind(OLD/'REPORT.md'),bind(OLD/'manifest.json'),
        bind(ROOT/'Light Edge Fault Tolerant Graph Spanners/CORRECTIONS.md'),
        bind(ROOT/'Light Edge Fault Tolerant Graph Spanners/verification/current-exact-source-evidence-20261018.json')]
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
      'prior_review':'Parent reports independent acceptance of handwritten Lemmas A-D and all11bindings; not Lean execution',
      'previous_bindings_verified':11,'all_preexisting_tracked_files_unchanged':True,
      'source_context':'https://arxiv.org/html/2502.10890v2#S3.SS1; fixed Theorem17 parameters only; no new PDF-byte authentication claimed',
      'unchanged_context_bindings':sources,'handwritten_results':['bounded-aspect-ratio screen','actual cut/cost bounds for new shared-hub family','three-regime stretch2 candidate obstruction'],
      'finite_experiments':'passed; f1 faults exhaustive through size1, f2 includes sampled size2 faults and is not exhaustive',
      'fixed_stretch2_target':'OPEN','general_Theorem34':'OPEN; no theorem counterexample or narrower completion scope',
      'compiler_kernel_invocations':0,'cache_retrieval_extraction_advice_invocations':0,'CI_invocations':0,
      'proof_source_edits':0,'runtime_or_disabled_preparation_changes':0,'website_changes':0,
      'lock':{'path':'/tmp/distance-sparsification-single-compiler.lock','device':s.st_dev,'inode':s.st_ino,'free':True},
      'active_compilers_checkers_tracers':active,'disk_free_bytes':shutil.disk_usage(ROOT).free,
      'visible_memory_max_bytes':int(Path('/sys/fs/cgroup/memory.max').read_text()),'independent_review':'pending'}
    (A/'preservation.json').write_text(json.dumps(status,indent=2)+'\n')
    entries=[bind(p) for p in sorted(A.rglob('*')) if p.is_file() and p!=A/'manifest.json']
    manifest={'scope':'Handwritten stretch2 research and finite experiments; not Lean acceptance','research_base_commit':BASE,
       'files':entries,'unchanged_context_bindings':sources,
       'exclusion':'Only this manifest excludes itself; immutable Git commit binds every file.'}
    (A/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'research_files':len(entries),'unchanged_context_bindings':len(sources),'previous_bindings_verified':11,
        'compiler_invocations':0,'fixed_stretch2_repair':'OPEN','lock_free':True,'active_compilers':active},indent=2))

if __name__=='__main__':main()
