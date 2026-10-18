"""Hash/preservation seal only. No mathematical experiment/compiler interface."""
from pathlib import Path
import datetime,fcntl,hashlib,json,os,shutil,subprocess

A=Path(__file__).resolve().parent;ROOT=A.parents[1]
BASE='c5f0837dba6578b5d6ef57e74c9c552b34a1bed3'
def bind(p):
    data=p.read_bytes()
    return {'repository_path':str(p.relative_to(ROOT)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

def main():
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()==BASE
    assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='light-eft-spanners-checkpoints'
    assert not subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT)
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT)
    previous=[];unique=set();context=[]
    for name,count in [('light-eft-theorem34-research-20261018',11),('light-eft-theorem34-stretch2-20261018',11),('light-eft-theorem34-incidence-20261018',12)]:
        folder=ROOT/'checkpoints'/name;p=folder/'manifest.json';m=json.loads(p.read_text())
        rows=m.get('files',[])+m.get('unchanged_context_bindings',m.get('unchanged_source_reading_bindings',[]))
        assert len(rows)==count
        for r in rows:assert bind(ROOT/r['repository_path'])==r;unique.add(r['repository_path'])
        previous.append({'manifest':bind(p),'verified_manifest_rows':len(rows)})
        context.extend([bind(folder/'REPORT.md'),bind(p)])
    context.append(bind(ROOT/'Light Edge Fault Tolerant Graph Spanners/CORRECTIONS.md'))
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
       'prior_review':'Parent independently accepted handwritten H-J and all12bindings; A-G reviews and original coverage labels preserved. Not Lean execution.',
       'prior_manifests_verified':previous,'prior_manifest_rows_checked':sum(p['verified_manifest_rows'] for p in previous),
       'unique_prior_bound_paths':len(unique),'all_preexisting_tracked_files_unchanged':True,
       'mathematical_status':'Self-contained handwritten conditional proof pending independent review; not machine-checked',
       'normalized_ratio':'min_H w(H)/(D_(2f)(G)*lambda(floor(n/sqrt(2f)),3))',
       'limsup_bound_for_each_fixed_f':'2*L_f*sqrt(2f)/(2f+1)',
       'strategy_exclusion':'L_f=o(sqrt(f)) excludes the stated uniform-backbone strategy, not the original existential theorem',
       'literal_special_cases':['projective incidence with L_f=4','all-cheap shared hubs with L_f=2'],
       'not_literal_special_cases':['mixed-weight spanning hub backbones','disconnected two-block cheap subgraph'],
       'new_candidate_experiments':0,'prior_experiment_or_synthetic_suite_reruns':0,
       'compiler_kernel_invocations':0,'retrieval_extraction_invocations':0,'CI_invocations':0,
       'accepted_source_edits':0,'runtime_preparation_changes':0,'website_changes':0,
       'fixed_stretch2_target':'OPEN','general_Theorem34':'OPEN; no theorem refutation or narrowed completion scope',
       'lock':{'path':'/tmp/distance-sparsification-single-compiler.lock','device':s.st_dev,'inode':s.st_ino,'free':True},
       'active_compilers_checkers_tracers':active,'disk_free_bytes':shutil.disk_usage(ROOT).free,
       'visible_memory_max_bytes':int(Path('/sys/fs/cgroup/memory.max').read_text()),'independent_review':'pending'}
    (A/'preservation.json').write_text(json.dumps(status,indent=2)+'\n')
    files=[bind(p) for p in sorted(A.rglob('*')) if p.is_file() and p!=A/'manifest.json']
    (A/'manifest.json').write_text(json.dumps({'scope':'Proof-only conditional strategy consolidation; no new experiments or Lean acceptance',
       'research_base_commit':BASE,'files':files,'unchanged_prior_context':context,
       'exclusion':'Only this manifest excludes itself; immutable Git commit binds every file.'},indent=2)+'\n')
    print(json.dumps({'research_files':len(files),'unchanged_context_bindings':len(context),'prior_manifest_rows_checked':34,
       'unique_prior_bound_paths':len(unique),'new_experiments':0,'compiler_invocations':0,'lock_free':True,'active_compilers':active},indent=2))

if __name__=='__main__':main()
